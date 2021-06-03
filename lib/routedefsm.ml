open! Base
open Printf
open Gtype
open Names
open Graph
open Err

type refinement_action_annot =
  { rec_expr_updates: (string * Expr.t) list
  ; tv_resets: TypeVariableName.t list}
[@@deriving ord, sexp_of]

let encase = sprintf "\"%s\""

let rec refinement_str = function
  | Expr.Var v -> encase @@ VariableName.user v
  | Expr.Int i -> encase @@ Int.to_string i
  | Expr.Bool b -> encase @@ Bool.to_string b
  | Expr.String s -> encase @@ "'" ^ s ^ "'"
  | Expr.Binop (b, e1, e2) ->
      sprintf 
      {|{"binop": "%s",
"e1": %s,
"e2": %s}|} 
      (Syntax.show_binop b) (refinement_str e1) (refinement_str e2)
  | Expr.Unop (u, e) -> sprintf 
      {|{"unop": "%s",
"e": %s}|}
      (Syntax.show_unop u) (refinement_str e)

let rec show_payload_type =
  let no_refinement = {|""|} in
  function
  | Expr.PTAbstract n -> (PayloadTypeName.user n, "")
  | Expr.PTRefined (_, ty', e) -> (fst @@ show_payload_type ty', refinement_str e)
  | Expr.PTInt -> ("number", no_refinement)
  | Expr.PTBool -> ("boolean", no_refinement)
  | Expr.PTString -> ("string", no_refinement)
  | Expr.PTUnit -> ("null", no_refinement)

let rec_expr_updates_str {rec_expr_updates; tv_resets} =
  let rec_expr_updates =
    String.concat ~sep:"," (List.map ~f:(fun (n, r) -> 
      encase n ^ ": " ^ refinement_str r) rec_expr_updates)
  in
  let tv_resets = 
    String.concat ~sep:"," (List.map ~f:(fun tv -> 
      encase @@ TypeVariableName.user tv) tv_resets) in
  rec_expr_updates, tv_resets

let name_sort_refinement pl pl_num = 
  (match pl with 
    | PValue (n, ty) ->
      let sort, refinement = show_payload_type ty in
      let sort = encase sort in
      let refinement = if String.equal refinement "" then encase refinement else refinement in
      let name =  (match n with 
        | Some n' -> encase @@ VariableName.user n' (* todo: error if name starting with payload_, to guarantee pl names distinct *)
        | None -> encase @@ "payload_" ^ Int.to_string pl_num)
      in
      (name, sort, refinement)
    | PDelegate _ -> Err.unimpl "delegation for routed FSM generation")

let payloads_str pl_num pl =
  let name, sort, refinement = name_sort_refinement pl pl_num
  in
  (pl_num + 1, sprintf 
    {|{
"name": %s,
"sort": %s,
"refinement": %s
}|} 
    name sort refinement)

type action_ref =
  | RefA of string
  | EpsilonRef
[@@deriving ord, sexp_of]

let show_action_ref = function
  | RefA id -> "l" ^ id
  | EpsilonRef -> "ε"

type action =
  | SendA of RoleName.t * Gtype.message * refinement_action_annot
  | RecvA of RoleName.t * Gtype.message * refinement_action_annot
  | Epsilon

let show_action =
  function
  | Epsilon -> "ε"
  | (SendA (r, msg, annot_as) | RecvA (r, msg, annot_as)) as a ->
    let action =
      match a with SendA _ -> "!" | RecvA _ -> "?" | _ -> assert false
    in
    let rec_expr_updates, tv_resets = rec_expr_updates_str annot_as in
    sprintf 
      {|{
"op": %s,
"role": %s,
"label": %s,
"payloads": [%s],
"rec_expr_updates": {%s},
"tv_resets": [%s]
}|} 
      (encase action)
      (encase @@ RoleName.user r)
      (encase @@ LabelName.user msg.label)
      (String.concat ~sep:",\n" (List.folding_map ~init:1 ~f:payloads_str msg.payload))
      (rec_expr_updates)
      (tv_resets)

module Label = struct
  module M = struct
    type t = action_ref

    let compare = compare_action_ref

    let sexp_of_t = sexp_of_action_ref
  end

  include M
  include Comparator.Make (M)

  let default = EpsilonRef
end

module G = Persistent.Digraph.ConcreteLabeled (Int) (Label)

type t = G.t

type state = int

module Display = struct
  include G

  let vertex_name = Int.to_string

  let graph_attributes _ = []

  let default_vertex_attributes _ = []

  let vertex_attributes _ = []

  let default_edge_attributes _ = []

  let edge_attributes (_, a, _) = [`Label (show_action_ref a)]

  let get_subgraph _ = None
end

module DotOutput = Graphviz.Dot (Display)

let show g =
  let buffer = Buffer.create 4196 in
  let formatter = Caml.Format.formatter_of_buffer buffer in
  DotOutput.fprint_graph formatter g ;
  Caml.Format.pp_print_flush formatter () ;
  Buffer.contents buffer

type efsm_conv_env =
  { g: G.t
  ; tyvars: (TypeVariableName.t * (int * (TypeVariableName.t list))) list
  ; states_to_merge: (int * int) list
  ; active_roles: (RoleName.t, RoleName.comparator_witness) Set.t
  ; role_activations: (RoleName.t * RoleName.t * (message * int)) list 
  ; tv_to_rec_var: (bool * Gtype.rec_var) list Map.M(TypeVariableName).t }
let init_efsm_conv_env:efsm_conv_env = 
  { g= G.empty
  ; tyvars= []
  ; states_to_merge= []
  ; active_roles= Set.empty (module RoleName)
  ; role_activations= [] 
  ; tv_to_rec_var= Map.empty (module TypeVariableName) }

let merge_state ~from_state ~to_state g =
  (* check for vertex ε-transitioning to itself: V --ε--> V. and just delete if present *)
  if from_state = to_state then 
    let g = G.remove_edge g from_state to_state in 
    g
  else
    let subst x = if x = from_state then to_state else x in
    let g =
      G.fold_succ_e
        (fun (ori, label, dest) g ->
          let ori = subst ori in
          let dest = subst dest in
          match label with
          | EpsilonRef -> g 
          | label -> G.add_edge_e g (ori, label, dest))
        g from_state g
    in
    let g =
      G.fold_pred_e
        (fun (ori, label, dest) g ->
          let ori = subst ori in
          let dest = subst dest in
          match label with
          | EpsilonRef -> g 
          | label -> G.add_edge_e g (ori, label, dest))
        g from_state g
    in
    let g = G.remove_vertex g from_state in
    g

(* checks if there is a 'continue Loop [recExprUpdate]' next *)
(* and applys an annotation to the current message for it *)
let make_refinement_annotation role env next_l =
  if Config.refinement_type_enabled () then
    let tv_resets = ref [] in
    let rec aux = (function
    | ChoiceG (selector, ls) ->
      let branch_updates = List.map ~f:snd @@ List.concat @@ List.map ~f:aux ls in
      let dedupped_branch_updates = List.dedup_and_sort ~compare:Expr.compare branch_updates in
      if List.length dedupped_branch_updates > 1 then
        uerr @@ RecExpressionUpdatesNonUniform selector
      ; aux @@ List.hd_exn ls
    | TVarG (tv, rec_exprs, _) ->
      let curr_tvs = Set.of_list (module TypeVariableName) @@ List.map ~f:fst env.tyvars in
      let (_, prev_tvs) = List.Assoc.find_exn ~equal:TypeVariableName.equal env.tyvars tv in
      let prev_tvs = Set.of_list (module TypeVariableName) prev_tvs in
      tv_resets := Set.to_list @@ Set.diff curr_tvs prev_tvs
      ; let rec_expr_filter = Map.find_exn env.tv_to_rec_var tv in
      let rec_exprs =
        List.map2_exn
          ~f:(fun (x, _) y -> if not x then Some y else None)
          rec_expr_filter rec_exprs
      in
      let rec_expr_name = if not @@ List.is_empty rec_expr_filter then
          VariableName.user (snd @@ List.hd_exn rec_expr_filter).rv_name 
        else
          ""
      in
      let rec_exprs = List.filter_opt rec_exprs in
      List.map ~f:(fun r -> (rec_expr_name, r)) rec_exprs 
    | MessageG (_, s, r, l') ->
      if RoleName.equal role s || RoleName.equal role r then
        []
      else
        aux l'
    | _ ->
      [])
    in
    let rec_expr_updates = aux next_l in
    (env, {rec_expr_updates; tv_resets= !tv_resets})
  else (env, {rec_expr_updates= []; tv_resets= []})

let first_msg_is_distinct_and_from_chooser chooser ar ras =
  let label_equals (pl1, lab1) (pl2, lab2) = (* should this check payloads too?? *)
    List.length pl1 = List.length pl2 &&
      List.for_all2_exn pl1 pl2 ~f:Gtype.equal_payload &&
      LabelName.equal lab1 lab2
  in
  let msgs_so_far = ref [] in
  RoleName.equal ar chooser || (* chooser doesn't need to receive from chooser *)
  List.for_all ras ~f:(fun se ->
    match List.find se ~f:(fun (s, r, _) -> RoleName.equal r ar || RoleName.equal s ar) with
      | Some (s, _, (m, _)) -> 
        let (pl, lab) = (m.payload, m.label) in
        let is_distinct_msg = not @@ List.mem !msgs_so_far (pl, lab) ~equal:label_equals in
        msgs_so_far := (pl, lab) :: !msgs_so_far
        ; RoleName.equal s chooser && is_distinct_msg
      | None -> false)

(* ordered flattening *)
(* e.g. [[1,2,3,4],[a,b,c]] --> [1,a,2,b,3,c,4] *)
(* to make nested choices not cause outermost choice's branch check to fail *)
let get_ordered_role_activations = 
  let rec get_ordered_role_activations' result ras =
    if List.for_all ~f:List.is_empty ras then
      !result
    else
      let leftover_cras = List.map ~f:(fun ra ->
        result := !result @ (List.take ra 1)
        ; List.drop ra 1) ras
      in
      get_ordered_role_activations' result leftover_cras
  in
  get_ordered_role_activations' (ref [])

let construct_json optional_active_roles mandatory_active_roles rec_expr_inits edges g_for_edge_to_source_state_json =
  let optional_active_roles_list = Set.to_list optional_active_roles in
  let mandatory_active_roles_list = Set.to_list mandatory_active_roles in
  let create_role_json role_type role_list = sprintf {|"%s": [%s]|} 
    role_type
    (String.concat ~sep:{|,|} (List.map ~f:(fun r -> encase @@ RoleName.user r) role_list))
  in
  let optional_json = create_role_json "optional" optional_active_roles_list in
  let mandatory_json = create_role_json "mandatory" mandatory_active_roles_list in
  let rec_expr_init_json = 
    "\"rec_exprs\": {\n" ^ 
      String.concat ~sep:"," 
        (List.map rec_expr_inits
          ~f:(fun (n, tv, init, ty) ->
            let sort, refinement = show_payload_type ty in
            let sort = encase sort in
            let refinement = if String.equal refinement "" then encase refinement else refinement in
            let init = refinement_str init in
            sprintf {|"%s": {"typevar": "%s", "sort": %s, "refinement": %s, "init": %s}|} 
              (VariableName.user n) (TypeVariableName.user tv) sort refinement init))
    ^ "\n}"
  in
  let edge_json = 
    "\"edges\": {\n" ^
      String.concat ~sep:",\n"
        (List.map edges
          ~f:(fun (ref_a_str, a_str) ->
            sprintf "\"%s\": %s" (ref_a_str) (a_str)))
    ^ "\n}"
  in
  let edge_to_source_state_json = 
    G.fold_edges_e
      (fun (from, label, _) s -> 
        s ^ sprintf {|"%s": "S%s",|} (show_action_ref label) (Int.to_string from))
      g_for_edge_to_source_state_json "{"
  in
  let edge_to_source_state_json = String.drop_suffix edge_to_source_state_json 1 ^ "}" in (* drop trailing comma *)
  let edge_to_source_state_json = sprintf {|"froms": %s|} edge_to_source_state_json in
  let final_json = 
    sprintf "\n\n{\n%s,\n%s,\n%s,\n%s, \n%s\n}" 
    mandatory_json optional_json edge_to_source_state_json rec_expr_init_json edge_json 
  in
  final_json

let of_global_type gty ~role ~server =
  let count = ref 0 in
  let fresh () =
    let n = !count in
    count := n + 1 ;
    n
  in
  let seen_choice = ref false in
  let mandatory_active_roles = ref (Set.add (Set.empty (module RoleName)) server) in
  let optional_active_roles = ref (Set.empty (module RoleName)) in
  let edges = ref [] in
  let rec_expr_inits = ref [] in
  let terminal = ref ~-1 in
  let rec conv_gtype_aux env =
    let {g; tyvars; active_roles; role_activations; _} = env in
    let terminate () =
      if !terminal = ~-1 then
        let curr = fresh () in
        terminal := curr ;
        let g = G.add_vertex g curr in
        ({env with g}, curr)
      else
        (env, !terminal)
    in
    function
    | EndG ->
      terminate ()
    | MessageG (m, send_n, recv_n, l) -> (
      if not @@ !seen_choice then (
        mandatory_active_roles := Set.add !mandatory_active_roles send_n
        ; mandatory_active_roles := Set.add !mandatory_active_roles recv_n
      )
      ; let active_roles = Set.add active_roles recv_n in
      let active_roles = Set.add active_roles send_n in
      match role with
      | _ when RoleName.equal role send_n || RoleName.equal role recv_n ->
        let curr = fresh () in
        let role_activations = role_activations @ [(send_n, recv_n, (m, curr))] in 
        let env, rannot = make_refinement_annotation role env l in
        let env, next = conv_gtype_aux {env with active_roles; role_activations} l in
        let a = if RoleName.equal role send_n then
            SendA (recv_n, m, rannot)
          else (* if role equals recv_n *)
            RecvA (send_n, m, rannot)
        in
        let ref_a = RefA (Int.to_string curr ^ Int.to_string next) in
        edges := (show_action_ref ref_a, show_action a) :: !edges
        ; let e = (curr, ref_a, next) in
        let g = env.g in
        let g = G.add_vertex g curr in
        let g = G.add_edge_e g e in
        ({env with g}, curr)
      | _ ->
        let role_activations = role_activations @ [(send_n, recv_n, (m, !count))] in
        conv_gtype_aux {env with active_roles; role_activations} l
    )
    | MuG (tv, rec_vars, l) ->
      let rec_vars =
        List.map
          ~f:(fun ({rv_roles; _} as rec_var) ->
            ( not @@ List.mem ~equal:RoleName.equal rv_roles role
            , rec_var ) )
          rec_vars
      in
      let new_st = fresh () in
      let g = G.add_vertex g new_st in
      let env =
        { env with
          tyvars= (tv, (new_st, tv :: List.map tyvars ~f:(fun (tv', _) -> tv'))) :: tyvars
        ; g
        ; tv_to_rec_var = Map.add_exn env.tv_to_rec_var ~key:tv ~data:rec_vars
        }
      in
      if not @@ List.is_empty rec_vars then
        (let rec_var = snd @@ List.hd_exn rec_vars in
        let name = rec_var.rv_name in
        let init = rec_var.rv_init_expr in
        let ty = rec_var.rv_ty in
        rec_expr_inits := (name, tv, init, ty) :: !rec_expr_inits)
      ; let env, curr = conv_gtype_aux env l in
      let g = env.g in
      let g = G.add_edge_e g (new_st, EpsilonRef, curr) in
      let states_to_merge = (new_st, curr) :: env.states_to_merge in
      ({env with g; states_to_merge}, curr)
    | TVarG (tv, _, _) ->
      let (st, _) = List.Assoc.find_exn ~equal:TypeVariableName.equal env.tyvars tv in
        (env, st)
    | ChoiceG (chooser, ls) ->
      let active_roles = Set.add active_roles chooser in
      if Int.equal !count 1 then (* if no msgs before first choice *)
        mandatory_active_roles := Set.add !mandatory_active_roles chooser
      ; seen_choice := true
      
      ; if 1 < List.count ~f:(fun l -> match l with MuG _ -> true | _ -> false) ls then
        (Err.unimpl "Multiple recursions with variables in choices")

      ; let curr = fresh () in

      (* work out what active roles get used in each branch *)
      let choice_active_rs = ref [] in
      let choice_r_activations:((RoleName.t * RoleName.t * (message * state)) list list ref) = ref [] in
      let env, nexts = List.fold_map ~f:(
        fun e l ->
          let acc_env, acc_n = conv_gtype_aux e l in
          choice_active_rs := !choice_active_rs @ [acc_env.active_roles]
          ; choice_r_activations := !choice_r_activations @ [acc_env.role_activations] 
          ; {acc_env with active_roles; role_activations= []}, acc_n
        ) ~init:{env with role_activations= []} ls
      in

      (* check over previous active roles *)
      Set.iter active_roles 
        ~f:(fun ar -> 
          if not @@ first_msg_is_distinct_and_from_chooser chooser ar !choice_r_activations then
              uerr (BranchErrorPrevious (chooser, ar))
          )
                                                 
      ; let new_r_sets = List.map ~f:(fun l_rs -> Set.diff l_rs active_roles) !choice_active_rs in
      optional_active_roles := Set.union !optional_active_roles (Set.union_list (module RoleName) new_r_sets)
      (* check over newly active roles *)
      ; List.iter new_r_sets ~f:(fun new_rs ->
        Set.iter new_rs ~f:(fun new_r -> 
          (*(Caml.Format.print_string (RoleName.user new_r) );*)
          let contains_new_r = List.exists ~f:(fun (s, r, _) -> RoleName.equal r new_r || RoleName.equal s new_r) in
          let filtered_branches = List.filter ~f:contains_new_r !choice_r_activations in
          (*(Caml.Format.print_string 
            ("\n" ^ String.concat ~sep:"\n" 
              (List.map filtered_branches
                ~f:(fun cra -> String.concat ~sep:"," (List.map ~f:(fun (s, r, _) -> RoleName.user s ^ "--" ^ RoleName.user r) cra))) ^ "\n")) ;*)
          if not @@ first_msg_is_distinct_and_from_chooser chooser new_r filtered_branches then
            uerr (BranchErrorNew (chooser, [new_r]))
        )
      )
      
      ; let g = env.g in

      (* don't do epsilon transition if next state is terminal *)
      (* this is for when a role is used (and becomes active) in one branch but not in another *)
      let non_terminal_nexts = List.filter ~f:(fun next -> next <> !terminal) nexts in
      let non_terminal_nexts = List.dedup_and_sort ~compare:Int.compare non_terminal_nexts in
      let es = List.map ~f:(fun n -> (curr, EpsilonRef, n)) non_terminal_nexts in

      let g = G.add_vertex g curr in
      let g = List.fold ~f:G.add_edge_e ~init:g es in
      let states_to_merge =
          List.map ~f:(fun next -> (curr, next)) non_terminal_nexts @ env.states_to_merge
      in
      let role_activations = role_activations @ (get_ordered_role_activations !choice_r_activations) in
      ({env with g; states_to_merge; active_roles; role_activations}, curr)
    | CallG (_, _, _, l) ->
      conv_gtype_aux env l
  in
  let init_env = init_efsm_conv_env in
  (* server is active by default *)
  let init_active_roles = Set.add init_env.active_roles server in
  let env, start = conv_gtype_aux {init_env with active_roles=init_active_roles} gty in
  let g = env.g in
  let (start, g) = 
    if not @@ List.is_empty env.states_to_merge then
      (let rec aux (start, g) = function
        | [] -> (start, g)
        | (s1, s2) :: rest ->
            let to_state = Int.min s1 s2 in
            let from_state = Int.max s1 s2 in
            let subst x = if x = from_state then to_state else x in
            let g = merge_state ~from_state ~to_state g in
            let start = subst start in
            let rest =
              List.map
                ~f:(fun (x, y) ->
                  let x = subst x in
                  let y = subst y in
                  (x, y))
                rest
            in
            aux (start, g) rest
      in
      aux (start, g) env.states_to_merge)
    else 
      (start, g)
  in
  let json = 
    construct_json !optional_active_roles !mandatory_active_roles !rec_expr_inits !edges g
  in
  ((start, g), json)
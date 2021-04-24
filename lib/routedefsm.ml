open! Base
open Printf
open Gtype
open Names
open Graph
open Err

type refinement_action_annot =
  { silent_vars: (VariableName.t * Expr.payload_type) list
  ; rec_expr_updates: Expr.t list }
[@@deriving ord, sexp_of]

let encase = sprintf "\"%s\""

let rec show_payload_type =
  function
  | Expr.PTAbstract n -> (PayloadTypeName.user n, "")
  | Expr.PTRefined (_, ty', e) -> (fst @@ show_payload_type ty', String.escaped @@ Expr.show e)
  | Expr.PTInt -> ("number", "")
  | Expr.PTBool -> ("boolean", "")
  | Expr.PTString -> ("string", "")
  | Expr.PTUnit -> ("null", "")

let silent_vars_and_rec_expr_updates_str {silent_vars; rec_expr_updates} =
  let silent_vars =
    String.concat ~sep:",\n"
      (List.map
          ~f:(fun (v, t) ->
            sprintf "\"%s\": \"%s\"" (VariableName.user v) (fst @@ show_payload_type t) )
          silent_vars)
  in
  let rec_expr_updates =
    String.concat ~sep:", " (List.map ~f:Expr.show rec_expr_updates)
  in
  silent_vars, rec_expr_updates

let payloads_str pl = 
  let name, sort, refinement = (match pl with 
    | PValue (n, ty) ->
      let sort, refinement = show_payload_type ty in
      let sort, refinement = encase sort, encase refinement in
      let name =  (match n with 
        | Some n' -> encase @@ VariableName.user n'
        | None -> encase "")
      in 
      (name, sort, refinement)
    | PDelegate _ -> Err.unimpl "delegation for routed fsm gen")
  in
  sprintf 
    {|{
"name": %s,
"sort": %s,
"refinement": %s
}|} 
    name sort refinement 

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
      match a with SendA _ -> "send" | RecvA _ -> "recv" | _ -> assert false
    in
    let svars, rec_expr_updates = silent_vars_and_rec_expr_updates_str annot_as in
    sprintf 
      {|{
"action": %s,
"target": %s,
"label": %s,
"payloads": [%s],
"silents": {%s},
"rec_exprs": [%s]
}|} 
      (encase action) 
      (encase @@ RoleName.user r)
      (encase @@ LabelName.user msg.label)
      (String.concat ~sep:",\n" (List.map ~f:payloads_str msg.payload))
      (svars)
      (if String.equal rec_expr_updates "" then "" else encase rec_expr_updates)

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
  ; tyvars: (TypeVariableName.t * int) list
  ; states_to_merge: (int * int) list
  ; active_roles: (RoleName.t, RoleName.comparator_witness) Set.t
  ; role_activations: (RoleName.t * RoleName.t * (message * int)) list 
  ; state_to_rec_var: (bool * Gtype.rec_var) list Map.M(Int).t
  ; tv_to_rec_var: (bool * Gtype.rec_var) list Map.M(TypeVariableName).t
  ; silent_var_buffer: (VariableName.t * Expr.payload_type) list 
  ; svars: (VariableName.t, VariableName.comparator_witness) Set.t }
let init_efsm_conv_env:efsm_conv_env = 
  { g= G.empty
  ; tyvars= []
  ; states_to_merge= []
  ; active_roles= Set.empty (module RoleName)
  ; role_activations= [] 
  ; state_to_rec_var= Map.empty (module Int)
  ; tv_to_rec_var= Map.empty (module TypeVariableName)
  ; silent_var_buffer= []
  ; svars= Set.empty (module VariableName) }

let merge_state ~from_state ~to_state g =
  (* check for vertex ε-transitioning to itself: V --ε--> V *)
  (* just delete that edge if present *)
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

(*todo: check that ~role is actually mentioned in protocol definition*)
let of_global_type gty ~role ~server =
  let json = ref "" in
  let count = ref 0 in
  let fresh () =
    let n = !count in
    count := n + 1 ;
    n
  in
  let make_refinement_annotation env next_l =
    if Config.refinement_type_enabled () then
      let silent_vars = env.silent_var_buffer in
      let rec_expr_updates =
        match next_l with
          | TVarG (tv, rec_exprs, _) ->
            let check_expr silent_vars e =
              let free_vars = Expr.free_var e in
              let unknown_vars = Set.inter free_vars silent_vars in
              if not @@ Set.is_empty unknown_vars then
                uerr
                  (UnknownVariableValue (role, Set.choose_exn unknown_vars))
            in
            let rec_expr_filter = Map.find_exn env.tv_to_rec_var tv in
            let rec_exprs =
              List.map2_exn
                ~f:(fun (x, _) y -> if not x then Some y else None)
                rec_expr_filter rec_exprs
            in
            let rec_exprs = List.filter_opt rec_exprs in
            List.iter ~f:(check_expr env.svars) rec_exprs
            ; rec_exprs
          | _ ->
            []
      in
      ({env with silent_var_buffer= []}, {silent_vars; rec_expr_updates})
    else (env, {silent_vars= []; rec_expr_updates= []})
  in
  let seen_choice = ref false in
  let mandatory_active_roles = ref (Set.add (Set.empty (module RoleName)) server) in
  let optional_active_roles = ref (Set.empty (module RoleName)) in
  let terminal = ref ~-1 in
  let rec conv_gtype_aux env=
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
        (*(Caml.Format.print_string ("send\n")) ;*)
        let curr = fresh () in
        let role_activations = role_activations @ [(send_n, recv_n, (m, curr))] in 
        let env, rannot = make_refinement_annotation env l in
        let env, next = conv_gtype_aux {env with active_roles; role_activations} l in
        let a = if RoleName.equal role send_n then
          SendA (recv_n, m, rannot)
        else (* if role equals recv_n *)
          RecvA (send_n, m, rannot)
        in
        let ref_a = RefA (Int.to_string curr ^ Int.to_string next) in
        json := sprintf "%s\n\"%s\": %s," (!json) (show_action_ref ref_a) (show_action a) ;
        let e = (curr, ref_a, next) in
        let g = env.g in
        let g = G.add_vertex g curr in
        let g = G.add_edge_e g e in
        ({env with g}, curr)
      | _ ->
        (*(Caml.Format.print_string ("other\n")) ;*)
        let role_activations = role_activations @ [(send_n, recv_n, (m, !count))] in
        let named_payloads =
          List.rev_filter_map
            ~f:(function
              | PValue (Some var, t) -> Some (var, t) | _ -> None )
            m.payload
        in
        if List.is_empty named_payloads || (not @@ Config.refinement_type_enabled ()) then 
          conv_gtype_aux {env with active_roles; role_activations} l
        else
          let svars =
            List.fold ~init:env.svars
              ~f:(fun acc (var, _) -> Set.add acc var)
              named_payloads
          in
          let silent_var_buffer = env.silent_var_buffer @ named_payloads in
          conv_gtype_aux {env with active_roles; role_activations; silent_var_buffer; svars} l
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
          tyvars= (tv, new_st) :: tyvars
        ; g
        ; state_to_rec_var= Map.set env.state_to_rec_var ~key:new_st ~data:rec_vars
        ; tv_to_rec_var = Map.add_exn env.tv_to_rec_var ~key:tv ~data:rec_vars
        }
      in
      let env, curr = conv_gtype_aux env l in
      let g = env.g in
      let g = G.add_edge_e g (new_st, EpsilonRef, curr) in
      let states_to_merge = (new_st, curr) :: env.states_to_merge in
      ({env with g; states_to_merge}, curr)
    | TVarG (tv, _, _) ->
      (*(Caml.Format.print_string ("tyvar\n")) ;*)
      let st = List.Assoc.find_exn ~equal:TypeVariableName.equal env.tyvars tv in
        (env, st)
    | ChoiceG (chooser, ls) ->
      let active_roles = Set.add active_roles chooser in
      if Int.equal !count 1 then (* if no msgs before first choice *)
        mandatory_active_roles := Set.add !mandatory_active_roles chooser
      ; seen_choice := true
      
      ; let curr = fresh () in
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

      let first_msg_is_distinct_and_from_chooser = fun ar ras ->
        let label_equals (pl1, lab1) (pl2, lab2) = 
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
      in
      let role_does_nothing_in_all_branches = fun ar ras -> 
        not @@ RoleName.equal ar server && (* server can't do nothing as it must get informed of the choice *)
        List.for_all ras ~f:(fun se -> 
          not @@ List.exists se ~f:(fun (s, r, _) ->
            RoleName.equal s ar || RoleName.equal r ar))
      in
      
      (* check over previous active roles *)
      Set.iter active_roles 
        ~f:(fun ar -> 
          if not @@ first_msg_is_distinct_and_from_chooser ar !choice_r_activations 
            && not @@ role_does_nothing_in_all_branches ar !choice_r_activations then
              uerr (BranchErrorPrevious (chooser, ar))
          )
                                                 
      ; let new_rs = List.map ~f:(fun l_rs -> Set.diff l_rs active_roles) !choice_active_rs in
      optional_active_roles := Set.union !optional_active_roles (Set.union_list (module RoleName) new_rs)
      ; let ars_and_ras = List.zip_exn new_rs !choice_r_activations in
      List.iter ~f:(fun (ars, ras) ->
        (* check over newly active roles *)
        if not @@ Set.for_all ~f:(fun r -> first_msg_is_distinct_and_from_chooser r [ras]) ars then
            uerr (BranchErrorNew (chooser, Set.to_list ars))
        ) ars_and_ras ;
      let g = env.g in

      (* don't do epsilon transition if next state is terminal *)
      (* this is for when a role is used (and becomes active) in one branch but not in another *)
      (* only works due to non-tail recursive limitation *)
      let non_terminal_nexts = List.filter ~f:(fun next -> next <> !terminal) nexts in
      let es = List.map ~f:(fun n -> (curr, EpsilonRef, n)) non_terminal_nexts in

      let g = G.add_vertex g curr in
      let g = List.fold ~f:G.add_edge_e ~init:g es in
      let states_to_merge =
          List.map ~f:(fun next -> (curr, next)) non_terminal_nexts @ env.states_to_merge
      in

      let rec get_ordered_role_activations' result ras =
        (* ordered flattening *)
        (* e.g. [[1,2,3,4],[a,b,c],[x,y]] --> [1,a,x,2,b,y,3,c,4] *)
        (* to make nested choices not cause outermost choice's well-formed/branched check to fail *)
        if List.for_all ~f:List.is_empty ras then
          !result
        else
          let leftover_cras = List.map ~f:(fun ra ->
            result := !result @ (List.take ra 1)
            ; List.drop ra 1
          ) ras
          in
          get_ordered_role_activations' result leftover_cras
      in
      let get_ordered_role_activations = get_ordered_role_activations' (ref []) in
      let role_activations = role_activations @ (get_ordered_role_activations !choice_r_activations) in
      ({env with g; states_to_merge; active_roles; role_activations}, curr)
    | CallG (_, _, _, l) ->
      conv_gtype_aux env l
  in
  let init_env = init_efsm_conv_env in
  let init_active_roles = Set.add init_env.active_roles server in
  let env, start = conv_gtype_aux {init_env with active_roles=init_active_roles} gty in
  let optional_active_roles_list = Set.to_list !optional_active_roles in
  let mandatory_active_roles_list = Set.to_list !mandatory_active_roles in
  json := "{" ^ !json ^ "\n}\n\n" ;
  (Caml.Format.print_string (!json)) ;
  let g = env.g in
  let state_to_rec_var = env.state_to_rec_var in
  if not @@ List.is_empty env.states_to_merge then (* TODO: add rec_var unimpl thing *)
    let rec aux (start, g, state_to_rec_var) = function
      | [] -> ((start, g), (mandatory_active_roles_list, optional_active_roles_list))
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
          let state_to_rec_var =
            match Map.find state_to_rec_var from_state with
            | None -> state_to_rec_var
            | Some rv ->
                Map.update
                  ~f:(function
                    | None -> rv
                    | Some _ -> rv 
                     (* todo: figure out what this is *)
                        (*Err.unimpl
                          "Multiple recursions with variables in choices" *))
                  state_to_rec_var to_state
          in
          aux (start, g, state_to_rec_var) rest
    in
    aux (start, g, state_to_rec_var) env.states_to_merge
  else ((start, g), (mandatory_active_roles_list, optional_active_roles_list))
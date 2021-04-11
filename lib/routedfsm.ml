open! Base
open Printf
open Gtype
open Names
open Graph
open Err

type action =
  | SendA of RoleName.t * Gtype.message
  | RecvA of RoleName.t * Gtype.message
  | Epsilon
[@@deriving ord, sexp_of]

let rec show_action =
  function
  | SendA (r, msg) ->
      sprintf "%s!%s" (RoleName.user r) (Gtype.show_message msg)
  | RecvA (r, msg) ->
      sprintf "%s?%s" (RoleName.user r) (Gtype.show_message msg)
  | Epsilon -> "ε"

module Label = struct
  module M = struct
    type t = action

    let compare = compare_action

    let sexp_of_t = sexp_of_action
  end

  include M
  include Comparator.Make (M)

  let default = Epsilon
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

  let edge_attributes (_, a, _) = [`Label (show_action a)]

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
  ; tyvars: (TypeVariableName.t * (int * ((RoleName.t, RoleName.comparator_witness) Set.t))) list
  ; states_to_merge: (int * int) list
  ; active_roles: (RoleName.t, RoleName.comparator_witness) Set.t
  ; role_activations: (RoleName.t * RoleName.t * (message * int)) list }
let init_efsm_conv_env:efsm_conv_env = 
  { g= G.empty
  ; tyvars= []
  ; states_to_merge= []
  ; active_roles= Set.empty (module RoleName)
  ; role_activations= [] }

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
          | Epsilon -> g 
          | label -> G.add_edge_e g (ori, label, dest))
        g from_state g
    in
    let g =
      G.fold_pred_e
        (fun (ori, label, dest) g ->
          let ori = subst ori in
          let dest = subst dest in
          match label with
          | Epsilon -> g 
          | label -> G.add_edge_e g (ori, label, dest))
        g from_state g
    in
    let g = G.remove_vertex g from_state in
    g

(*todo: check that ~role is actually mentioned in protocol definition*)
let of_global_type gty ~role ~server =
  let count = ref 0 in
  let fresh () =
    let n = !count in
    count := n + 1 ;
    n
  in
  let terminal = ref ~-1 in
  let first_active_role = ref server in
  let rec conv_gtype_aux first_active_role env=
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
      (if RoleName.equal !first_active_role server then
        (*(Caml.Format.print_string (RoleName.user (if RoleName.equal send_n server then recv_n else send_n))) ;*)
        first_active_role := (if RoleName.equal send_n server then recv_n else send_n))
      ; let active_roles = Set.add active_roles recv_n in
      let active_roles = Set.add active_roles send_n in
      match role with
      | _ when RoleName.equal role send_n ->
        (*(Caml.Format.print_string ("send\n")) ;*)
        let curr = fresh () in
        let a = SendA (recv_n, m) in
        let role_activations = role_activations @ [(send_n, recv_n, (m, curr))] in 
        let env, next = conv_gtype_aux first_active_role {env with active_roles; role_activations} l in
        let e = (curr, a, next) in
        let g = env.g in
        let g = G.add_vertex g curr in
        let g = G.add_edge_e g e in
        ({env with g}, curr)
      | _ when RoleName.equal role recv_n ->
        (*(Caml.Format.print_string ("recv\n")) ;*)
        let curr = fresh () in
        let a = RecvA (send_n, m) in
        let role_activations = role_activations @ [(send_n, recv_n, (m, curr))] in 
        let env, next = conv_gtype_aux first_active_role {env with active_roles; role_activations} l in
        let e = (curr, a, next) in
        let g = env.g in
        let g = G.add_vertex g curr in
        let g = G.add_edge_e g e in
        ({env with g}, curr)
      | _ ->
        (*(Caml.Format.print_string ("other\n")) ;*)
        let role_activations = role_activations @ [(send_n, recv_n, (m, !count))] in
        conv_gtype_aux first_active_role {env with active_roles; role_activations} l
    )
    | MuG (tv, _, l) ->
      let new_st = fresh () in
      let g = G.add_vertex g new_st in
      let env = {env with tyvars= (tv, (new_st, active_roles)) :: tyvars; g} in
      let env, curr = conv_gtype_aux first_active_role env l in
      let g = env.g in
      let g = G.add_edge_e g (new_st, Epsilon, curr) in
      let states_to_merge = (new_st, curr) :: env.states_to_merge in
      ({env with g; states_to_merge}, curr)
    | TVarG (tv, _, _) ->
      (*(Caml.Format.print_string ("tyvar\n")) ;*)
      (*st, prior_active_roles -- may need prior_active_roles to know whether to dc? *)
      let st, _ = List.Assoc.find_exn ~equal:TypeVariableName.equal env.tyvars tv in
        (env, st)
    | ChoiceG (chooser, ls) ->
      let curr = fresh () in
      let choice_active_rs = ref [] in
      let choice_r_activations:((RoleName.t * RoleName.t * (message * state)) list list ref) = ref [] in
      let env, nexts = List.fold_map ~f:(
        fun e l ->
          let acc_env, acc_n = conv_gtype_aux first_active_role e l in
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
      
      (* check that active_roles size is greater than 1, i.e. it's not just server *)
      Set.iter active_roles (* check over previous active roles *)
        ~f:(fun ar -> 
          if not @@ first_msg_is_distinct_and_from_chooser ar !choice_r_activations 
            && not @@ role_does_nothing_in_all_branches ar !choice_r_activations then
              uerr (BranchErrorPrevious (chooser, ar))
          )
                                                 
      ; let new_rs = List.map ~f:(fun l_rs -> Set.diff l_rs active_roles) !choice_active_rs in
      let ars_and_ras = List.zip_exn new_rs !choice_r_activations in
      List.iter ~f:(fun (ars, ras) ->
        (* check over newly active roles *)
        if not @@ Set.for_all ~f:(fun r -> first_msg_is_distinct_and_from_chooser r [ras]) ars then
            uerr (BranchErrorNew (chooser, Set.to_list ars))
        ) ars_and_ras ;
      let g = env.g in

      (* don't do epsilon transition if next state is terminal *)
      (* this is for when a role is used (and becomes active) in one branch but not in another *)
      (* only works due to non-tail recursive limitation *)
      (* will have to think of something else should that change *)
      let non_terminal_nexts = List.filter ~f:(fun next -> next <> !terminal) nexts in
      let es = List.map ~f:(fun n -> (curr, Epsilon, n)) non_terminal_nexts in

      let g = G.add_vertex g curr in
      let g = List.fold ~f:G.add_edge_e ~init:g es in
      let states_to_merge =
          List.map ~f:(fun next -> (curr, next)) non_terminal_nexts @ env.states_to_merge
      in

      let active_roles = Set.add active_roles chooser in
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
      conv_gtype_aux first_active_role env l
  in
  let init_env = init_efsm_conv_env in
  let init_active_roles = Set.add init_env.active_roles server in
  let env, start = conv_gtype_aux first_active_role {init_env with active_roles=init_active_roles} gty in
  let g = env.g in
  if not @@ List.is_empty env.states_to_merge then
    let rec aux (start, g) = function
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
    aux (start, g) env.states_to_merge
  else (start, g)
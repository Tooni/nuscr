open! Base
open Printf
open Gtype
open Names
open Graph
open Err

type c_action =
  | MsgA of RoleName.t * Gtype.message * RoleName.t
  | Epsilon
[@@deriving ord, sexp_of]

let rec show_c_action = 
  function
  | MsgA (p, m, q) ->
      sprintf "%s → %s: %s" (RoleName.user p) (RoleName.user q) (Gtype.show_message m)
  | Epsilon -> "ε"

module CLabel = struct
  module M = struct
    type t = c_action

    let compare = compare_c_action

    let sexp_of_t = sexp_of_c_action
  end

  include M
  include Comparator.Make (M)

  let default = Epsilon
end

module G = Persistent.Digraph.ConcreteLabeled (Int) (CLabel)

type t = G.t

type state = int

module Display = struct
  include G

  let vertex_name = Int.to_string

  let graph_attributes _ = []

  let default_vertex_attributes _ = []

  let vertex_attributes _ = []

  let default_edge_attributes _ = []

  let edge_attributes (_, a, _) = [`Label (show_c_action a)]

  let get_subgraph _ = None
end

module DotOutput = Graphviz.Dot (Display)

let show g =
  let buffer = Buffer.create 4196 in
  let formatter = Caml.Format.formatter_of_buffer buffer in
  DotOutput.fprint_graph formatter g ;
  Caml.Format.pp_print_flush formatter () ;
  Buffer.contents buffer

type chor_automata_conv_env =
  { g: G.t
          (*startId prevNode prevSendAndRecvRoles*)
  ; prevs: (state * state * (RoleName.t * RoleName.t)) list
  ; tyvars: (TypeVariableName.t * (int * int) list) list
  ; states_to_merge: (int * int) list }
let init_chor_automata_conv_env:chor_automata_conv_env =
  { g= G.empty
  ; prevs= []
  ; tyvars= []
  ; states_to_merge= []}

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

let of_global_type gty =
  let count = ref 0 in
  let fresh () =
    let n = !count in
    count := n + 1
    ; n
  in
  let starts = ref [] in
  let rec conv_gtype_aux env = 
    let {g; prevs; tyvars; states_to_merge} = env in
    function
    | EndG ->
      env
    | MessageG (m, send_n, recv_n, l) ->
      (*let prev_str (start_id, c, (s, r)) = "(" ^ Int.to_string start_id ^ "," ^ Int.to_string c ^ " , " ^ RoleName.user s ^ "," ^ RoleName.user r ^ ")" in 
      let prevs_str prevs = "\n" ^ String.concat ~sep:"__" (List.map ~f:prev_str prevs) ^ "\n" in*)
      let a = MsgA (send_n, m, recv_n) in
      let (prev, curr, prevs) = 
        let prev_search = List.find prevs ~f:(fun (_, _, (s, r)) -> RoleName.equal send_n s || RoleName.equal send_n r) in
        (match prev_search with
          | Some (start_id, prev, (s, r)) ->
            let prev_equality (start_id2, prev2, (s2, r2)) = 
              not (Int.equal start_id start_id2 && Int.equal prev prev2 &&
                   RoleName.equal s s2 && RoleName.equal r r2)
            in
            let curr' = fresh () in
            let new_prev = (start_id, curr', (send_n, recv_n)) in
            let new_prevs =
                (List.take_while prevs ~f:prev_equality)
                @ [new_prev]
                @ List.drop (List.drop_while prevs ~f:prev_equality) 1
            in
            (prev, curr', new_prevs)
          | None ->
            let prev = fresh () in
            let curr' = fresh () in
            starts := prev :: !starts
            ; let new_prev = (prev, curr', (send_n, recv_n)) in
            let new_prevs = prevs @ [new_prev] in
            (prev, curr', new_prevs))
      in
      (*(Caml.Format.print_string (prevs_str prevs)) ;*)
      let e = (prev, a, curr) in
      let g = G.add_vertex g curr in
      let g = G.add_edge_e g e in
      conv_gtype_aux {env with g; prevs} l
    | ChoiceG (selector, ls) ->
      let prevs = 
        if List.is_empty env.prevs then 
          let curr = fresh () in
          starts := curr :: !starts
          (* check against selector is ok as all choices will start with messages from selector
             for well-branchedness, verified in Routedefsm *)
          ; [(curr, curr, (selector, selector))]
        else 
          env.prevs 
      in
      List.fold ls ~init:env ~f:(fun env' -> conv_gtype_aux {env' with prevs})
    | MuG (tv, _, l) ->
      let tyvars = 
        (if !count = 0 then
          (tv, [])
        else
          let rec_states = List.map prevs ~f:(fun (id, p, _) ->  (id, p)) in
          (tv, rec_states))
        :: tyvars
      in
      conv_gtype_aux {env with tyvars} l
    | TVarG (tv, _, _) ->
      let starts_and_rec_states = List.Assoc.find_exn ~equal:TypeVariableName.equal env.tyvars tv in
      let st_to_merge = ref [] in
      let g = List.fold prevs ~init:g 
        ~f:(fun g (id, prev, (s, r)) ->
          let check_if_well_sequenced n = 
            let outgoing_edges = G.succ_e g n in
            List.iter outgoing_edges ~f:(fun (_, a, _) ->
              match a with
                | MsgA (s', _, _) ->
                  if not (RoleName.equal s' s || RoleName.equal s' r) then
                    uerr (ChorAutomataNotWellSequencedOverRecursion tv) (* todo: print more info with this error *)
                | Epsilon ->
                  () )
          in
          let goto_state =
            (match List.find starts_and_rec_states ~f:(fun (id', _) -> Int.equal id' id) with 
              | Some (_, rec_state) ->
                check_if_well_sequenced rec_state
                ; st_to_merge := (prev, rec_state) :: !st_to_merge
                ; rec_state
              | None ->
                check_if_well_sequenced id
                ; st_to_merge := (prev, id) :: !st_to_merge
                ; id)
          in 
          G.add_edge_e g (prev, Epsilon, goto_state))
      in
      {env with g; states_to_merge= states_to_merge @ !st_to_merge}
    | CallG (_, _, _, _) ->
      env
    in
    let env = conv_gtype_aux init_chor_automata_conv_env gty in
    let g = env.g in
    (* sub-automata have disjoint participants iff
       the sum of the cardinalities of the sets == the cardinality of the union of the sets *)
    let rec get_role_set_from_start n = 
      let outgoing_edges = G.succ_e g n in
      let next_nodes = ref [] in
      let curr_set = Set.union_list (module RoleName) 
        (List.map outgoing_edges ~f:(fun (_, a, n2) ->
          let sr = Set.empty (module RoleName) in
          match a with
            | MsgA (s, _, r) ->
              next_nodes := n2 :: !next_nodes
              ; Set.add (Set.add sr s) r
            | Epsilon -> (* epsilon implies recursion on the graph *)
              sr))
      in
      Set.union 
        curr_set
        (Set.union_list (module RoleName) 
          (List.map !next_nodes ~f:get_role_set_from_start))
    in
    let chor_automata_have_disjoint_participants =
      let role_sets = List.map !starts ~f:get_role_set_from_start in
      let roles_union = Set.union_list (module RoleName) role_sets in
      let cardinality_of_union = Set.length roles_union in
      let role_set_lengths = List.map role_sets ~f:Set.length in
      let sum_of_cardinalities = List.reduce_exn role_set_lengths ~f:(+) in
      Int.equal sum_of_cardinalities cardinality_of_union
    in
    if chor_automata_have_disjoint_participants then
      ()
      (*(Caml.Format.print_string "\nTHIS CHOREOGRAPHY AUTOMATON'S SUB-AUTOMATA HAVE DISJOINT PARTICIPANTS\n\n")*)
    else 
      (*(Caml.Format.print_string (show g ^ "\n\n")*)
      uerr ChorAutomataNotWellSequencedDueToNonDisjointParticipants
    ; if not @@ List.is_empty env.states_to_merge then
      let rec aux (start, g) = function
        | [] -> (*(Caml.Format.print_string (show g ^ "\n\n") ;*) g
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
      aux (0, g) env.states_to_merge
    else (*(Caml.Format.print_string (show g ^ "\n\n") ;*) g
    
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

let show_c_action =
  function
  | Epsilon -> "ε"
  | MsgA (p, m, q) ->
    sprintf "%s → %s: %s" (RoleName.user p) (RoleName.user q) (Gtype.show_message m)

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
  ; tyvars: (TypeVariableName.t * int) list
  ; states_to_merge: (int * int) list }
let init_chor_automata_conv_env:chor_automata_conv_env =
  { g= G.empty
  ; tyvars= []
  ; states_to_merge= []}

let rec extract_pairs =
  function
  | [] -> 
    []
  | h :: tl ->
    List.map tl ~f:(fun t -> (h, t)) @ extract_pairs tl

let check_labels gt = 
  let rec get_labels =
  function 
  | EndG ->
    Set.empty (module LabelName)
  | MessageG (m, _, _, l) ->
    Set.add (get_labels l) m.label
  | ChoiceG (_, ls) ->
    let labels = List.map ls ~f:get_labels in
    let pairs = extract_pairs labels in
    if not @@ List.for_all pairs ~f:(fun (l1, l2) -> Set.is_empty @@ Set.inter l1 l2) then 
      uerr NonDisjointLabelsAcrossBranches
    ; Set.union_list (module LabelName) (List.map ls ~f:get_labels)
  | MuG (_, _, l) ->
    get_labels l
  | TVarG (_, _, _) ->
    Set.empty (module LabelName)
  | CallG (_, _, _, l) -> (* unimpl *)
    get_labels l
  in 
  let _ = get_labels gt in
  ()

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

let of_global_type_for_role gty role =
  let count = ref 0 in
  let terminal = ref ~-1 in
  let fresh () =
    let n = !count in
    count := n + 1 ;
    n
  in
  let rec conv_gtype_aux env = 
    let {g; tyvars; _} = env in
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
    | MessageG (m, send_n, recv_n, l) ->
      if RoleName.equal role send_n || RoleName.equal role recv_n then
        let curr = fresh () in
        let a = MsgA (send_n, m, recv_n) in
        let env, next = conv_gtype_aux env l in
        let e = (curr, a, next) in
        let g = env.g in
        let g = G.add_vertex g curr in
        let g = G.add_edge_e g e in
        ({env with g}, curr)
      else
        conv_gtype_aux env l
    | ChoiceG (_, ls) ->
      let curr = fresh () in
      let env, nexts = List.fold_map ~f:conv_gtype_aux ~init:env ls in
      let g = env.g in
      let es = List.map ~f:(fun n -> (curr, Epsilon, n)) nexts in
      let g = G.add_vertex g curr in
      let g = List.fold ~f:G.add_edge_e ~init:g es in
      let states_to_merge =
        List.map ~f:(fun next -> (curr, next)) nexts @ env.states_to_merge
      in
      ({env with g; states_to_merge}, curr)
    | MuG (tv, _, l) ->
      let new_st = fresh () in
      let g = G.add_vertex g new_st in
      let env =
        { env with
          tyvars= (tv, new_st) :: tyvars
        ; g
        }
      in
      let env, curr = conv_gtype_aux env l in
      let g = env.g in
      let g = G.add_edge_e g (new_st, Epsilon, curr) in
      let states_to_merge = (new_st, curr) :: env.states_to_merge in
      ({env with g; states_to_merge}, curr)
    | TVarG (tv, _, _) ->
      (env, List.Assoc.find_exn ~equal:TypeVariableName.equal env.tyvars tv)
    | CallG (_, _, _, l) -> (* unimpl *)
      conv_gtype_aux env l
    in
    let env, _ = conv_gtype_aux init_chor_automata_conv_env gty in
    let g = env.g in
    if not @@ List.is_empty env.states_to_merge then
      let rec aux (start, g) = function
        | [] -> g
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
    else g

let product gs =
  let count = ref 1 in
  let fresh () =
    let n = !count in
    count := n + 1 ;
    n
  in
  let system_state_id = 
    Map.fold
      ~init:"" 
      ~f:(fun ~key:id ~data:s acc -> 
        sprintf "%s@%s.%s" acc (Int.to_string id) (Int.to_string s))
  in
  let ids_to_gs = 
    Map.of_alist_exn (module Int) @@ 
      List.mapi gs ~f:(fun i g -> (i, g))
  in
  let rec product_aux ss prod src m =
    let es = Map.fold ss ~init:[] 
      ~f:(fun ~key:id ~data:s acc ->
        let g = Map.find_exn ids_to_gs id in
        let next_es = G.succ_e g s in
        acc @ List.map next_es ~f:(fun e -> (id, e)))
    in
    let is_dual ((id1, (_, a1, dest1)), (id2, (_, a2, dest2))) =
      if CLabel.compare a1 a2 = 0 then
        Some (a1, (id1, dest1), (id2, dest2))
      else
        None
    in
    let pairs = extract_pairs es in
    let duals = List.filter_map pairs ~f:is_dual in
    if List.is_empty duals then
      (prod, m)
    else 
      List.fold duals ~init:(prod, m)
        ~f:(fun (prod, m) (a, (id1, dest1), (id2, dest2))  ->
          let ss = Map.set ss ~key:id1 ~data:dest1 in
          let ss = Map.set ss ~key:id2 ~data:dest2 in
          let key = system_state_id ss in
          if Map.mem m key then 
            let dest = Map.find_exn m key in 
            let prod = G.add_edge_e prod (src, a, dest) in
            (prod, m)
          else
            let dest = fresh () in
            let m = Map.add_exn m ~key ~data:dest in
            let prod = G.add_edge_e prod (src, a, dest) in
            product_aux ss prod dest m)
  in
  let ss = Map.of_alist_exn (module Int) @@ List.map (Map.keys ids_to_gs) ~f:(fun id -> (id, 0)) in
  let prod = G.empty in
  let src = 0 in
  let m = Map.add_exn (Map.empty (module String)) ~key:(system_state_id ss) ~data:0 in
  fst @@ product_aux ss prod src m

let of_global_type gty all_roles _(*role*) =
  check_labels gty
  ; let locals = List.map ~f:(of_global_type_for_role gty) all_roles in
  (*List.iter locals ~f:(fun g -> Caml.Format.print_string (show g ^ "\n")) 
  ; Caml.Format.print_string  ("\n----------\n"); *)
  product locals


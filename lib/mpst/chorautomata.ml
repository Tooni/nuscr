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
  ; alphabet: c_action list
  ; states_to_merge: (int * int) list }
let init_chor_automata_conv_env:chor_automata_conv_env =
  { g= G.empty
  ; tyvars= []
  ; alphabet= []
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
    let {g; tyvars; alphabet; _} = env in
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
        let alphabet = a :: alphabet in
        let env, next = conv_gtype_aux {env with alphabet} l in
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
    let alphabet = env.alphabet in
    if not @@ List.is_empty env.states_to_merge then
      let rec aux (start, g) = function
        | [] -> (alphabet, g)
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
    else (alphabet, g)

(* https://en.wikipedia.org/wiki/Pairing_function#Cantor_pairing_function *)
let get_cantor_pair (k1, k2) =
  ((k1 + k2) * (k1 + k2 + 1)) / 2 + k2

let label_equal a1 a2 = 
  CLabel.compare a1 a2 = 0

(* Find cartesian product of two graphs *)
(* roughly the 2nd algorithm from http://www.iaeng.org/publication/WCECS2010/WCECS2010_pp141-143.pdf *)
(* but uses `found_x' and `found_y' to skip some self-transitions *)
let product (a1, g1) (a2, g2) =
  if G.is_empty g1 then
    (a2, g2)
  else if G.is_empty g2 then
    (a1, g1)
  else
    let count = ref 1 in
    let fresh () =
      let n = !count in
      count := n + 1 ;
      n
    in
    let alphabet = a1 @ a2 in
    (* cantor pair of (0,0) is 0 *)
    let g = G.add_vertex G.empty 0 in
    let r = [(0, 0)] in
    (* `m' maps cantor pairs to nodes *)
    (* can't use cantor pairs directly as nodes because they'd get very large in successive products *)
    let m = Map.add_exn (Map.empty (module Int)) ~key:0 ~data:0 in
    let rec product_aux (g, r, m) = 
      if List.is_empty r then
        (alphabet, g)
      else
        let (x, y) as prod_src = List.hd_exn r in
        let r = List.tl_exn r in
        product_aux @@ List.fold alphabet ~init:(g, r, m) 
          ~f:(fun (g, r, m) a ->
            let find_dest edges src = 
              match (List.find edges ~f:(fun (_, label, _) -> label_equal label a)) with
                | Some (_, _, dest) -> (dest, true)
                | None -> (src, false)
            in
            let x_succ = G.succ_e g1 x in
            let y_succ = G.succ_e g2 y in
            let (dest_x, found_x) = find_dest x_succ x in
            let (dest_y, found_y) = find_dest y_succ y in
            let prod_dest = (dest_x, dest_y) in
            let prod_dest_encoded = get_cantor_pair prod_dest in
            let (g, r, m) =
              if not @@ Map.mem m prod_dest_encoded then
                let curr = fresh () in
                (G.add_vertex g curr,
                 prod_dest :: r,
                 Map.set m ~key:prod_dest_encoded ~data:curr)
              else
                (g, r, m)
            in
            if not found_x && not found_y then
              (g, r, m)
            else
              let e_src = Map.find_exn m @@ get_cantor_pair prod_src in
              let e_dest = Map.find_exn m prod_dest_encoded in
              let new_e = (e_src, a, e_dest) in
              (G.add_edge_e g new_e, r, m))
    in
    product_aux (g, r, m)

(* `trims' global product to remove transitions/states that break data dependencies. *)
(* Traverses global product (g) while traversing through equivalent transitions in local graphs (gs). *)
(* For each global transition, only adds to resultant trimmed graph if transition was 
   also possible in two local graphs, i.e. the send and the receive *)
let trim g gs =
  let ids_to_gs = Map.of_alist_exn (module Int) @@ List.mapi gs ~f:(fun i g -> (i, g)) in
  let rec trim_aux global_s local_ss result_g seen = 
    let global_es = G.succ_e g global_s in
    let local_es = Map.fold local_ss ~init:[] 
      ~f:(fun ~key:id ~data:s ->
        let g = Map.find_exn ids_to_gs id in
        List.cons (id, G.succ_e g s))
    in
    List.fold global_es ~init:result_g 
      ~f:(fun result_g ((_, global_a, dest) as e) ->
        let matching_locals = List.filter_map local_es 
          ~f:(fun (id, es) -> 
            match List.find es ~f:(fun (_, local_a, _) -> label_equal local_a global_a) with
            | Some (_, _, dest') -> Some (id, dest')
            | None -> None)
        in
        if List.length matching_locals = 2 then
          let result_g = G.add_edge_e result_g e in
          let global_s = dest in
          let local_ss = List.fold matching_locals ~init:local_ss 
            ~f:(fun local_ss (id, s) -> Map.set local_ss ~key:id ~data:s) 
          in
          if List.mem seen global_s ~equal:(=) then 
            result_g
          else
            trim_aux global_s local_ss result_g (dest :: seen)
        else
          result_g)
  in
  let global_s = 0 in
  (* mapping ids to starts *)
  let local_ss = Map.of_alist_exn (module Int) @@ List.map (Map.keys ids_to_gs) ~f:(fun id -> (id, 0)) in
  let result_g = G.empty in
  let seen = [] in
  trim_aux global_s local_ss result_g seen

let of_global_type gty all_roles _(*role*) =
  check_labels gty
  ; let locals = List.map ~f:(of_global_type_for_role gty) all_roles in
  (*List.iter locals ~f:(fun g -> Caml.Format.print_string (show g ^ "\n")) 
  ; Caml.Format.print_string  ("\n----------\n"); *)
  let (_, naive_product) = List.fold locals ~init:([], G.empty) ~f:product in
  let trimmed_product = trim naive_product (List.map ~f:snd locals) in
  trimmed_product


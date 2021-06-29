(** Choreography Automata **)

open Names

(** Transitions in the choreography automata *)
type c_action =
| MsgA of RoleName.t * Gtype.message * RoleName.t
| Epsilon  (** Not used *)

(** Type of states in EFSM *)
type state = int

(** EFSM graph representation *)
module G :
  Graph.Sig.P
    with type V.t = state
     and type E.label = c_action
     and type E.t = state * c_action * state

(** Type of the Choreography Automata *)
type t = G.t

val of_global_type : Gtype.t -> RoleName.t -> state * t
(** Construct an choreography automata from a global type *)

val show : t -> string
(** Produce a DOT representation of choreography automata, which can be visualised by Graphviz *)

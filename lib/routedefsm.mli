(** Endpoint finite state machines (EFSM) *)

open Names

(** Transitions in the EFSM *)
type action =
| SendA of RoleName.t * Gtype.message  (** Sending a [message] to [name] *)
| RecvA of RoleName.t * Gtype.message (** Receiving a [message] from [name] *)
| SendAWithNewRoles of RoleName.t * RoleName.t list * Gtype.message
| RecvAWithNewRoles of RoleName.t * RoleName.t list * Gtype.message
| Epsilon  (** Not used *)

(** Type of states in EFSM *)
type state = int

(** EFSM graph representation *)
module G :
  Graph.Sig.P
    with type V.t = state
     and type E.label = action
     and type E.t = state * action * state

(** Type of the EFSM *)
type t = G.t

val of_global_type : Gtype.t -> role:RoleName.t -> server:RoleName.t -> (state * t) * (RoleName.t list * RoleName.t list)

val show : t -> string
(** Produce a DOT representation of EFSM, which can be visualised by Graphviz *)

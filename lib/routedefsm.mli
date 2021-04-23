(** Routed endpoint finite state machines *)

open Names

(** Annotation for refined actions *)
type refinement_action_annot =
  { silent_vars: (VariableName.t * Expr.payload_type) list
        (** List of silent variables and their types *)
  ; rec_expr_updates: Expr.t list
        (** List of updates to recursion variables *) }
[@@deriving ord, sexp_of]
  
(** Transitions in the EFSM *)
type action =
  | SendA of RoleName.t * Gtype.message * refinement_action_annot
      (** Sending a [message] to [name] *)
  | RecvA of RoleName.t * Gtype.message * refinement_action_annot
      (** Receiving a [message] from [name] *)
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

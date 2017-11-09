From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A semantics of contracts with decidable deterministic transitions *)

Section State.

Definition value := nat.
Definition address := nat.
Definition tag := nat.
Definition payload := (seq (nat * seq nat)).

(* Message with a payload *)
Record message := Msg {
      val    : value;
      sender : address;
      method : tag;
      body   :  payload
}.

(* State of a contract *)
(* Record cstate (T : Type) := CState { *)
(*       my_id : address; *)
(*       balance : value; *)
(*       state : T   *)
(* }. *)

(* Global blockchain state *)
Record bstate := BState {
      block_num : nat;
      (* Anything else? *)               
}.

End State.

Section Protocol.

Section Transitions.

(* State type *)
Variable S: Type.

(* A response from a transition *)
Definition resp_type := (address * value * tag * payload)%type.
Definition msg_bal (rt : resp_type) : value := rt.1.1.2.

(* Transitions are functions *)
Definition trans_fun_type :=
  address -> value -> S -> message -> bstate -> (S * option message).
  
(* Contract transition in the spirit of I/O automata *)
Record ctransition :=
  CTrans {
      (* Unique tag of a transition in the protocol *)
      ttag : tag;
      
      (* Funcion (bstate, state, msg) :-> (state', option msg') *)
      tfun : trans_fun_type;
  }.

End Transitions.

Record Protocol (S : Type) :=
  CProt {
      (*Account id *)
      acc : address;
      (* Initial balance *)
      init_bal : nat;
      (* Initial state of a protocol *)
      init_state : S;      
      (* Protocol comes with a set of transitions *)
      transitions : seq (ctransition S);
      (* All transitions have unique tags *)
      _ : uniq (map (@ttag _) transitions)
    }.

End Protocol.

Section Semantics.

(* TODO: define semantics for blockchain-schedules: 

- Each components in the schedule has a timestamp, and an incoming message;
- In good schedules, schedules timestamps are (non-strictly) growing;
- Goodness also ensures that all messages are well-formed wrt. the tag;
- Contract functions are total, so we handle all incoming messages;
*)


End Semantics.


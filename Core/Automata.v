From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*

I'm not sure whether the I/O automata is the right model for this
task. Perhaps, we shoudl instead rethink the model in terms of
call/receive automata, which are similar to Disel's protocols in a way
they handle message passing. The only difference is that here we don't
have consider several communicating nodes, and instead work with just
one.

Thus, only "well-formed" messages get reacted to.

Furthermore, any transition can end with zero to n send messages
(i.e., calls), which will be sent in a non-deterministic order.

This should give enough space to implement the systems of
communicating contracts.

Next, we can proceed on making assertions for composing contracts ans
build on the research from the I/O automata community.

Finally, we will have to come up with a way to represent SC automata
in a language with exceptions and cost semantics, and compile it down
to EVM.

*)

(* Implementation of a simple state *)

Section State.

Definition value_type := nat.
Definition acc_id_type := nat.
Definition method_tag_type := nat.
Definition payload_type := (seq (nat * seq nat)).

(* Message with a payload *)
Record message :=
  Msg { value : value_type;
        sender : acc_id_type;
        method_tag : method_tag_type;
        payload :  payload_type
    }.

(* State of a contract *)
Record cstate (T : Type) :=
  CState {
      acc_id : acc_id_type;
      balance : value_type;
      state : T  
    }.

End State.

Section Protocol.

(* Protocol operates on states of a predefined type T *)

Section Transitions.

(* State type *)
Variable S: Type.

Definition input_filter_type := message -> cstate S -> bool.

Definition resp_type :=
  (acc_id_type * value_type * method_tag_type * payload_type)%type.

Definition msg_bal (rt : resp_type) : value_type := rt.1.1.2.
Definition msg_bals outs := sumn (map msg_bal outs).

Definition trans_rel_type (input_filter : input_filter_type) :=
  forall m st1, input_filter m st1 ->
         forall (s2 : S) (outs : seq resp_type), Prop.

(* Contract transition in the spirit of I/O automata *)
Record ctransition :=
  CTrans {
      (* Unique tag of a transition in the protocol *)
      tag : method_tag_type;
      
      (* Decidable filter on incoming messages *)
      input_filter : input_filter_type;

      (* Relation between input and output state *)
      trans_rel : trans_rel_type input_filter;
    }.

End Transitions.

Record Protocol (S : Type) :=
  CProt {
      (*Account id *)
      acc_num : nat;
      (* Initial balance *)
      init_bal : nat;
      (* Initial state of a protocol *)
      init_state : S;      
      (* Protocol comes with a set of transitions *)
      transitions : seq (ctransition S);
      (* All transitions have unique tags *)
      _ : uniq (map (@tag _) transitions)
    }.

(* TODO: Should we also say something about exclusivity of
         transition's preconditions? *)

(* TODO: Next, a program will have to be shown to refine a
         corresponding protocol. *)

End Protocol.

(***********************************************************)
(***              Protocol properties                    ***)
(***********************************************************)

Section Invariants.

Variable (S : Type) (p : Protocol S).

Notation s0 := (init_state p).
Notation acc := (acc_num p).
Notation b0 := (init_bal p).
Notation trans := (transitions p).

(* Definition of an inductive invariant with respect to a protocol p *)
(* Notice that the invariant updates the balance *)

Notation State := (cstate S).

Definition inductive (I : State -> Prop) :=
  (* A. Invariant holds in the initial state *)
  I (CState acc b0 s0) /\ 
  (* B. Any transition preserves the invariant *)
  forall ts, ts \In transitions p ->
  forall st1, I st1 ->
    forall m (pf : input_filter ts m st1) s2 outs,
    trans_rel pf s2 outs ->
  let bal' := (balance st1) - (msg_bals outs) + (value m) in
  I (CState acc bal' s2).

(* Here we assume that we always dispatch the messages, i.e., one
   cannot just transfer us money. *)

(* Determining whether we can reach s2 from s1 in one step *)
Definition can_step (st1 st2 : State) :=
  let: CState acc b1 s1 := st1 in
  exists ts m (pf : input_filter ts m st1) outs s2,
    [/\ ts \In transitions p,
     trans_rel pf s2 outs &
     let b2 := b1 - (msg_bals outs) + (value m) in
     st2 = CState acc b2 s2].
  
Fixpoint reachable' st1 st2 n :=
  if n is n'.+1
  then exists st, can_step st1 st /\ reachable' st st2 n'
  else st1 = st2.

Definition reachable st1 st2 := exists n, reachable' st1 st2 n.

(*****************************************************)
(*            Some modal connectives                 *)
(*****************************************************)

(* q holds since p becomes true *)
Definition since (p : State -> Prop) (q : State -> State -> Prop) :=
  forall st, p st -> forall st', reachable st st'-> q st st'.

(* TODO: can we come up with more sorts of invariants that have
   somewhat "temporal flavour?", e.g., in the spirit of eventual
   consistency. For instance, one should be able to prove that it's
   possible to withdraw money from th eaccount. *)

End Invariants.

(*************************************

Great story for compositionality: verify the "library" and then link
another contract against it and show that the joined interaction
always produces the same traces as it were only a client contract with
internal function.

This is still not equivalent to the usual execution because of limited
stack size. Thus, a call to library contract can fail, even if
everything is implemented correctly!

Wow.

Just wow.

 **************************************)

(************

Some more things to discuss or implement in the future:

* Formulate other sorts invariants for outgoing messages.

* Do we have to model the return value explicitly, or can we just
  represent it via message passing?

* How to fomulate the property that shouldn't be violated by the
  Puzzle contract from the Luu-al:CCS'16 paper?

  Perhaps, for this, we need a more "Concurrent" semantics, in which
  message sends are disparate from the corresponding contracts.

* Formalize the protocol of KoET contract and state the trace property
  that a previous king always gets correctly reimbursed. This would
  require to state properties over interactions between several
  parties.

* Start discussing a compiler from a back-end, verified with respect
  to a protocol.

*)


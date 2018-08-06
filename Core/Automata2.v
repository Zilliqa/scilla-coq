From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
From Heaps
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap coding.
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
      to     : address;
      method : tag;
      body   :  payload
}.

(* Augmented state of a contract *)
Record cstate (T : Type) := CState {
      my_id : address;
      balance : value;
      state : T
}.

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

Definition idle_fun : trans_fun_type := fun _ _ s _ _ => (s, None).
Definition idle := CTrans 0 idle_fun.

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

Definition tags {S : Type} (p : Protocol S) :=
  map (@ttag _) (transitions p).

End Protocol.

Section Semantics.

Variables (S : Type) (p : Protocol S).

(* Blockchain schedules *)
Definition schedule := seq (bstate * message).

(* In a well-formed schedule block numbers only grow *)
Fixpoint wf_sched (sch : schedule) :=
  if sch is s :: sch'
  then let bnum := block_num s.1 in
       all [pred s' | bnum <= block_num s'.1] sch' && wf_sched sch'
  else true.

Record step :=
  Step {
      pre  : cstate S;
      post : cstate S;
      out  : option message
  }.

Definition trace := seq step.

Definition apply_prot id bal s m bc : (S * option message) :=
  let n  := seq.find (fun t => ttag t == method m) (transitions p) in
  let tr := nth (idle S) (transitions p) n in
  let f  := tfun tr in
  f id bal s m bc.

Definition step_prot pre bc m : step :=
  let: CState id bal s := pre in
  let: (s', out) := apply_prot id bal s m bc in
  let: bal' := if out is Some m' then (bal + val m) - val m' else bal in
  let: s'' := if out is Some m' then s' else s in
  let: post := CState id bal' s'' in
  Step pre post out.

(* Map a schedule into a trace *)
Fixpoint execute (pre : cstate S) (sc: schedule) : trace :=
  if sc is (bc, m) :: sc'
  then let stp := step_prot pre bc m in
       stp :: execute (post stp) sc'
  else [::].



Definition state0 := CState (acc p) (init_bal p) (init_state p).

(* Execute from the initial contract state,
   if schedule is empty, repeat the initial state *)
Definition execute0 sc :=
  if sc is _ :: _
  then execute state0 sc
  else [:: Step state0 state0 None].

(****************************************************************)
(* Safety property:

For any state s in _any_ trace, starting from the initial one, 
the unary property I holds (i.e., I s).

*)
(****************************************************************)
Definition safe (I : cstate S -> Prop) : Prop :=
  forall (sc : schedule) pre post out,
    Step pre post out \In execute0 sc -> I pre /\ I post.

Lemma bad_tag_step bc m s :
  method m \notin (tags p) -> post (step_prot s bc m) = s.
Proof.
move=>M; rewrite /step_prot; case: s=>id bal s.
rewrite [apply_prot _ _ _ _ _]surjective_pairing/=.
rewrite /apply_prot.
suff X : seq.find (fun t : ctransition S => ttag t == method m) (transitions p) =
         size (transitions p).
by rewrite !X !nth_default ?leqnn//.
move: (find_size (fun t : ctransition S => ttag t == method m) (transitions p)).
rewrite leq_eqVlt; case/orP; first by move/eqP.
rewrite -has_find=>G. suff X: False by [].
rewrite /tags in M; clear s bal id bc.
elim: (transitions p) G M=>//t ts Hi/=.
case/orP; last by move/Hi=>{Hi} Hi H; apply: Hi; rewrite inE in H; case/norP: H.
by move/eqP=>->; rewrite inE eqxx.
Qed.

(* A strong induction principle for proving safety *)
Lemma safe_ind (I : cstate S -> Prop) :
  I state0 ->
  (forall pre bc m, 
      (method m \in tags p) -> I pre -> I (post (step_prot pre bc m))) ->
  safe I.
Proof.
move=>H1 H2; case=>[|[bc m] sc] pre pst out; first by case; case=>->->.
case/In_cons=>[E|];[| rewrite -/execute].
- have Z: pst = post (step_prot state0 bc m) by rewrite -E.
  subst pst; split.
  + suff Z: pre = state0 by subst pre.
    move: E; rewrite /step_prot/=.
    by rewrite [apply_prot _ _ _ _ _]surjective_pairing; case.
  case M: (method m \in tags p); first by apply: H2.
  by rewrite bad_tag_step// M.
have Hp: I (post (step_prot state0 bc m)).
- case M: (method m \in tags p); first by apply: H2.
  by rewrite bad_tag_step// M.
move: (post (step_prot state0 bc m)) Hp=>s Hi G; clear H1 bc m.
elim: sc s Hi G=>//[[bc m] sc] Hi s Is.
case/In_cons=>[E|];[|rewrite -/execute]; last first.
- move/Hi=>H; apply: H.
  case M: (method m \in tags p); first by apply: H2.
  by rewrite bad_tag_step// M.
suff Z: s = pre /\ pst = post (step_prot pre bc m).
- case: Z=>??; subst pre pst; split=>//.
  case M: (method m \in tags p); first by apply: H2.
  by rewrite bad_tag_step// M.
move: E; rewrite /step_prot/=; clear Is.
case: s=>id bal s; rewrite [apply_prot _ _ _ _ _]surjective_pairing.
by case=>->; rewrite {4 5}[apply_prot id bal s m bc]surjective_pairing.
Qed.

(*****************************************************)
(*            Some modal connectives                 *)
(*****************************************************)

Definition reachable' (st st' : cstate S) sc :=
  st' = post (last (Step st st None) (execute st sc)).

Definition reachable (st st' : cstate S) :=
  exists sc, reachable' st st' sc.

(* q holds since p , as long as schedule bits satisfy r. *)
Definition since_as_long
           (p : cstate S -> Prop)
           (q : cstate S -> cstate S -> Prop)
           (r : bstate * message -> Prop) :=
  forall sc st st',
    p st ->
    (forall b, b \In sc -> r b) ->
    reachable' st st' sc ->
    q st st'.

End Semantics.


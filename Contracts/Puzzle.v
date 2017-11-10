From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
From Heaps
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
From Contracts
Require Import Automata.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
An encoding of the Puzzle contract from Luu et al.

contract Puzzle {
  address public owner; 
  bool public locked; 
  uint public reward; 
  bytes32 public diff; 
  bytes public solution;

  function Puzzle() { //constructor
    owner = msg.sender;
    reward = msg.value;
    locked = false;
    diff = bytes32(11111); //pre-defined difficulty 
 }

  function(){ //main code, runs at every invocation 
    if (msg.sender == owner){ //update reward
      if (locked) throw;
      owner.send(reward);
      reward = msg.value; 
    } else if (msg.data.length > 0){ //submit a solution
      if (locked) throw;
      if (sha256(msg.data) < diff) {
        msg.sender.send(reward); //send reward solution = msg.data;
        locked = true;
      }
    }
  }
}

*)

Section Puzzle.

Variable bytes32 : nat -> nat.
Variable sha256 : nat -> nat.
(* Variable data_tag : nat. *)

Definition get_solution (pl : payload_type) :=
  if pl is (0, n :: _) :: _ then n
  else 0.

Record PuzzleState :=
  PS {
      owner : nat;
      locked: bool;
      reward : nat;
      diff : nat;
      solution : option nat;
    }.

Variable init_sender : nat.
Variable init_reward : nat.

(* Inital state after the constructor execution *)
Definition s0 := PS init_sender false init_reward (bytes32 11111) None.

(* Transition 1 -- changing the reward *)
Definition input_filter1 : input_filter_type PuzzleState :=
  fun m st1 => (sender m == init_sender) && (~~ locked (state st1)).

Definition new_reward s r :=
  let: PS a b _ d e := s in PS a b r d e.

Definition trans_rel1 : trans_rel_type input_filter1 :=
  fun m st1 _ s2 outs =>
    let s1 := state st1 in
    s2 = new_reward s1 (value m) /\
    outs = [:: (init_sender, reward s1, 0, [::])].

Definition update_reward := CTrans 1 trans_rel1.

(* Transition 2 *)
Definition input_filter2 : input_filter_type PuzzleState :=
  fun m st1 =>
    (sender m != init_sender) && (~~ locked (state st1)).

Definition trans_rel2 : trans_rel_type input_filter2 :=
  fun m st1 _ s2 outs =>
    let s1 := state st1 in
    let sol := get_solution (payload m) in
    if sha256 sol < diff s1
    then s2 = PS (owner s1) true (reward s1) (diff s1) (Some sol)
         /\ outs = [:: (sender m, reward s1, 0, [::])]
    else s2 = s1 /\ outs = [::].

Definition try_solution := CTrans 2 trans_rel2.

(* Puzzle protocol *)

Variable puzzle_acc : nat.

Program Definition puzzle_prot : Protocol PuzzleState :=
  @CProt _ puzzle_acc init_reward s0 [:: update_reward; try_solution] _.

(* Let the fun begin now *)
Section PuzzleInvariants.

Notation PState := (cstate PuzzleState).

(* 
   First invariant: the real balance at any time is not smaller than the reward,
   so the reward can be always transferred.
*)


Definition I_bal (st : PState) :=
  ~~ locked (state st) ->
  balance st >= reward (state st).

Theorem I_bal_ind : inductive puzzle_prot I_bal.
Proof.
split; rewrite /s0/I_bal/=; first by rewrite leqnn. 
move=>ts; case=>/=;[|case; last by []]=>Z [a bal s1];
subst ts=>/= Hi m pf s2 outs; last first.
- rewrite /trans_rel2; case:ifP=>// _; first by case=>->.  
  case=>->E/=/Hi=>G; subst outs.
  rewrite /msg_bals/=; rewrite subn0.
  suff X : bal <= bal + value m by apply: (leq_trans G X).
  by apply: leq_addr.
rewrite /trans_rel1/==>[][]->E.
rewrite /input_filter1/= in pf; case/andP:pf=>_ L.
case: (s1) L Hi E=>x b c d e/={s1}Z/(_ Z){Z}Hi->_.
by rewrite /msg_bals/msg_bal/= addn0 leq_addl.
Qed.


(* Since locked the balance doesn't change *)
Definition is_locked st := locked (state st).

Definition holds_same_balance (st st' : PState) :=
  balance st = balance st'.

(* Fact: since we're locked, the balance doesn't change 
   (this is how it should be!) *)
Theorem since_locked : since puzzle_prot is_locked holds_same_balance.
Proof.
move=>st1 Hl st2 [n]; elim: n st1 Hl=>/=[st _|n Hi st1 Hl [st][Hs Hr]]; first by move=><-. 
suff [Eb Hl']: balance st = balance st1 /\ is_locked st.
- by rewrite /holds_same_balance in Hi *; rewrite -Eb{Eb}; apply: Hi=>//.
clear Hr Hi st2.
case: st1 Hs Hl=>acc b[ow1]lk1 rw1 d1 s1 [ts][m]/=[pf][os][s2][G]_->{st}/= Hl.
rewrite /is_locked/= in Hl. rewrite Hl in pf=>{Hl}.
by case: G=>/=;[|case=>//]=>Z; subst ts; simpl in pf;
   rewrite?/input_filter1 /input_filter2 andbC/= in pf.
Qed.

(* TODO: Think of more interesting temporal properties *)

End PuzzleInvariants.

End Puzzle.




(* TODO: Implement the puzzle contract as an I/O automata *)




(* TODO: Prove a bunch of atomic invariants *)


 
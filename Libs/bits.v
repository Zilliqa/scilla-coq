From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple div.

Definition BITS n := n.-tuple bool.
Definition NIBBLE := BITS 4.
Definition BYTE := BITS 8.
Definition WORD := BITS 16.
Definition DWORD := BITS 32.
Definition QWORD := BITS 64.
Definition DWORDorBYTE (d: bool) :=
  BITS (if d then 32 else 8).

Require Import Recdef.

Function natToBits' (n : nat) (acc : seq bool) {measure id n} : seq bool :=
  if n is 0 then acc 
  else let:  (q, r) := (n %/ 2, n %% 2)
       in natToBits' q (odd r :: acc).
Proof.
by move=>_ _ n _; apply/ltP; apply: ltn_Pdiv=>//.
Defined.

Definition natToBitSeq n : seq bool :=
  if n is 0 then [:: false] else natToBits' n [::].

Definition natToBits n : (size (natToBitSeq n)).-tuple bool :=
  @Tuple (size (natToBitSeq n)) _ (natToBitSeq n) (eqxx _).

Lemma bitSize {n1 n2} (b1 : BITS n1):
  n1 <= n2 -> size (nseq (n2 - n1) false ++ b1) == n2.
Proof.
by move=>N; rewrite size_cat size_tuple size_nseq subnK//.
Qed.

Function bitShift {n1 n2 : nat} (b1: BITS n1) {pf: n1 <= n2}: BITS n2
  := Tuple (bitSize b1 pf).

(* TODO: figure out how to define it with a coercion *)
Notation "# n" := (@bitShift _ _ (natToBits n) _) (at level 2).


Program Definition w : WORD  := #1232.

(* TODO: develop the theory of 256-bit signed integers *)

(* From mathcomp.algebra *)
(* Require Import ssrint. *)

(* Check a. *)

(* Function nToB n : @tuple (size natsToBits n) bool := [tuple of natToBits n]. *)

(* Check natToBits. *)

(* Eval compute in natToBits' 41 [::]. *)


(* Require Import Coq.Strings.String. *)


(* Example a : NIBBLE := [tuple of [:: false; false; true; true]]. *)

(* Fixpoint fromHex s : BITS (length s * 4) := *)
(* if s is String c s *)
(* then joinNibble (charToNibble c) (fromHex s) else 0. *)

(* Check String. *)

(* Example fortytwo := #42 : BYTE. *)

(* Definition foo (t : Type) := *)
(*   if t is option nat then True else False. *)

(* Goal option nat = nat -> False. *)
(* move=> E. *)


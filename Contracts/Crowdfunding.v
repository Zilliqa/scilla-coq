From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Automata2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Crowdfunding.
(* Encoding of the Crowdfunding contract from the Scilla whitepaper *)

(******************************************************
contract Crowdfunding 
 (owner     : address,
  max_block : uint,
  goal      : uint)

(* Mutable state description *)
{
  backers : address => uint = [];
  funded  : boolean = false;
}

(* Transition 1: Donating money *)
transition Donate 
  (sender : address, value : uint, tag : string)
  (* Simple filter identifying this transition *)
  if tag == "donate" =>

  bs <- & backers;
  blk <- && block_number; 
  let nxt_block = blk + 1 in
  if max_block <= nxt_block
  then send (<to -> sender, amount -> 0,
	      tag -> main,
	      msg -> "deadline_passed">, MT)
  else
    if not (contains(bs, sender))
    then let bs1 = put(sbs, ender, value) in
         backers := bs1;
         send (<to -> sender,
                amount -> 0,
	        tag -> "main",
	        msg -> "ok">, MT)
    else send (<to -> sender,
                amount -> 0,
	        tag -> "main",
	        msg -> "already_donated">, MT)

(* Transition 2: Sending the funds to the owner *)
transition GetFunds
  (sender : address, value : uint, tag : string)
  (* Only the owner can get the money back *)
  if (tag == "getfunds") && (sender == owner) =>
  blk <- && block_number;
  bal <- & balance;
  if max_block >= blk
  then if goal <= bal
       then funded := true;   
            send (<to -> owner, amount -> bal,
                   tag -> "main", msg -> "funded">, MT)
       else send (<to -> owner, amount -> 0,
                   tag -> "main", msg -> "failed">, MT)
  else send (<to -> owner, amount -> 0, tag -> "main",
   	      msg -> "too_early_to_claim_funds">, MT)

(* Transition 3: Reclaim funds by a backer *)
transition Claim
  (sender : address, value : uint, tag : string)
  if tag == "claim" =>
  blk <- && block_number;
  if blk <= max_block
  then send (<to -> sender, amount -> 0, tag -> "main",
              msg -> "too_early_to_reclaim">, MT)
  else bs <- & backers;
       bal <- & balance;
       if (not (contains(bs, sender))) || funded ||
          goal <= bal 
       then send (<to -> sender, amount -> 0,
                   tag -> "main",
	           msg -> "cannot_refund">, MT)
       else 
       let v = get(bs, sender) in
       backers := remove(bs, sender);
       send (<to -> sender, amount -> v, tag -> "main", 
              msg -> "here_is_your_money">, MT)

 *******************************************************)

Record crowdState := CS {
   owner_mb_goal : address * nat * value;                          
   backers : seq (address * value); 
   funded : bool;
}.

(* Administrative setters/getters *)
Definition get_owner cs : address := (owner_mb_goal cs).1.1.
Definition get_goal cs : value := (owner_mb_goal cs).2.
Definition get_max_block cs : nat := (owner_mb_goal cs).1.2.


Definition set_backers cs bs : crowdState :=
  CS (owner_mb_goal cs) bs (funded cs).

Definition set_funded cs f : crowdState :=
  CS (owner_mb_goal cs) (backers cs) f.

(* Parameters *)
Variable init_owner : address.
Variable init_max_block : nat.
Variable init_goal : value.

(* Initial state *)
Definition init_state := CS (init_owner, init_max_block, init_max_block) [::] false.

(*********************************************************)
(********************* Transitions ***********************)
(*********************************************************)

(* Transition 1 *)
(*
transition Donate 
  (sender : address, value : uint, tag : string)
  (* Simple filter identifying this transition *)
  if tag == "donate" =>

  bs <- & backers;
  blk <- && block_number; 
  let nxt_block = blk + 1 in
  if max_block <= nxt_block
  then send (<to -> sender, amount -> 0,
	      tag -> main,
	      msg -> "deadline_passed">, MT)
  else
    if not (contains(bs, sender))
    then let bs1 = put(sbs, ender, value) in
         backers := bs1;
         send (<to -> sender,
                amount -> 0,
	        tag -> "main",
	        msg -> "ok">, MT)
    else send (<to -> sender,
                amount -> 0,
	        tag -> "main",
	        msg -> "already_donated">, MT)
 *)

Notation tft := (trans_fun_type crowdState).
Definition ok_msg := [:: (0, [:: 1])].
Definition no_msg := [:: (0, [:: 0])].

Definition donate_tag := 1.
Definition donate_fun : tft := fun id bal s m bc =>
  if method m == donate_tag then
    let bs := backers s in
    let nxt_block := block_num bc + 1 in
    let from := sender m in 
    if get_max_block s <= nxt_block
    then (s, Some (Msg 0 from 0 no_msg))
    else if all [pred e | e.1 != from] bs
         (* new backer *)        
         then let bs' := (from, val m) :: bs in
              let s'  := set_backers s bs' in
              (s', Some (Msg 0 from 0 ok_msg))
         else (s, Some (Msg 0 from 0 no_msg))
  else (s, None).

Definition donate := CTrans donate_tag donate_fun.

(* Transition 2: Sending the funds to the owner *)
(*
transition GetFunds
  (sender : address, value : uint, tag : string)
  (* Only the owner can get the money back *)
  if (tag == "getfunds") && (sender == owner) =>
  blk <- && block_number;
  bal <- & balance;
  if max_block >= blk
  then if goal <= bal
       then funded := true;   
            send (<to -> owner, amount -> bal,
                   tag -> "main", msg -> "funded">, MT)
       else send (<to -> owner, amount -> 0,
                   tag -> "main", msg -> "failed">, MT)
  else send (<to -> owner, amount -> 0, tag -> "main",
   	      msg -> "too_early_to_claim_funds">, MT)
 *)

Definition getfunds_tag := 2.
Definition getfunds_fun : tft := fun id bal s m bc =>
  let: from := sender m in 
  if (method m == getfunds_tag) && (from == (get_owner s)) then
    let blk := block_num bc + 1 in
    if (get_max_block s >= blk) 
    then if get_goal s <= bal
         then let s' := set_funded s true in
              (s', Some (Msg bal from 0 ok_msg))
         else (s, Some (Msg 0 from 0 no_msg))
    else (s, Some (Msg 0 from 0 no_msg))
  else (s, None).

Definition get_funds := CTrans getfunds_tag getfunds_fun.

(* Transition 3: Reclaim funds by a backer *)
(*
transition Claim
  (sender : address, value : uint, tag : string)
  if tag == "claim" =>
  blk <- && block_number;
  if blk <= max_block
  then send (<to -> sender, amount -> 0, tag -> "main",
              msg -> "too_early_to_reclaim">, MT)
  else bs <- & backers;
       bal <- & balance;
       if (not (contains(bs, sender))) || funded ||
          goal <= bal 
       then send (<to -> sender, amount -> 0,
                   tag -> "main",
	           msg -> "cannot_refund">, MT)
       else 
       let v = get(bs, sender) in
       backers := remove(bs, sender);
       send (<to -> sender, amount -> v, tag -> "main", 
              msg -> "here_is_your_money">, MT)
*)

Definition claim_tag := 3.
Definition claim_fun : tft := fun id bal s m bc =>
  let: from := sender m in
  if method m == claim_tag then
    let blk := block_num bc in
    if blk <= get_max_block s 
    then
      (* Too early! *)
      (s, Some (Msg 0 from 0 no_msg))
    else let bs := backers s in
         if [|| funded s | get_goal s <= bal]
         (* Cannot reimburse: campaign suceeded *)     
         then (s, Some (Msg 0 from 0 no_msg))
         else let n := seq.find [pred e | e.1 == from] bs in
              if n < size bs
              then let v := nth 0 (map snd bs) n in
                   let bs' := filter [pred e | e.1 != from] bs in
                   let s'  := set_backers s bs' in
                   (s', Some (Msg v from 0 no_msg))
              else
                (* Didn't back or already claimed *)
                (s, None)
  else (s, None).

Definition claim := CTrans claim_tag claim_fun.

(* Definition of the protocol *)
Variable crowd_addr : address.

Program Definition crowd_prot : Protocol crowdState :=
  @CProt _ crowd_addr 0 init_state [:: donate; get_funds; claim] _.

Lemma crowd_tags : tags crowd_prot = [:: 1; 2; 3].
Proof. by []. Qed.

(***********************************************************)
(**                  Safety properties                    **)
(***********************************************************)

(* The contract always has sufficient balance to reimburse everyone,
   unless it's successfully finished its campaign:  

   The "funded" flag is set only if the campaign goals were reached,
   then all money goes to owner. Otherwise, the contract keeps 
   all its money intact.

   Perhaps, we should make it stronger, adding a temporal property
   that one's reimbursement doesn't change.
*)
Definition balance_backed (st: cstate crowdState) : Prop :=
  (* If the campaign not funded... *)
  ~~ (funded (state st)) ->
  (* the contract has enough funds to reimburse everyone. *)
  sumn (map snd (backers (state st))) <= balance st.

Lemma sufficient_funds_safe : safe crowd_prot balance_backed.
Proof.
apply: safe_ind=>[|[id bal s]bc m M Hi]//. 
rewrite crowd_tags !inE in M.
(* Get the exact transitions and start struggling... *)
rewrite /= /apply_prot; case/orP: M; [|case/orP]=>/eqP M; rewrite M/=.

(* Donate transition *)
rewrite /donate_fun M eqxx.
case: ifP=>/=_; [move/Hi=>{Hi}Hi|].
- by rewrite subn0; apply: (leq_trans Hi (leq_addr (val m) bal)).
case: ifP=>/=_; move/Hi=>{Hi}Hi; last first.
- by rewrite subn0; apply: (leq_trans Hi (leq_addr (val m) bal)).
by rewrite subn0 /balance_backed/= in Hi *; rewrite addnC leq_add2r.

(* Get funds transition. *)
rewrite /getfunds_fun M eqxx.
case: ifP=>//=_; case:ifP=>//=_;[|move/Hi=>{Hi}Hi]; last first.
- by rewrite subn0; apply: (leq_trans Hi (leq_addr (val m) bal)).
case: ifP=>//=_; move/Hi=>{Hi}Hi.
by rewrite subn0; apply: (leq_trans Hi (leq_addr (val m) bal)).

(* Claim funds back *)
rewrite /claim_fun M eqxx.
case: ifP=>//=_; [move/Hi=>{Hi}Hi|].
- by rewrite subn0; apply: (leq_trans Hi (leq_addr (val m) bal)).
case: ifP=>//=X.
- case/orP: X; first by rewrite /balance_backed/==>->.
  by move=>_/Hi Z; rewrite subn0; apply: (leq_trans Z (leq_addr (val m) bal)).
case: ifP=>//=G/=; move/Hi=>/={Hi}Hi.
rewrite addnC.
have H1: nth 0 [seq i.2 | i <- backers s] (seq.find [pred e | e.1 == sender m] (backers s)) <=
         sumn [seq i.2 | i <- backers s].
- Search _ (sumn).
  (* sumn_cat *)
  by admit. (* Boring and trivial *)
move: (leq_trans H1 Hi)=> H2.  
rewrite -(addnBA _ H2); clear H2 H1.
suff H3: sumn [seq i.2 | i <- backers s & [pred e | e.1 != sender m] i] <=
         bal - nth 0 [seq i.2 | i <- backers s] (seq.find [pred e | e.1 == sender m] (backers s)).
-  by apply: (leq_trans H3 (leq_addl (val m) _ )).
(* Search _ (_ - _ <= _ - _). *)
admit.
(* super-boring manipulation with sums... *)   
   
Admitted.

End Crowdfunding.

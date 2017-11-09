From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Automata2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
   backers : union_map [ordType of address] value; 
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
Definition init_state := CS (init_owner, init_max_block, init_max_block) Unit false.

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
    else if from \notin dom bs
         then let bs' := bs \+ (from \\-> (val m)) in
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
Definition claim : tft := fun id bal s m bc =>
  let: from := sender m in
  if method m == claim_tag then
    let blk := block_num bc in
    if blk <= get_max_block s 
    then (s, Some (Msg 0 from 0 no_msg))
    else let bs := backers s in
         if [|| (from \notin dom bs), funded s | get_goal s <= bal]
         then (s, Some (Msg 0 from 0 no_msg))
         else match find from bs with
              | Some v =>
                let bs' := free from bs in
                let s'  := set_backers s bs' in
                (s', Some (Msg v from 0 no_msg))
              (* cannot happen *)
              | _ => (s, Some (Msg 0 from 0 no_msg))
              end
  else (s, None).

(* Variable crowd_addr : address. *)
(* Program Definition crowd_prot : Protocol crowsState := *)
(*   @CProt _ crowd_addr init_reward s0 [:: update_reward; try_solution] _. *)


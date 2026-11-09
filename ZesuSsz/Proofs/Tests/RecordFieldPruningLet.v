Require Import ZesuSsz.Automation2.All.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Local Open Scope Z_scope.

(* A goal that reaches a record field only through a local definition keeps
   the facts about that field after record-field pruning. Shape taken from a
   store-address range goal of decodeItem block 697c. *)
Lemma record_field_pruning_keeps_let_body_facts : forall (args : DecodeItemArgs)
    (Hbound : decodeItemOutputPointer args + 40 < 2^64) (Hother : True),
  let address := (Z_to_bv 64 (decodeItemOutputPointer args) + BV 64 8)%bv in
  bv_unsigned address + 8 <= 3221225472 \/ True.
Proof.
  intros.
  ContextCollection.zesu_context_prune_goal.
  match goal with
  | _ : decodeItemOutputPointer args + 40 < 2^64 |- _ => right; exact I
  end.
Qed.

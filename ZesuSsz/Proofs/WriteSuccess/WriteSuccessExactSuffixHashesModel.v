Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessRepresentation WriteSuccessOutputSemantic WriteSuccessExactStorageKeysModel.
From Coq Require Import Lists.List ZArith.ZArith.

Fixpoint writeSuccessExactSuffixHashesEvents (sp : bv 64)
    (processed count : nat) (source : list (bv 8)) (tail : spec) : spec :=
  match count with
  | O => tail
  | S remaining =>
      writeOutputEvents (sp + BV 64 1744)%bv (BV 64 32)
        (take 32 (drop (32 * processed) source))
        (writeSuccessExactSuffixHashesEvents sp (S processed) remaining source tail)
  end.

Lemma suffix_hashes_events_canonical sp processed count source tail :
  writeSuccessExactSuffixHashesEvents sp processed count source tail =
  writeOutputPayloadsSpec (repeat ((sp + BV 64 1744)%bv, BV 64 32) count)
    (map writeSuccessPrivateBytes (writeSuccessFixedChunks 32 count
      (drop (32 * processed) source))) tail.
Proof.
  revert processed. induction count as [|count IH]; intros processed; first reflexivity.
  rewrite writeSuccessFixedChunks_cons.
  cbn [List.map repeat writeOutputPayloadsSpec writeSuccessExactSuffixHashesEvents].
  unfold writeSuccessBytesAt. rewrite drop_0 writeSuccessPrivatePublicBytes.
  rewrite drop_drop.
  replace (32 * processed + 32)%nat with (32 * S processed)%nat by lia.
  rewrite IH. reflexivity.
Qed.
Print Assumptions suffix_hashes_events_canonical.


Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.OutputPayloads.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.

Lemma output_count_payload (sp count : bv 64) (items : list (bv 8))
    (tail : spec) :
  bv_unsigned count = Z.of_nat (length items) ->
  writeOutputEvents (sp - (BV 64 32 + BV 64 16))%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned count))) tail
  ⊆ writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64 (Z.of_nat (length items)))) tail.
Proof. intros Hcount. zesu_normalize_output_payload. reflexivity. Qed.
Print Assumptions output_count_payload.

Lemma output_frame_payload (sp : bv 64) (bytes : list (bv 8)) (tail : spec) :
  writeOutputEvents (sp - (BV 64 128 + BV 64 16))%bv (BV 64 8) bytes tail
  ⊆ writeOutputEvents (sp - BV 64 144)%bv (BV 64 8) bytes tail.
Proof. zesu_normalize_output_payload. reflexivity. Qed.
Print Assumptions output_frame_payload.

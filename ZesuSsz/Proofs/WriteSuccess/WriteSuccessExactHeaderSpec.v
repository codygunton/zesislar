Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.

Import ListNotations.

Definition writeSuccessHeaderPayload
    (offset width : nat) (bytes : list (bv 8)) : list (bv 8) :=
  take width (drop offset (take 592 bytes)).

Lemma writeSuccessHeaderPayload_length offset width bytes :
  length bytes = 720%nat ->
  (offset + width <= 592)%nat ->
  length (writeSuccessHeaderPayload offset width bytes) = width.
Proof.
  intros Hlength Hbounds. unfold writeSuccessHeaderPayload.
  rewrite length_take length_drop length_take Hlength. cbn. lia.
Qed.

Definition writeSuccessExactHeaderAfterCopySpec `{!islaG Sigma} `{!threadG}
    (offset width : nat) (sp : bv 64) (bytes : list (bv 8))
    (events tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessHeaderRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ (bv_unsigned sp + 104) ↦ₘ? 16 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ take offset (take 592 bytes) ∗
   (bv_unsigned sp + 1032 + Z.of_nat offset) ↦ₘ∗
     writeSuccessHeaderPayload offset width bytes ∗
   (bv_unsigned sp + 1032 + Z.of_nat (offset + width)) ↦ₘ∗
     drop (offset + width) (take 592 bytes) ∗
   (bv_unsigned sp + 1624) ↦ₘ? 272 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace events ∗
   ⌜(offset + width <= 592)%nat⌝ ∗
   ⌜length bytes = 720%nat⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗
   instr_pre 0x14e88 (writeSuccessHeaderPost sp bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessExactHeaderAfterCopySpec) := I.

Lemma writeSuccessExactHeaderAfterCopySpec_to_standard
    `{!islaG Sigma} `{!threadG}
    (offset width : nat) (sp : bv 64) (bytes : list (bv 8))
    (events tail : spec) (P : iProp Sigma) :
  writeSuccessExactHeaderAfterCopySpec offset width sp bytes events tail P -∗
  writeSuccessHeaderAfterCopySpec sp bytes events tail P.
Proof.
  iIntros "Hsplit".
  rewrite /writeSuccessExactHeaderAfterCopySpec
    /writeSuccessHeaderAfterCopySpec /writeSuccessHeaderPayload.
  iDestruct "Hsplit" as
    "(Hsys & Hregs & H2 & Hgap & Hbytes & Hprefix & Hmiddle & Hsuffix &
      Hstack & Hmmio & Htrace & %Hbounds & %Hlength & %Halign & %Hmin &
      %Hmax & HP & Hpost & _)".
  iPoseProof (mem_mapsto_array_app_combine_at 8%N
    (bv_unsigned sp + 1032) (DfracOwn 1)
    (take offset (take 592 bytes))
    (take width (drop offset (take 592 bytes))) offset with "Hprefix")
    as "Hleft".
  { have Htake : length (take 592 bytes) = 592%nat.
    { rewrite length_take Hlength. done. }
    rewrite length_take Htake. lia. }
  iEval (rewrite /= Z.mul_1_l) in "Hleft".
  iSpecialize ("Hleft" with "Hmiddle").
  iPoseProof (mem_mapsto_array_app_combine_at 8%N
    (bv_unsigned sp + 1032) (DfracOwn 1)
    (take offset (take 592 bytes) ++
      take width (drop offset (take 592 bytes)))
    (drop (offset + width) (take 592 bytes)) (offset + width)
    with "Hleft") as "Hcopy".
  { have Htake : length (take 592 bytes) = 592%nat.
    { rewrite length_take Hlength. done. }
    rewrite length_app !length_take !length_drop Htake. lia. }
  iEval (rewrite /= Z.mul_1_l) in "Hcopy".
  iSpecialize ("Hcopy" with "Hsuffix").
  iEval (rewrite take_take_drop take_drop) in "Hcopy".
  iFrame.
  repeat iSplit; iPureIntro; assumption.
Qed.

Definition writeSuccessExactHeaderPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessHeaderRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ (bv_unsigned sp + 104) ↦ₘ? 16 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ take 524 (take 592 bytes) ∗
   (bv_unsigned sp + 1556) ↦ₘ∗ writeSuccessHeaderPayload 524 32 bytes ∗
   (bv_unsigned sp + 1588) ↦ₘ∗ drop 556 (take 592 bytes) ∗
   (bv_unsigned sp + 1624) ↦ₘ? 272 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ ⌜length bytes = 720%nat⌝ ∗ P ∗ True)%I.

Lemma writeSuccessExactHeaderPost_to_standard
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  writeSuccessExactHeaderPost sp bytes tail P -∗
  writeSuccessHeaderPost sp bytes tail P.
Proof.
  iIntros "Hsplit".
  rewrite /writeSuccessExactHeaderPost /writeSuccessHeaderPost
    /writeSuccessHeaderPayload.
  iDestruct "Hsplit" as
    "(Hsys & Hregs & H2 & Hgap & Hbytes & Hprefix & Hmiddle & Hsuffix &
      Hstack & Hmmio & Htrace & %Hlength & HP & _)".
  iPoseProof (mem_mapsto_array_app_combine_at 8%N
    (bv_unsigned sp + 1032) (DfracOwn 1) (take 524 (take 592 bytes))
    (take 32 (drop 524 (take 592 bytes))) 524 with "Hprefix") as "Hleft".
  { rewrite length_take length_take Hlength. done. }
  iEval (rewrite /= Z.mul_1_l) in "Hleft".
  iEval (replace (bv_unsigned sp + 1556)%Z with
    (bv_unsigned sp + 1032 + 524)%Z by lia) in "Hmiddle".
  iSpecialize ("Hleft" with "Hmiddle").
  iPoseProof (mem_mapsto_array_app_combine_at 8%N
    (bv_unsigned sp + 1032) (DfracOwn 1)
    (take 524 (take 592 bytes) ++ take 32 (drop 524 (take 592 bytes)))
    (drop 556 (take 592 bytes)) 556 with "Hleft") as "Hcopy".
  { have Htake : length (take 592 bytes) = 592%nat.
    { rewrite length_take Hlength. done. }
    rewrite length_app !length_take !length_drop Htake. cbn. lia. }
  iEval (rewrite /= Z.mul_1_l) in "Hcopy".
  iEval (replace (bv_unsigned sp + 1588)%Z with
    (bv_unsigned sp + 1032 + 556)%Z by lia) in "Hsuffix".
  iSpecialize ("Hcopy" with "Hsuffix").
  iEval (rewrite take_take_drop take_drop) in "Hcopy".
  iFrame.
Qed.

Definition writeSuccessExactHeaderEventsAfter1300
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) : spec :=
  writeOutputEvents (sp + 1556)%bv (BV 64 32)
    (writeSuccessHeaderPayload 524 32 bytes) tail.

Definition writeSuccessExactHeaderFinalSpec `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessHeaderRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ (bv_unsigned sp + 104) ↦ₘ? 16 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes ∗
   (bv_unsigned sp + 1624) ↦ₘ? 272 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactHeaderEventsAfter1300 sp bytes tail) ∗
   ⌜length bytes = 720%nat⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗
   instr_pre 0x14e88 (writeSuccessExactHeaderPost sp bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessExactHeaderFinalSpec) := I.

Lemma writeSuccessHeaderAfterCopy_to_exact_final
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  writeSuccessHeaderAfterCopySpec sp bytes
    (writeSuccessExactHeaderEventsAfter1300 sp bytes tail) tail P -∗
  writeSuccessExactHeaderFinalSpec sp bytes tail P.
Proof.
  iIntros "Hstandard".
  rewrite /writeSuccessHeaderAfterCopySpec /writeSuccessExactHeaderFinalSpec.
  iDestruct "Hstandard" as
    "(Hsys & Hregs & H2 & Hgap & Hbytes & Hcopy & Hstack & Hmmio & Htrace &
      %Hlength & %Halign & %Hmin & %Hmax & HP & Hpost & _)".
  iAssert (instr_pre 0x14e88
      (writeSuccessExactHeaderPost sp bytes tail P))%I with "[Hpost]"
    as "HexactPost".
  { iApply (instr_pre_wand 0x14e88 0x14e88 true true with "Hpost");
      [done | done |].
    iIntros "Hsplit".
    iApply (writeSuccessExactHeaderPost_to_standard with "Hsplit"). }
  iFrame.
  repeat iSplit; iPureIntro; assumption.
Qed.

Definition writeSuccessExactHeaderEventsAfter1268
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) : spec :=
  writeOutputEvents (sp + 1300)%bv (BV 64 256)
    (writeSuccessHeaderPayload 268 256 bytes)
    (writeSuccessExactHeaderEventsAfter1300 sp bytes tail).

Definition writeSuccessExactHeaderEventsAfter1236
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) : spec :=
  writeOutputEvents (sp + 1268)%bv (BV 64 32)
    (writeSuccessHeaderPayload 236 32 bytes)
    (writeSuccessExactHeaderEventsAfter1268 sp bytes tail).

Definition writeSuccessExactHeaderEventsAfter1216
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) : spec :=
  writeOutputEvents (sp + 1236)%bv (BV 64 32)
    (writeSuccessHeaderPayload 204 32 bytes)
    (writeSuccessExactHeaderEventsAfter1236 sp bytes tail).

Definition writeSuccessExactHeaderEventsAfter1184
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) : spec :=
  writeOutputEvents (sp + 1216)%bv (BV 64 20)
    (writeSuccessHeaderPayload 184 20 bytes)
    (writeSuccessExactHeaderEventsAfter1216 sp bytes tail).

Definition writeSuccessExactHeaderEventsAfterTag
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) : spec :=
  writeOutputEvents (sp + 1184)%bv (BV 64 32)
    (writeSuccessHeaderPayload 152 32 bytes)
    (writeSuccessExactHeaderEventsAfter1184 sp bytes tail).

Definition writeSuccessExactHeaderEvents
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) : spec :=
  writeOutputEvents (BV 64 0x179c5) (BV 64 6)
    (writeSuccessPrivateBytes [90; 83; 83; 90; 1; 1])
    (writeSuccessExactHeaderEventsAfterTag sp bytes tail).

Definition writeSuccessExactHeaderSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (bytes : list (bv 8)) (tail : spec),
    writeSuccessHeaderBeforeCopySpec sp bytes
      (writeSuccessExactHeaderEvents sp bytes tail) tail
      (bv_unsigned (BV 64 0x179c5) ↦ₘ∗
        writeSuccessPrivateBytes [90; 83; 83; 90; 1; 1] ∗ P))%I.

Global Instance : LithiumUnfold (@writeSuccessExactHeaderSpec) := I.

Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsMaxBlobFee WriteSuccessExactTransactionsMaxBlobFeeCount
  WriteSuccessExactAuthorizationsCount WriteSuccessExactEncoderU128
  WriteSuccessObservation WriteSuccessOutputSemantic.

Definition authorizationPrefixEntry `{!islaG Sigma} `{!threadG}
    (sp low high count oldra old5 : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)] ∗
   reg_col [(KindReg "x18", BitsShape 64)] ∗
   (bv_unsigned sp + 144) ↦ₘ high ∗ (bv_unsigned sp + 152) ↦ₘ low ∗
   (bv_unsigned sp + 160) ↦ₘ count ∗ (bv_unsigned sp - 32) ↦ₘ? 32 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
     (writeSuccessU128WordsPayload low high)
     (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
       (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned count))) tail)) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗
   ⌜bv_unsigned sp + 176 < (machineRamEnd defaultMap)⌝ ∗ P ∗
   instr_pre 0x15584 (authorizationCountPost sp count tail (maxBlobFeeCountFrame sp low high P)) ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationPrefixEntry) := I.

Lemma authorization_prefix_correct `{!islaG Sigma} `{!threadG}
    sp low high count oldra old5 tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_72.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_73.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15564 (authorizationPrefixEntry sp low high count oldra old5 tail P).
Proof.
  iStartProof. iIntros "#H72 #H73 #Hu128 #Hint #Houtput".
  iEval (rewrite instr_pre'_eq). iIntros "Hentry".
  iDestruct "Hentry" as "(Hsys & Hsp & H1 & H5 & Hwords & H18 & Hhighword & Hlowword & Hcountword & Hscratch & Hmmio & Htrace & %Halign & %Hlow & %Hhigh & HP & Hfinal & _)".
  iPoseProof (authorization_count_correct sp count (BV 64 0x15574) (BV 64 (mapIoContextAddress defaultMap))
    (BV 64 16) tail (maxBlobFeeCountFrame sp low high P) with "H73 Hint Houtput") as "Hcount".
  iAssert (instr_pre 0x15574 (maxBlobFeePost sp low high
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned count))) tail)
    (reg_col [(KindReg "x18", BitsShape 64)] ∗ (bv_unsigned sp + 160) ↦ₘ count ∗
     ⌜bv_unsigned sp + 176 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I)) with "[Hfinal]" as "Hnext".
  { iApply (instr_pre_wand 0x15574 0x15574 false true with "Hcount"); [done | done |].
    iIntros "Hpost". iApply max_blob_fee_to_count. iFrame "Hpost Hfinal". }
  iPoseProof (max_blob_fee_correct sp low high oldra old5
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned count))) tail)
    (reg_col [(KindReg "x18", BitsShape 64)] ∗ (bv_unsigned sp + 160) ↦ₘ count ∗
     ⌜bv_unsigned sp + 176 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I with "H72 Hu128 Houtput") as "Hfee".
  iEval (rewrite instr_pre'_eq) in "Hfee". iApply "Hfee".
  unfold maxBlobFeeEntry. iFrame "Hsys Hsp H1 H5 Hwords Hhighword Hlowword Hscratch Hmmio Htrace Hnext".
  iSplit; first done. iSplit; first done. iSplit; first (iPureIntro; lia).
  iFrame. done.
Qed.
Print Assumptions authorization_prefix_correct.

Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsInt WriteSuccessExactWithdrawalsSecondInt WriteSuccessExactWithdrawalsThirdInt
  WriteSuccessExactWithdrawalsIntNext WriteSuccessExactWithdrawalsAddressEntry
  WriteSuccessExactWithdrawalsOutputWhole WriteSuccessExactWithdrawalsPhases.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactWithdrawalsSecondIntSuffix.
Definition withdrawalFieldsEntry `{!islaG Sigma} `{!threadG}
    (sp oldra old5 old11 : bv 64) (bytes : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x11" ↦ᵣ RVal_Bits old11 ∗ reg_col [(KindReg "x10", BitsShape 64)] ∗
   (bv_unsigned sp + 1744) ↦ₘ∗ bytes ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace (withdrawalExactPhaseEvents 0 sp bytes tail) ∗
   ⌜length bytes = 48%nat⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= bv_unsigned sp - 48)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z⌝ ∗
   "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalFieldsEntry) := I.
Definition withdrawalFieldsPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  withdrawalIntPost sp bytes (BV 64 0x156dc) tail ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalFieldsPost) := I.

Lemma withdrawal_fields_correct `{!islaG Sigma} `{!threadG}
    sp oldra old5 old11 bytes tail (P : iProp Sigma) :
  length bytes = 48%nat ->
  ([∗ list] instruction ∈ IslaTraces.write_success_91.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_92.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_93.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_94.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x156dc (withdrawalFieldsPost sp bytes tail P) -∗
  instr_body 0x156a8 (withdrawalFieldsEntry sp oldra old5 old11 bytes tail P).
Proof.
  intros Hlen. iStartProof. iIntros "#Hfirst #Hsecond #Haddress #Hamount #Hint #Houtput Hfinal".
  iPoseProof (withdrawal_second_int_suffix_correct sp bytes tail P Hlen
    with "Hsecond Haddress Hamount Hint Houtput Hfinal") as "Hlast".
  iAssert (instr_pre 0x156b4 (withdrawalIntPost sp bytes (BV 64 0x156b4)
    (withdrawalExactPhaseEvents 1 sp bytes tail) ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I)) with "[Hlast]" as "Hnext".
  { iApply (instr_pre_wand 0x156b4 0x156b4 false true with "Hlast"); [done | done |]. iIntros "$". }
  iPoseProof (withdrawal_first_int_correct sp oldra old5 old11 bytes
    (withdrawalExactPhaseEvents 1 sp bytes tail) ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I
    with "Hfirst Hint Houtput") as "Hcallee".
  iApply (instr_pre_wand 0x156a8 0x156a8 false false with "Hcallee"); [done | done |].
  iIntros "Hentry". iEval (rewrite /withdrawalFieldsEntry) in "Hentry".
  iDestruct "Hentry" as "(Hsys & Hsp & H1 & H5 & H11 & H10 & Hbytes & Hscratch &
    Hmmio & Htrace & %Hsize & %Halign & %Hlow & %Hhigh & H18 & HP & _)".
  iEval (rewrite (withdrawal_phase_0 sp bytes tail Hlen)) in "Htrace".
  rewrite /withdrawalIntEntry. iFrame. repeat iSplit; done.
Qed.
Print Assumptions withdrawal_fields_correct.

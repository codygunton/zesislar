Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.

#[local] Hint Rewrite (@bv_sign_extend_idemp 64) :
  lithium_rewrite isla_coq_rewrite.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Definition zesuEncoderBytesCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (data size sp old_s0 old_s1 : bv 64) (ret : Z)
      (bytes : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 ret) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝ ∗
    "x6" ↦ᵣ: fun r6 => ⌜valu_has_shape r6 (BitsShape 64)⌝ ∗
    "x8" ↦ᵣ RVal_Bits old_s0 ∗ "x9" ↦ᵣ RVal_Bits old_s1 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEventsAny data size tail)) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜0 <= ret < 2 ^ 64⌝ ∗
    ⌜bv_extract 0 1 (Z_to_bv 64 ret) = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 (Z_to_bv 64 ret) = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 (Z_to_bv 64 ret) = BV 2 0⌝ ∗
    instr_pre ret
      (reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 ret) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
       ("x6" ↦ᵣ: fun r6 => ⌜valu_has_shape r6 (BitsShape 64)⌝) ∗
       "x8" ↦ᵣ RVal_Bits old_s0 ∗ "x9" ↦ᵣ RVal_Bits old_s1 ∗
       "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
       (bv_unsigned sp - 48) ↦ₘ? 48 ∗
       bv_unsigned data ↦ₘ∗ bytes ∗
       mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@zesuEncoderBytesCallSpec) := I.

Lemma zesu_encoder_bytes_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c6c zesuEncoderBytesCallSpec.
Proof.
  iStartProof. iIntros "#H06 #H07 #H01".
  rewrite instr_pre'_eq. iIntros "Hspec".
  iDestruct "Hspec" as
    (data size sp old_s0 old_s1 ret bytes tail)
    "(Hsys & H1 & H2 & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r5) "(H5 & %Hr5 & Hrest)".
  apply valu_has_bits_shape in Hr5 as (old_x5 & ->).
  iDestruct "Hrest" as (r6) "(H6 & %Hr6 & Hrest)".
  apply valu_has_bits_shape in Hr6 as (old_x6 & ->).
  iDestruct "Hrest" as
    "(H8 & H9 & H10 & H11 & Hstack & Hdata & %Hlen & Hmmio & Htrace &
      %Halign & %Hspmin & %Hspmax & %HretRange &
      %Hret0 & %Hret1 & %Hret2 & Hret & _)".
  iDestruct (mem_mapsto_uninit_split 8 with "Hstack") as
    "[Hstack0 Hstack]"; [lia|].
  have Haddr0 : bv_unsigned sp - 48 + 8 = bv_unsigned sp - 40 by lia.
  iEval (rewrite Haddr0) in "Hstack".
  iDestruct (mem_mapsto_uninit_split 8 with "Hstack") as
    "[Hstack1 Hstack]"; [lia|].
  have Haddr1 : bv_unsigned sp - 40 + 8 = bv_unsigned sp - 32 by lia.
  iEval (rewrite Haddr1) in "Hstack".
  iDestruct (mem_mapsto_uninit_split 8 with "Hstack") as
    "[Hstack2 Hstack]"; [lia|].
  have Haddr2 : bv_unsigned sp - 32 + 8 = bv_unsigned sp - 24 by lia.
  iEval (rewrite Haddr2) in "Hstack".
  iDestruct (mem_mapsto_uninit_split 8 with "Hstack") as
    "[Hstack3 Hstack]"; [lia|].
  have Haddr3 : bv_unsigned sp - 24 + 8 = bv_unsigned sp - 16 by lia.
  iEval (rewrite Haddr3) in "Hstack".
  iDestruct (mem_mapsto_uninit_split 8 with "Hstack") as
    "[Hstack4 Hstack5]"; [lia|].
  have Haddr4 : bv_unsigned sp - 16 + 8 = bv_unsigned sp - 8 by lia.
  iEval (rewrite Haddr4) in "Hstack5".
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hstack0") as
    (n0 stack0 Hn0) "Hstack0".
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hstack1") as
    (n1 stack1 Hn1) "Hstack1".
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hstack2") as
    (n2 stack2 Hn2) "Hstack2".
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hstack3") as
    (n3 stack3 Hn3) "Hstack3".
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hstack4") as
    (n4 stack4 Hn4) "Hstack4".
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hstack5") as
    (n5 stack5 Hn5) "Hstack5".
  cbn in Hn0, Hn1, Hn2, Hn3, Hn4, Hn5.
  subst n0 n1 n2 n3 n4 n5.
  iPoseProof (encoder_bytes_correct data size sp (Z_to_bv 64 ret)
    bytes tail True%I with "H06 H07 H01") as "Hbody".
  rewrite instr_pre'_eq. iApply "Hbody".
  iExists old_x5, old_x6, old_s0, old_s1,
    stack0, stack1, stack2, stack3, stack4, stack5.
  iFrame "Hsys H1 H2 H5 H6 H8 H9 H10 H11 Hstack0 Hstack1 Hstack2
    Hstack3 Hstack4 Hstack5 Hdata Hmmio Htrace".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  rewrite instr_pre'_eq. iNext. iIntros "Hpost".
  iDestruct "Hpost" as (final_x6)
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 &
      Hstack0 & Hstack1 & Hstack2 & Hstack3 & Hstack4 & Hstack5 &
      Hdata & Hmmio & Htrace & _ & _)".
  have HretUnsigned : bv_unsigned (Z_to_bv 64 ret) = ret by bv_solve.
  rewrite HretUnsigned.
  iApply ("Hret" with "[-]").
  iFrame "Hsys H1 H2 H5 H8 H9 H10 H11 Hdata Hmmio Htrace".
  iSplitL "H6".
  { iExists (RVal_Bits final_x6). iFrame.
    iPureIntro. done. }
  iApply (mem_mapsto_uninit_combine 8 with
    "[Hstack0] [Hstack1 Hstack2 Hstack3 Hstack4 Hstack5]"); [lia| |].
  { iApply (mem_mapsto_mapsto_to_uninit with "Hstack0"). }
  rewrite Haddr0.
  iApply (mem_mapsto_uninit_combine 8 with
    "[Hstack1] [Hstack2 Hstack3 Hstack4 Hstack5]"); [lia| |].
  { iApply (mem_mapsto_mapsto_to_uninit with "Hstack1"). }
  rewrite Haddr1.
  iApply (mem_mapsto_uninit_combine 8 with
    "[Hstack2] [Hstack3 Hstack4 Hstack5]"); [lia| |].
  { iApply (mem_mapsto_mapsto_to_uninit with "Hstack2"). }
  rewrite Haddr2.
  iApply (mem_mapsto_uninit_combine 8 with
    "[Hstack3] [Hstack4 Hstack5]"); [lia| |].
  { iApply (mem_mapsto_mapsto_to_uninit with "Hstack3"). }
  rewrite Haddr3.
  iApply (mem_mapsto_uninit_combine 8 with
    "[Hstack4] [Hstack5]"); [lia| |].
  { iApply (mem_mapsto_mapsto_to_uninit with "Hstack4"). }
  rewrite Haddr4.
  iApply (mem_mapsto_mapsto_to_uninit with "Hstack5").
Qed.

Lemma zesu_encoder_bytes_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec.
Proof.
  iStartProof. iIntros "#HbytesCode #HintCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_bytes_call_correct; iAssumption.
Qed.

Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_06 Require Import instrs.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.

Definition encoderBytesContract `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_call 48 (fun args sp RET => ∃ (bytes : list (bv 8)) (tail : spec),
    bv_unsigned (args !!! 0%nat) ↦ₘ∗ bytes ∗
    ⌜bv_unsigned (args !!! 1%nat) = length bytes⌝ ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned (args !!! 1%nat))))
      (writeOutputEvents (args !!! 0%nat) (args !!! 1%nat) bytes tail)) ∗
    RET (fun _ => bv_unsigned (args !!! 0%nat) ↦ₘ∗ bytes ∗
      mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True)))%I.
#[local] Instance : LithiumUnfold (@encoderBytesContract) := I.
#[local] Typeclasses Opaque encoderBytesContract.

Lemma encoder_bytes_contract_stack `{!islaG Sigma} (sp ret s0 s1 stack2 size : bv 64)
    (Haddress : bv_unsigned (sp - BV 64 48)%bv = bv_unsigned sp - 48) :
  bv_unsigned (sp - BV 64 48)%bv ↦ₘ∗
    writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)) ∗
  (bv_unsigned sp - 40) ↦ₘ (BV 64 0x15c90) ∗
  (bv_unsigned sp - 32) ↦ₘ stack2 ∗ (bv_unsigned sp - 24) ↦ₘ s1 ∗
  (bv_unsigned sp - 16) ↦ₘ s0 ∗ (bv_unsigned sp - 8) ↦ₘ ret -∗
  (bv_unsigned sp - 48) ↦ₘ? 48.
Proof.
  iIntros "(H0 & H1 & H2 & H3 & H4 & H5)".
  iDestruct (mem_mapsto_byte_array_to_mapsto_len 8 with "H0") as "H0".
  { reflexivity. }
  iDestruct (mem_mapsto_mapsto_to_uninit with "H0") as "H0".
  iEval (rewrite Haddress /=) in "H0".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H1") as "H1".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H2") as "H2".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H3") as "H3".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H4") as "H4".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H5") as "H5".
  iEval (replace (bv_unsigned sp - 8) with (bv_unsigned sp - 16 + 8) by lia) in "H5".
  iDestruct (mem_mapsto_uninit_combine 8 _ _ 16 with "H4 H5") as "H4"; [lia|].
  iEval (replace (bv_unsigned sp - 16) with (bv_unsigned sp - 24 + 8) by lia) in "H4".
  iDestruct (mem_mapsto_uninit_combine 8 _ _ 24 with "H3 H4") as "H3"; [lia|].
  iEval (replace (bv_unsigned sp - 24) with (bv_unsigned sp - 32 + 8) by lia) in "H3".
  iDestruct (mem_mapsto_uninit_combine 8 _ _ 32 with "H2 H3") as "H2"; [lia|].
  iEval (replace (bv_unsigned sp - 32) with (bv_unsigned sp - 40 + 8) by lia) in "H2".
  iDestruct (mem_mapsto_uninit_combine 8 _ _ 40 with "H1 H2") as "H1"; [lia|].
  iEval (replace (bv_unsigned sp - 40) with (bv_unsigned sp - 48 + 8) by lia) in "H1".
  iApply (mem_mapsto_uninit_combine 8 _ _ 48 with "H0 H1"). lia.
Qed.

Definition encoderBytesContractFrame `{!islaG Sigma} `{!threadG} (regs : list valu) : iProp Sigma :=
  (reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x7"; "x28"; "x29"; "x30"; "x31"]) ∗
   reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
     ["x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27"] regs) ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
     ["x12"; "x13"; "x14"; "x15"; "x16"; "x17"]))%I.
#[local] Instance : LithiumUnfold (@encoderBytesContractFrame) := I.
#[local] Typeclasses Opaque encoderBytesContractFrame.

Lemma encoder_bytes_contract_return `{!islaG Sigma} `{!threadG}
    (data size sp ret x6 s0 s1 stack2 : bv 64) (bytes : list (bv 8))
    (tail : spec) (regs : list valu)
    (Haddress : bv_unsigned (sp - BV 64 48)%bv = bv_unsigned sp - 48) :
  encoderBytesExactPost data size sp ret bytes x6 s0 s1 stack2 tail
    (encoderBytesContractFrame regs) -∗
  zesu_call_ret 48 ([RVal_Bits s0; RVal_Bits s1] ++ regs) ret sp
    (fun _ => bv_unsigned data ↦ₘ∗ bytes ∗
      mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True).
Proof.
  iEval (unfold encoderBytesExactPost, encoderBytesExactOutputResources, encoderBytesContractFrame).
  iIntros "(Hsys & H1 & H5 & H10 & H11 & Hbytes & Hmmio & Htrace & (H6 & H2 & H8 & H9 & Hstack & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Htemps & Hsaved & Hargs) & _)".
  iPoseProof (encoder_bytes_contract_stack sp ret s0 s1 stack2 size Haddress
    with "[$Hstack $Hs1 $Hs2 $Hs3 $Hs4 $Hs5]") as "Hstack".
  iEval (unfold zesu_call_ret). iFrame "Hsys".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H6".
  iDestruct "H6" as (r6) "[H6 %Hr6]".
  rewrite /tmp_registers /= !reg_col_cons reg_col_nil.
  iDestruct "Htemps" as "(H7 & H28 & H29 & H30 & H31 & _)".
  iDestruct "Hargs" as "(H12 & H13 & H14 & H15 & H16 & H17 & _)".
  iFrame "H7 H28 H29 H30 H31 H12 H13 H14 H15 H16 H17 Hsaved".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "H1 H5 H6 H8 H9".
  repeat iSplit; try (iPureIntro; done).
  iExists (RVal_Bits data). iFrame "H10". iExists data. iSplit; [done|].
  iExists (RVal_Bits size). iFrame "H11". iExists size. iFrame. done.
Qed.

Lemma encoder_bytes_contract_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c6c encoderBytesContract.
Proof.
  iIntros "HbytesCode HintCode HoutputCode". rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (unfold encoderBytesContract) in "Hentry". zesu_unpack_call "Hentry".
  subst r10 r11 r12 r13 r14 r15 r16 r17.
  iDestruct "Hrest" as (bytes tail) "(Hbytes & %Hsize & Hmmio & Htrace & Hreturn)".
  apply valu_has_bits_shape in Hr8. destruct Hr8 as [s0 ->].
  apply valu_has_bits_shape in Hr9. destruct Hr9 as [s1 ->].
  iEval (rewrite /tmp_registers /= !reg_col_cons reg_col_nil) in "Htmp".
  iDestruct "Htmp" as "(H5 & H6 & H7 & H28 & H29 & H30 & H31 & _)".
  iDestruct "H5" as (v5 Hv5) "H5". apply valu_has_bits_shape in Hv5. destruct Hv5 as [x5 ->].
  iDestruct "H6" as (v6 Hv6) "H6". apply valu_has_bits_shape in Hv6. destruct Hv6 as [x6 ->].
  set (regs := [r18; r19; r20; r21; r22; r23; r24; r25; r26; r27]).
  iAssert (encoderBytesContractFrame regs) with
    "[H7 H28 H29 H30 H31 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R12 R13 R14 R15 R16 R17]" as "HF".
  { iEval (unfold encoderBytesContractFrame). rewrite /regs /=.
    rewrite !reg_col_cons reg_col_nil.
    iFrame. repeat iSplit; iPureIntro; done. }
  iDestruct (encoder_bytes_uninit_48_to_words sp with "Hstack") as
    (w0 w1 w2 w3 w4 w5) "(Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5)".
  iPoseProof (encoder_bytes_exact_correct b10 b11 sp ret bytes tail
    (encoderBytesContractFrame regs) with "HbytesCode HintCode HoutputCode") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody". iApply "Hbody".
  iEval (unfold encoderBytesExactSpec). iExists x5, x6, s0, s1, w0, w1, w2, w3, w4, w5.
  iFrame "Hsys R1 R2 H5 H6 R8 R9 R10 R11 Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hbytes Hmmio Htrace HF".
  repeat iSplit; try (iPureIntro; assumption).
  all: try (iPureIntro; bv_solve).
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hreturn"); [done | done |].
  iApply encoder_bytes_contract_return. bv_solve.
Qed.

Print Assumptions encoder_bytes_contract_correct.

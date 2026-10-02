Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256Spec.


Definition encoderU256Contract `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_call 48 (fun args sp RET => ∃ tail : spec,
     mmio_range (machineOutputAddress defaultMap) 16 ∗
     spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
       (writeSuccessU256WordsPayload (args !!! 0%nat) (args !!! 1%nat) (args !!! 2%nat) (args !!! 3%nat)) tail) ∗
     RET (fun _ => mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True)))%I.
#[local] Instance : LithiumUnfold (@encoderU256Contract) := I.
#[local] Typeclasses Opaque encoderU256Contract.

Lemma encoder_u256_exact_return_to_call_ret `{!islaG Sigma} `{!threadG}
    (w0 w1 w2 w3 sp ret : bv 64) (tail : spec) (regs : list valu) (F : iProp Sigma)
    (Hsp : 48 <= bv_unsigned sp) :
  (F ⊣⊢ reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tl tmp_registers) ∗
    reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
      ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
       "x22"; "x23"; "x24"; "x25"; "x26"; "x27"] regs) ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      ["x14"; "x15"; "x16"; "x17"]))%I ->
  encoderU256ExactPost w0 w1 w2 w3 sp ret tail F -∗
  zesu_call_ret 48 regs ret sp (fun _ =>
    mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True).
Proof.
  intros Hframe. iEval (unfold encoderU256ExactPost).
  iIntros "(Hsys & H1 & H2 & H5 & H10 & H11 & H12 & H13 & Hpayload & Hlow & Hra & Hmmio & Htrace & HF & _)".
  iEval (rewrite Hframe) in "HF".
  have Haddr : bv_unsigned (sp - BV 64 48)%bv = bv_unsigned sp - 48 by bv_solve.
  iEval (rewrite Haddr) in "Hpayload".
  iDestruct (mem_mapsto_byte_array_to_mapsto_len 32 with "Hpayload") as "Hword".
  { reflexivity. }
  iDestruct (mem_mapsto_mapsto_to_uninit with "Hword") as "Hhead".
  iDestruct (mem_mapsto_mapsto_to_uninit with "Hra") as "Hra".
  iEval (rewrite /=) in "Hhead".
  have Hraaddr : bv_unsigned sp - 8 = bv_unsigned sp - 16 + 8 by lia.
  iEval (rewrite Hraaddr) in "Hra".
  iDestruct (mem_mapsto_uninit_combine 8 _ _ 16 with "Hlow Hra") as "Htail"; first lia.
  have Htailaddr : bv_unsigned sp - 16 = bv_unsigned sp - 48 + 32 by lia.
  iEval (rewrite Htailaddr) in "Htail".
  iDestruct (mem_mapsto_uninit_combine 32 _ _ 48 with "Hhead Htail") as "Hstack"; first lia.
  iDestruct "HF" as "(Htemps & Hsaved & Hargs)".
  iEval (unfold zesu_call_ret). iFrame "Hsys Hsaved".
  iEval (rewrite /tmp_registers /= !reg_col_cons reg_col_nil) in "Htemps".
  iDestruct "Htemps" as "(H6 & H7 & H28 & H29 & H30 & H31 & _)".
  iEval (rewrite /= !reg_col_cons reg_col_nil) in "Hargs".
  iDestruct "Hargs" as "(H14 & H15 & H16 & H17 & _)".
  rewrite /tmp_registers /= !reg_col_cons reg_col_nil.
  iFrame "H6 H7 H28 H29 H30 H31 H12 H13 H14 H15 H16 H17".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "H1 H2 H5 H10 H11 Hstack Hmmio Htrace".
  iSplit. { repeat iSplit; iPureIntro; done. }
  iExists (sp - BV 64 48)%bv. iSplit; [done |].
  iExists (BV 64 32). done.
Qed.

Lemma encoder_u256_contract_from_exact `{!islaG Sigma} `{!threadG} :
  (∀ w0 w1 w2 w3 sp ret tail P, instr_body 0x15cb0 (encoderU256ExactSpec w0 w1 w2 w3 sp ret tail P)) -∗
  instr_body 0x15cb0 encoderU256Contract.
Proof.
  iIntros "Hbody". rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (unfold encoderU256Contract) in "Hentry".
  zesu_unpack_call "Hentry". subst r10 r11 r12 r13 r14 r15 r16 r17.
  iDestruct "Hrest" as (tail) "(Hmmio & Htrace & Hreturn)".
  iEval (rewrite /tmp_registers /= reg_col_cons) in "Htmp".
  iDestruct "Htmp" as "[H5 Htemps]".
  iDestruct "H5" as (old5) "[%Hshape5 H5]".
  apply valu_has_bits_shape in Hshape5. destruct Hshape5 as [b5 ->].
  set (regs := [r8; r9; r18; r19; r20; r21; r22; r23; r24; r25; r26; r27]).
  set (F := (reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tl tmp_registers) ∗
    reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
      ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
       "x22"; "x23"; "x24"; "x25"; "x26"; "x27"] regs) ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      ["x14"; "x15"; "x16"; "x17"]))%I).
  iAssert F with "[Htemps R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R14 R15 R16 R17]" as "HF".
  { rewrite /F. iFrame "Htemps".
    rewrite /regs /= !reg_col_cons reg_col_nil. iFrame.
    repeat iSplit; iPureIntro; done. }
  iEval (rewrite -instr_pre'_eq) in "Hbody".
  iSpecialize ("Hbody" $! b10 b11 b12 b13 sp ret tail F).
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody". iEval (unfold encoderU256ExactSpec).
  iExists b5. iFrame "Hsys H5 R10 R11 R12 R13 R1 R2 Hstack Hmmio Htrace HF".
  repeat iSplit; try (iPureIntro; tauto); try (iPureIntro; bv_simplify_arith Hspalign; bv_solve).
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hreturn"); [done | done |].
  iApply encoder_u256_exact_return_to_call_ret.
  - unfold mapRamBase, defaultMap in Hstackbounds. simpl in Hstackbounds. lia.
  - by rewrite /F.

Qed.

Lemma encoder_u256_contract_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15cb0 encoderU256Contract.
Proof.
  iIntros "HencoderCode HoutputCode".
  iApply encoder_u256_contract_from_exact.
  iIntros (w0 w1 w2 w3 sp ret tail P).
  iApply (encoder_u256_exact_correct with "HencoderCode HoutputCode").
Qed.

Print Assumptions encoder_u256_contract_correct.

From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import a15cc8 a15ccc a15cd0 a15cd4.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256Spec.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma zesu_encoder_u256_write_output_entry_to_call
    `{!islaG Sigma} `{!threadG} :
  zesuEncoderU256WriteOutputEntrySpec -∗ zesuWriteOutputCallSpec.
Proof.
  iStartProof.
  iIntros "Hentry".
  iDestruct "Hentry" as
    (sp ret saved tail)
    "(Hsys & Htemps & Hsaved & H1 & H2 & H10 & H11 & Hframe &
      HsavedRet & %HsavedLen & %HsavedShapes & %HspAlign & %Hmin & %Hmax &
      %Hret0 & %Hret1 & %Hret2 & Hmmio & Htrace & Hcaller & Hnext & _)".
  destruct saved as [|s0 saved]; [cbn in HsavedLen; lia |].
  destruct saved as [|s1 saved]; [cbn in HsavedLen; lia |].
  destruct saved as [|s2 saved]; [cbn in HsavedLen; lia |].
  destruct saved as [|s3 saved]; [cbn in HsavedLen; lia |].
  destruct saved as [|s4 saved]; [cbn in HsavedLen; lia |].
  destruct saved as [|s5 saved]; [cbn in HsavedLen; lia |].
  destruct saved as [|s6 saved]; [cbn in HsavedLen; lia |].
  destruct saved as [|s7 saved]; [cbn in HsavedLen; lia |].
  destruct saved as [|s8 saved]; [cbn in HsavedLen; lia |].
  destruct saved as [|s9 saved]; [cbn in HsavedLen; lia |].
  destruct saved as [|s10 saved]; [cbn in HsavedLen; lia |].
  destruct saved as [|s11 saved]; [cbn in HsavedLen; lia |].
  destruct saved as [|extra saved]; [|cbn in HsavedLen; lia].
  repeat rewrite Forall_cons_iff in HsavedShapes.
  destruct HsavedShapes as
    (Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 &
     Hs10 & Hs11 & _).
  iEval (cbn [zesuEncoderU256SavedRegisters]) in "Hsaved".
  iAssert (instr_pre 0x15cd8
    (zesu_c_call_ret 0
      [s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11]
      (BV 64 0x15cd8)
      (sp - BV 64 48)%bv
      (fun _ =>
        mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)))%I
    with "[Hnext Hframe HsavedRet Hcaller]" as "Hreturn".
  {
    iApply instr_pre_to_body. iNext.
    iApply (instr_pre_wand 0x15cd8 0x15cd8 false false with "Hnext");
      [done | done |].
    iIntros "HoutputReturn".
    rewrite /zesuEncoderU256AfterOutputSpec.
    iExists sp, ret,
      [s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11], tail.
    iFrame.
    repeat iSplit; try iPureIntro; try assumption.
    all: try reflexivity.
    all: try (repeat constructor; assumption).
  }
  rewrite /zesuWriteOutputCallSpec /zesu_c_call.
  iExists (sp - BV 64 48)%bv, (BV 64 0x15cd8).
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  all: simpl.
Qed.

Lemma zesu_encoder_u256_output_call `{!islaG Sigma} `{!threadG} :
  instr 0x15cc8 (Some IslaTraces.write_success_08.a15cc8.a15cc8) -∗
  instr 0x15ccc (Some IslaTraces.write_success_08.a15ccc.a15ccc) -∗
  instr 0x15cd0 (Some IslaTraces.write_success_08.a15cd0.a15cd0) -∗
  instr 0x15cd4 (Some IslaTraces.write_success_08.a15cd4.a15cd4) -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x15cd8 zesuEncoderU256AfterOutputSpec -∗
  instr_body 0x15cc8 zesuEncoderU256AtOutputCallSpec.
Proof.
  iStartProof.
  iIntros "#H18 #H1c #H20 #H24 #Houtput Hnext".
  iAssert (□ instr_pre 0x10190
    zesuEncoderU256WriteOutputEntrySpec)%I as "#HwriteOutput".
  {
    iModIntro.
    iApply (instr_pre_wand 0x10190 0x10190 true true with "Houtput");
      [done | done |].
    iApply zesu_encoder_u256_write_output_entry_to_call.
  }
  iClear "Houtput".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  Unshelve. all: try liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  iExists (tail, saved, ret, sp, tt)ₗ.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try reflexivity.
  all: try bv_solve.
  all: try lia.
  all: simpl.
Qed.

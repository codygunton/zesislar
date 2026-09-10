From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsWithdrawalsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsSpec.

Import ListNotations.
Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Ltac run_withdrawals_returns :=
  lazymatch goal with
  | |- environments.envs_entails _ (∃ _ : (), _)%I =>
      iExists tt;
      iSplit; [|done];
      run_write_success_withdrawals_chunk 0x156dc;
      run_withdrawals_returns
  | |- environments.envs_entails _ ((_ -∗ _) ∗ True) =>
      iSplit; [|done];
      liARun;
      run_withdrawals_returns
  | |- environments.envs_entails _
      (subsume
        (instr ?address
          (IslaTraces.write_success_blocks.Index.lookup ?address)) _ _) =>
      iEval (vm_compute [IslaTraces.write_success_blocks.Index.lookup]);
      iApply subsume_instr_some_pre;
      run_withdrawals_returns
  | _ => idtac
  end.

Lemma write_success_withdrawals_rest `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x156dc (writeSuccessWithdrawalsTailSpec P) -∗
  instr_body 0x156a8
    (writeSuccessWithdrawalsCopiedSpec WithdrawalsFirstInt P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hint #Houtput Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  run_write_success_withdrawals_chunk 0x156dc.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try run_withdrawals_returns.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  Unshelve.
  all: try run_withdrawals_returns.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  Unshelve.
  all: try run_withdrawals_returns.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  Unshelve.
  all: try run_withdrawals_returns.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  Unshelve.
  iExists
    (tail, suffix, prefix, prefix ++ suffix, processed,
     (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try liAStep.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  Unshelve.
  all: try liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
Qed.

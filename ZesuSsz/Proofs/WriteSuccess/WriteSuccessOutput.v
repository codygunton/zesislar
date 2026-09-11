Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Hooks.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Export.Snapshots.

Import ListNotations.
Import ZesuSsz.Automation.Hooks.

#[local] Hint Rewrite bv_sign_extend_64_idemp : isla_coq_rewrite.

Definition writeOutputEntry `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_data old_size : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    0x2401a0c0 ↦ₘ old_data ∗ 0x2401a0c8 ↦ₘ old_size ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeOutputEntry) := I.

Definition writeOutputExit `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
   0x2401a0c0 ↦ₘ data ∗ 0x2401a0c8 ↦ₘ size ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeOutputExit) := I.

Lemma write_output_correct `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x10190
    (writeOutputEntry data size ret P ∗
     instr_pre (bv_unsigned ret) (writeOutputExit data size ret P) ∗ True).
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Definition writeOutputTraceSpec `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    bv_unsigned data ↦ₘ∗ payload ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents data size payload tail) ∗
    ⌜Z.to_N (bv_unsigned size) = N.of_nat (length payload)⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits ret ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
       "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
       bv_unsigned data ↦ₘ∗ payload ∗
       mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@writeOutputTraceSpec) := I.

Lemma write_output_trace_correct `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x10190 (writeOutputTraceSpec data size ret payload tail P).
Proof.
  move => * /=.
  iStartProof.
  unshelve (repeat zesu_liAStepNoWrite).
  1-3: prepare_sidecond; try assumption; try bv_solve.
  replace LET4 with (BV 64 0x2401a0c0) by
    (unfold LET4, LET2, LET0; bv_solve).
  zesu_liAStepGenericWrite.
  Unshelve.
  unshelve (repeat zesu_liAStepNoWrite).
  1: prepare_sidecond; try assumption; try bv_solve.
  replace LET8 with (BV 64 0x2401a0c8) by bv_solve.
  zesu_liAStepSnapshotWriteAt (bv_unsigned data).
  Unshelve.
  unshelve (repeat zesu_liAStepNoWrite).
  iExists ((fun snapshot =>
    read_mem_list snapshot.(snap_mem) (bv_unsigned data)
      (Z.to_N (bv_unsigned size)) = Some payload), tail, tt)ₗ.
  iSplit.
  { iPureIntro. intros snapshot Hmemory.
    inversion Hmemory as [|[address bytes] claims Hhead Htail]; subst.
    rewrite H0. exact Hhead. }
  iSplit.
  { iPureIntro. reflexivity. }
  unshelve (repeat zesu_liAStepNoWrite).
  all: try iFrame.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Print Assumptions write_output_trace_correct.

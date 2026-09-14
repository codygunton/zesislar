Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.SnapshotSlices.
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

Definition writeOutputWholeSpec `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (base : Z) (start count : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    base ↦ₘ∗ bytes ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents data size (take count (drop start bytes)) tail) ∗
    ⌜Z.to_N (bv_unsigned size) = N.of_nat count⌝ ∗
    ⌜bv_unsigned data = (base + Z.of_nat start)%Z⌝ ∗
    ⌜(start + count <= length bytes)%nat⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits ret ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
       "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
       base ↦ₘ∗ bytes ∗
       mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ P ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@writeOutputWholeSpec) := I.

Lemma write_output_whole_correct `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (base : Z) (start count : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x10190 (writeOutputWholeSpec data size ret base start count bytes tail P).
Proof.
  move => * /=.
  iStartProof.
  unshelve (repeat zesu_liAStepNoWrite).
  all: try zesu_solve_pending_sidecond.
  zesu_liAStepGenericWrite.
  Unshelve.
  unshelve (repeat zesu_liAStepNoWrite).
  all: try zesu_solve_pending_sidecond.
  zesu_liAStepSnapshotWriteAt base.
  Unshelve.
  unshelve (repeat zesu_liAStepNoWrite).
  iExists ((fun snapshot =>
    read_mem_list snapshot.(snap_mem) (bv_unsigned data)
      (Z.to_N (bv_unsigned size)) = Some (take count (drop start bytes))), tail, tt)ₗ.
  iSplit.
  { iPureIntro. intros snapshot Hmemory.
    inversion Hmemory as [|[address owned] claims Hhead Htail]; subst.
    match goal with
    | Hd : bv_unsigned data = (base + Z.of_nat start)%Z,
      Hs : Z.to_N (bv_unsigned size) = N.of_nat count |- _ =>
      rewrite Hd Hs; eapply snapshot_memory_slice; eassumption
    end. }
  iSplit.
  { iPureIntro. reflexivity. }
  unshelve (repeat zesu_liAStepNoWrite).
  all: try zesu_run.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Print Assumptions write_output_whole_correct.

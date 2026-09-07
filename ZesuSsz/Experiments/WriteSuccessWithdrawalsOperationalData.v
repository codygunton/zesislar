From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.opsem.
Require Import IslaTraces.write_success_01.instrs.
Require Import IslaTraces.write_success_02.instrs.
Require Import IslaTraces.write_success_07.instrs.
Require Import IslaTraces.write_success_87.instrs.
Require Import IslaTraces.write_success_88.instrs.
Require Import IslaTraces.write_success_89.instrs.
Require Import IslaTraces.write_success_90.instrs.
Require Import IslaTraces.write_success_91.instrs.
Require Import IslaTraces.write_success_92.instrs.
Require Import IslaTraces.write_success_93.instrs.
Require Import IslaTraces.write_success_94.instrs.
Require Import IslaTraces.write_success_95.instrs.
Require Import IslaTraces.write_success_96.instrs.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessWithdrawalsInstructionMap : list (Z * isla_trace) :=
  IslaTraces.write_success_01.instrs.instr_map ++
  IslaTraces.write_success_02.instrs.instr_map ++
  IslaTraces.write_success_07.instrs.instr_map ++
  IslaTraces.write_success_87.instrs.instr_map ++
  IslaTraces.write_success_88.instrs.instr_map ++
  IslaTraces.write_success_89.instrs.instr_map ++
  IslaTraces.write_success_90.instrs.instr_map ++
  IslaTraces.write_success_91.instrs.instr_map ++
  IslaTraces.write_success_92.instrs.instr_map ++
  IslaTraces.write_success_93.instrs.instr_map ++
  IslaTraces.write_success_94.instrs.instr_map ++
  IslaTraces.write_success_95.instrs.instr_map ++
  IslaTraces.write_success_96.instrs.instr_map.

Definition writeSuccessWithdrawalsInstructionSource
    (pc : Z) (trace : isla_trace) : Prop :=
  In (pc, trace) writeSuccessWithdrawalsInstructionMap.

Definition writeSuccessWithdrawalsInstructionTable
    (global : seq_global_state) : Prop :=
  forall pc trace,
    writeSuccessWithdrawalsInstructionSource pc trace ->
    global.(seq_instrs) !! Z_to_bv 64 pc = Some trace.

Definition writeSuccessWithdrawalsMemcpyBytePcs : list Z :=
  [0x101d8; 0x101e0; 0x101e4; 0x101e8; 0x101ec; 0x101f0; 0x101f4].

Definition writeSuccessWithdrawalsMemcpyPcs (count : nat) : list Z :=
  [0x101d4] ++ concat (repeat writeSuccessWithdrawalsMemcpyBytePcs count) ++
  [0x101d8; 0x101dc].

Definition writeSuccessWithdrawalsOutputPcs : list Z :=
  [0x10190; 0x10194; 0x10198; 0x1019c; 0x101a0].

Definition writeSuccessWithdrawalsIntegerPcs : list Z :=
  [0x15d10; 0x15d14; 0x15d18; 0x15d1c; 0x15d20; 0x15d24; 0x15d28] ++
  writeSuccessWithdrawalsOutputPcs ++ [0x15d2c; 0x15d30; 0x15d34].

Definition writeSuccessWithdrawalsIterationPcs : list Z :=
  [0x15694; 0x15698; 0x1569c; 0x156a0; 0x156a4] ++
  writeSuccessWithdrawalsMemcpyPcs 48 ++
  [0x156a8; 0x156ac; 0x156b0] ++
  writeSuccessWithdrawalsIntegerPcs ++
  [0x156b4; 0x156b8; 0x156bc] ++
  writeSuccessWithdrawalsIntegerPcs ++
  [0x156c0; 0x156c4; 0x156c8; 0x156cc] ++
  writeSuccessWithdrawalsOutputPcs ++
  [0x156d0; 0x156d4; 0x156d8] ++
  writeSuccessWithdrawalsIntegerPcs ++
  [0x156dc; 0x156e0; 0x156e4].

Definition writeSuccessWithdrawalsPreheaderPcs : list Z :=
  [0x1568c; 0x15690].

Definition writeSuccessWithdrawalsRepeatedIterationPcs (count : nat) : list Z :=
  concat (repeat writeSuccessWithdrawalsIterationPcs count).

Definition writeSuccessWithdrawalsFromPreheaderPcs (count : nat) : list Z :=
  writeSuccessWithdrawalsPreheaderPcs ++
    writeSuccessWithdrawalsRepeatedIterationPcs count.

Lemma writeSuccessWithdrawalsMemcpyCostChecked count :
  length (writeSuccessWithdrawalsMemcpyPcs count) = (7 * count + 3)%nat.
Proof.
  have Hrepeat : forall n,
      length (concat (repeat writeSuccessWithdrawalsMemcpyBytePcs n)) =
        (7 * n)%nat.
  { intros n. induction n as [|n IH]; simpl; first reflexivity.
    rewrite IH. lia. }
  unfold writeSuccessWithdrawalsMemcpyPcs.
  rewrite !app_length Hrepeat. cbn. lia.
Qed.

Lemma writeSuccessWithdrawalsOutputCostChecked :
  length writeSuccessWithdrawalsOutputPcs = 5%nat.
Proof. reflexivity. Qed.

Lemma writeSuccessWithdrawalsIntegerCostChecked :
  length writeSuccessWithdrawalsIntegerPcs = 15%nat.
Proof. reflexivity. Qed.

Lemma writeSuccessWithdrawalsIterationCostChecked :
  length writeSuccessWithdrawalsIterationPcs = 410%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma writeSuccessWithdrawalsPreheaderCostChecked :
  length writeSuccessWithdrawalsPreheaderPcs = 2%nat.
Proof. reflexivity. Qed.

Lemma writeSuccessWithdrawalsRepeatedIterationCostChecked count :
  length (writeSuccessWithdrawalsRepeatedIterationPcs count) =
    (410 * count)%nat.
Proof.
  unfold writeSuccessWithdrawalsRepeatedIterationPcs.
  induction count as [|count IH]; first reflexivity.
  change (length (writeSuccessWithdrawalsIterationPcs ++
    concat (repeat writeSuccessWithdrawalsIterationPcs count)) =
      (410 * S count)%nat).
  rewrite app_length writeSuccessWithdrawalsIterationCostChecked IH. lia.
Qed.

Lemma writeSuccessWithdrawalsFromPreheaderCostChecked count :
  length (writeSuccessWithdrawalsFromPreheaderPcs count) =
    (410 * count + 2)%nat.
Proof.
  unfold writeSuccessWithdrawalsFromPreheaderPcs.
  rewrite app_length writeSuccessWithdrawalsPreheaderCostChecked.
  rewrite writeSuccessWithdrawalsRepeatedIterationCostChecked. lia.
Qed.

Lemma writeSuccessWithdrawalsFrom15694CostRejectsPlusTwo count :
  length (writeSuccessWithdrawalsRepeatedIterationPcs count) <>
    (410 * count + 2)%nat.
Proof. rewrite writeSuccessWithdrawalsRepeatedIterationCostChecked. lia. Qed.

Lemma writeSuccessWithdrawalsPreheaderPcsHaveTraces :
  Forall (fun pc => exists trace,
    writeSuccessWithdrawalsInstructionSource pc trace)
    writeSuccessWithdrawalsPreheaderPcs.
Proof.
  unfold writeSuccessWithdrawalsPreheaderPcs,
    writeSuccessWithdrawalsInstructionSource,
    writeSuccessWithdrawalsInstructionMap.
  constructor.
  - exists IslaTraces.write_success_89.a1568c.a1568c. cbn. tauto.
  - constructor.
    + exists IslaTraces.write_success_89.a15690.a15690. cbn. tauto.
    + constructor.
Qed.

Ltac solve_write_success_withdrawals_source trace :=
  exists trace;
  unfold writeSuccessWithdrawalsInstructionSource,
    writeSuccessWithdrawalsInstructionMap;
  cbn; tauto.

Lemma writeSuccessWithdrawalsMemcpyBytePcsHaveTraces :
  Forall (fun pc => exists trace,
    writeSuccessWithdrawalsInstructionSource pc trace)
    writeSuccessWithdrawalsMemcpyBytePcs.
Proof.
  unfold writeSuccessWithdrawalsMemcpyBytePcs.
  constructor; [solve_write_success_withdrawals_source
    IslaTraces.write_success_02.a101d8.a101d8|].
  constructor; [solve_write_success_withdrawals_source
    IslaTraces.write_success_02.a101e0.a101e0|].
  constructor; [solve_write_success_withdrawals_source
    IslaTraces.write_success_02.a101e4.a101e4|].
  constructor; [solve_write_success_withdrawals_source
    IslaTraces.write_success_02.a101e8.a101e8|].
  constructor; [solve_write_success_withdrawals_source
    IslaTraces.write_success_02.a101ec.a101ec|].
  constructor; [solve_write_success_withdrawals_source
    IslaTraces.write_success_02.a101f0.a101f0|].
  constructor; [solve_write_success_withdrawals_source
    IslaTraces.write_success_02.a101f4.a101f4|].
  constructor.
Qed.

Lemma writeSuccessWithdrawalsMemcpyPcsHaveTraces count :
  Forall (fun pc => exists trace,
    writeSuccessWithdrawalsInstructionSource pc trace)
    (writeSuccessWithdrawalsMemcpyPcs count).
Proof.
  unfold writeSuccessWithdrawalsMemcpyPcs.
  apply Forall_app. split.
  - constructor; [solve_write_success_withdrawals_source
      IslaTraces.write_success_02.a101d4.a101d4|constructor].
  - apply Forall_app. split.
    + apply Forall_concat.
      induction count as [|count IH]; cbn; constructor; auto.
      exact writeSuccessWithdrawalsMemcpyBytePcsHaveTraces.
    + constructor; [solve_write_success_withdrawals_source
        IslaTraces.write_success_02.a101d8.a101d8|].
      constructor; [solve_write_success_withdrawals_source
        IslaTraces.write_success_02.a101dc.a101dc|constructor].
Qed.

Lemma writeSuccessWithdrawalsOutputPcsHaveTraces :
  Forall (fun pc => exists trace,
    writeSuccessWithdrawalsInstructionSource pc trace)
    writeSuccessWithdrawalsOutputPcs.
Proof.
  unfold writeSuccessWithdrawalsOutputPcs.
  constructor; [solve_write_success_withdrawals_source
    IslaTraces.write_success_01.a10190.a10190|].
  constructor; [solve_write_success_withdrawals_source
    IslaTraces.write_success_01.a10194.a10194|].
  constructor; [solve_write_success_withdrawals_source
    IslaTraces.write_success_01.a10198.a10198|].
  constructor; [solve_write_success_withdrawals_source
    IslaTraces.write_success_01.a1019c.a1019c|].
  constructor; [solve_write_success_withdrawals_source
    IslaTraces.write_success_01.a101a0.a101a0|constructor].
Qed.

Lemma writeSuccessWithdrawalsIntegerPcsHaveTraces :
  Forall (fun pc => exists trace,
    writeSuccessWithdrawalsInstructionSource pc trace)
    writeSuccessWithdrawalsIntegerPcs.
Proof.
  unfold writeSuccessWithdrawalsIntegerPcs.
  apply Forall_app. split.
  - constructor; [solve_write_success_withdrawals_source
      IslaTraces.write_success_07.a15d10.a15d10|].
    constructor; [solve_write_success_withdrawals_source
      IslaTraces.write_success_07.a15d14.a15d14|].
    constructor; [solve_write_success_withdrawals_source
      IslaTraces.write_success_07.a15d18.a15d18|].
    constructor; [solve_write_success_withdrawals_source
      IslaTraces.write_success_07.a15d1c.a15d1c|].
    constructor; [solve_write_success_withdrawals_source
      IslaTraces.write_success_07.a15d20.a15d20|].
    constructor; [solve_write_success_withdrawals_source
      IslaTraces.write_success_07.a15d24.a15d24|].
    constructor; [solve_write_success_withdrawals_source
      IslaTraces.write_success_07.a15d28.a15d28|constructor].
  - apply Forall_app. split; [exact writeSuccessWithdrawalsOutputPcsHaveTraces|].
    constructor; [solve_write_success_withdrawals_source
      IslaTraces.write_success_07.a15d2c.a15d2c|].
    constructor; [solve_write_success_withdrawals_source
      IslaTraces.write_success_07.a15d30.a15d30|].
    constructor; [solve_write_success_withdrawals_source
      IslaTraces.write_success_07.a15d34.a15d34|constructor].
Qed.

Ltac solve_write_success_withdrawals_main_pc :=
  first
    [ solve_write_success_withdrawals_source IslaTraces.write_success_90.a15694.a15694
    | solve_write_success_withdrawals_source IslaTraces.write_success_90.a15698.a15698
    | solve_write_success_withdrawals_source IslaTraces.write_success_90.a1569c.a1569c
    | solve_write_success_withdrawals_source IslaTraces.write_success_90.a156a0.a156a0
    | solve_write_success_withdrawals_source IslaTraces.write_success_90.a156a4.a156a4
    | solve_write_success_withdrawals_source IslaTraces.write_success_91.a156a8.a156a8
    | solve_write_success_withdrawals_source IslaTraces.write_success_91.a156ac.a156ac
    | solve_write_success_withdrawals_source IslaTraces.write_success_91.a156b0.a156b0
    | solve_write_success_withdrawals_source IslaTraces.write_success_92.a156b4.a156b4
    | solve_write_success_withdrawals_source IslaTraces.write_success_92.a156b8.a156b8
    | solve_write_success_withdrawals_source IslaTraces.write_success_92.a156bc.a156bc
    | solve_write_success_withdrawals_source IslaTraces.write_success_93.a156c0.a156c0
    | solve_write_success_withdrawals_source IslaTraces.write_success_93.a156c4.a156c4
    | solve_write_success_withdrawals_source IslaTraces.write_success_93.a156c8.a156c8
    | solve_write_success_withdrawals_source IslaTraces.write_success_93.a156cc.a156cc
    | solve_write_success_withdrawals_source IslaTraces.write_success_94.a156d0.a156d0
    | solve_write_success_withdrawals_source IslaTraces.write_success_94.a156d4.a156d4
    | solve_write_success_withdrawals_source IslaTraces.write_success_94.a156d8.a156d8
    | solve_write_success_withdrawals_source IslaTraces.write_success_95.a156dc.a156dc
    | solve_write_success_withdrawals_source IslaTraces.write_success_95.a156e0.a156e0
    | solve_write_success_withdrawals_source IslaTraces.write_success_95.a156e4.a156e4 ].

Ltac solve_write_success_withdrawals_main_pcs :=
  repeat (constructor; [solve_write_success_withdrawals_main_pc|]); constructor.

Lemma writeSuccessWithdrawalsIterationPcsHaveTraces :
  Forall (fun pc => exists trace,
    writeSuccessWithdrawalsInstructionSource pc trace)
    writeSuccessWithdrawalsIterationPcs.
Proof.
  unfold writeSuccessWithdrawalsIterationPcs.
  apply Forall_app. split; [solve_write_success_withdrawals_main_pcs|].
  apply Forall_app. split.
  - exact (writeSuccessWithdrawalsMemcpyPcsHaveTraces 48).
  - apply Forall_app. split; [solve_write_success_withdrawals_main_pcs|].
    apply Forall_app. split; [exact writeSuccessWithdrawalsIntegerPcsHaveTraces|].
    apply Forall_app. split; [solve_write_success_withdrawals_main_pcs|].
    apply Forall_app. split; [exact writeSuccessWithdrawalsIntegerPcsHaveTraces|].
    apply Forall_app. split; [solve_write_success_withdrawals_main_pcs|].
    apply Forall_app. split; [exact writeSuccessWithdrawalsOutputPcsHaveTraces|].
    apply Forall_app. split; [solve_write_success_withdrawals_main_pcs|].
    apply Forall_app. split; [exact writeSuccessWithdrawalsIntegerPcsHaveTraces|].
    solve_write_success_withdrawals_main_pcs.
Qed.

Print Assumptions writeSuccessWithdrawalsMemcpyCostChecked.
Print Assumptions writeSuccessWithdrawalsOutputCostChecked.
Print Assumptions writeSuccessWithdrawalsIntegerCostChecked.
Print Assumptions writeSuccessWithdrawalsIterationCostChecked.
Print Assumptions writeSuccessWithdrawalsPreheaderCostChecked.
Print Assumptions writeSuccessWithdrawalsRepeatedIterationCostChecked.
Print Assumptions writeSuccessWithdrawalsFromPreheaderCostChecked.
Print Assumptions writeSuccessWithdrawalsFrom15694CostRejectsPlusTwo.
Print Assumptions writeSuccessWithdrawalsPreheaderPcsHaveTraces.
Print Assumptions writeSuccessWithdrawalsMemcpyBytePcsHaveTraces.
Print Assumptions writeSuccessWithdrawalsMemcpyPcsHaveTraces.
Print Assumptions writeSuccessWithdrawalsOutputPcsHaveTraces.
Print Assumptions writeSuccessWithdrawalsIntegerPcsHaveTraces.
Print Assumptions writeSuccessWithdrawalsIterationPcsHaveTraces.

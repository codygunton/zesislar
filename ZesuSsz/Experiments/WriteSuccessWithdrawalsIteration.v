From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import IslaTraces.write_success_01.instrs.
Require Import IslaTraces.write_success_02.instrs.
Require Import IslaTraces.write_success_07.instrs.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMeasure.

Import ListNotations.
Open Scope Z_scope.

(** The state fields exposed by one native withdrawals-loop iteration.  The
    [frame] parameter names the resources that the iteration must preserve. *)
Record WriteSuccessWithdrawalsIterationState (Frame : Type) : Type := {
  writeSuccessIterationPc : Z;
  writeSuccessIterationPointer : Z;
  writeSuccessIterationProcessed : nat;
  writeSuccessIterationRemaining : nat;
  writeSuccessIterationSuffix : list (bv 8);
  writeSuccessIterationFrame : Frame
}.

Arguments writeSuccessIterationPc {Frame} _.
Arguments writeSuccessIterationPointer {Frame} _.
Arguments writeSuccessIterationProcessed {Frame} _.
Arguments writeSuccessIterationRemaining {Frame} _.
Arguments writeSuccessIterationSuffix {Frame} _.
Arguments writeSuccessIterationFrame {Frame} _.

Definition writeSuccessWithdrawalsIterationUpdate {Frame}
    (before after : WriteSuccessWithdrawalsIterationState Frame) : Prop :=
  writeSuccessIterationPc before = 0x15694 /\
  writeSuccessIterationRemaining before =
    S (writeSuccessIterationRemaining after) /\
  length (writeSuccessIterationSuffix before) =
    (48 * writeSuccessIterationRemaining before)%nat /\
  writeSuccessIterationPointer after =
    writeSuccessIterationPointer before + 48 /\
  writeSuccessIterationProcessed after =
    S (writeSuccessIterationProcessed before) /\
  writeSuccessIterationSuffix after =
    skipn 48 (writeSuccessIterationSuffix before) /\
  writeSuccessIterationFrame after = writeSuccessIterationFrame before /\
  writeSuccessIterationPc after =
    if writeSuccessIterationRemaining after is O then 0x156e8 else 0x15694.

Lemma writeSuccessWithdrawalsIterationStateUpdate {Frame}
    (before after : WriteSuccessWithdrawalsIterationState Frame) :
  writeSuccessWithdrawalsIterationUpdate before after ->
  writeSuccessIterationPointer after =
    writeSuccessIterationPointer before + 48 /\
  writeSuccessIterationSuffix after =
    skipn 48 (writeSuccessIterationSuffix before) /\
  writeSuccessIterationFrame after = writeSuccessIterationFrame before /\
  (writeSuccessIterationPc after = 0x15694 \/
   writeSuccessIterationPc after = 0x156e8).
Proof.
  intros (_ & _ & _ & Hpointer & _ & Hsuffix & Hframe & Hpc).
  repeat split; try assumption.
  destruct (writeSuccessIterationRemaining after); cbn in Hpc; auto.
Qed.

Lemma writeSuccessWithdrawalsIterationDecreases {Frame}
    (before after : WriteSuccessWithdrawalsIterationState Frame) :
  writeSuccessWithdrawalsIterationUpdate before after ->
  (writeSuccessWithdrawalsMeasure (writeSuccessIterationSuffix after) <
   writeSuccessWithdrawalsMeasure (writeSuccessIterationSuffix before))%nat.
Proof.
  intros (_ & Hremaining & Hlength & _ & _ & Hsuffix & _ & _).
  rewrite Hsuffix. unfold writeSuccessWithdrawalsMeasure.
  rewrite skipn_length. rewrite Hlength. rewrite Hremaining. lia.
Qed.

Lemma writeSuccessWithdrawalsIterationBackEdge {Frame}
    (before after : WriteSuccessWithdrawalsIterationState Frame) :
  writeSuccessWithdrawalsIterationUpdate before after ->
  writeSuccessIterationRemaining after <> O ->
  writeSuccessIterationPc after = 0x15694.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & Hpc) Hremaining.
  destruct (writeSuccessIterationRemaining after); congruence.
Qed.

Lemma writeSuccessWithdrawalsIterationExit {Frame}
    (before after : WriteSuccessWithdrawalsIterationState Frame) :
  writeSuccessWithdrawalsIterationUpdate before after ->
  writeSuccessIterationRemaining after = O ->
  writeSuccessIterationPc after = 0x156e8.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & Hpc) Hremaining.
  rewrite Hremaining in Hpc. exact Hpc.
Qed.

(** These lists record completed instruction PCs.  They come from the pinned
    traces for memcpy, write_output, Encoder.int, and the loop body. *)
Definition writeSuccessWithdrawalsMemcpyBytePcs : list Z :=
  [0x101d8; 0x101e0; 0x101e4; 0x101e8; 0x101ec; 0x101f0; 0x101f4].

Definition writeSuccessWithdrawalsMemcpy48Pcs : list Z :=
  [0x101d4] ++
  concat (repeat writeSuccessWithdrawalsMemcpyBytePcs 48) ++
  [0x101d8; 0x101dc].

Definition writeSuccessWithdrawalsOutputPcs : list Z :=
  [0x10190; 0x10194; 0x10198; 0x1019c; 0x101a0].

Definition writeSuccessWithdrawalsIntegerPcs : list Z :=
  [0x15d10; 0x15d14; 0x15d18; 0x15d1c; 0x15d20; 0x15d24; 0x15d28] ++
  writeSuccessWithdrawalsOutputPcs ++ [0x15d2c; 0x15d30; 0x15d34].

Definition writeSuccessWithdrawalsIterationPcs : list Z :=
  [0x15694; 0x15698; 0x1569c; 0x156a0; 0x156a4] ++
  writeSuccessWithdrawalsMemcpy48Pcs ++
  [0x156a8; 0x156ac; 0x156b0] ++
  writeSuccessWithdrawalsIntegerPcs ++
  [0x156b4; 0x156b8; 0x156bc] ++
  writeSuccessWithdrawalsIntegerPcs ++
  [0x156c0; 0x156c4; 0x156c8; 0x156cc] ++
  writeSuccessWithdrawalsOutputPcs ++
  [0x156d0; 0x156d4; 0x156d8] ++
  writeSuccessWithdrawalsIntegerPcs ++
  [0x156dc; 0x156e0; 0x156e4].

Definition writeSuccessWithdrawalsIterationCost : nat :=
  length writeSuccessWithdrawalsIterationPcs.

Lemma writeSuccessWithdrawalsIterationCostChecked :
  writeSuccessWithdrawalsIterationCost = 410%nat.
Proof. vm_compute. reflexivity. Qed.

Definition writeSuccessWithdrawalsPcHasTrace (pc : Z) : Prop :=
  exists trace,
    IslaTraces.write_success_blocks.Index.lookup pc = Some trace \/
    In (pc, trace) IslaTraces.write_success_01.instrs.instr_map \/
    In (pc, trace) IslaTraces.write_success_02.instrs.instr_map \/
    In (pc, trace) IslaTraces.write_success_07.instrs.instr_map.

Lemma writeSuccessWithdrawalsOutputPcHasTrace pc trace :
  In (pc, trace) IslaTraces.write_success_01.instrs.instr_map ->
  writeSuccessWithdrawalsPcHasTrace pc.
Proof. intro Hin. exists trace. auto. Qed.

Lemma writeSuccessWithdrawalsMemcpyPcHasTrace pc trace :
  In (pc, trace) IslaTraces.write_success_02.instrs.instr_map ->
  writeSuccessWithdrawalsPcHasTrace pc.
Proof. intro Hin. exists trace. auto. Qed.

Lemma writeSuccessWithdrawalsIntegerPcHasTrace pc trace :
  In (pc, trace) IslaTraces.write_success_07.instrs.instr_map ->
  writeSuccessWithdrawalsPcHasTrace pc.
Proof. intro Hin. exists trace. auto. Qed.

Lemma writeSuccessWithdrawalsMemcpyBytePcsHaveTraces :
  Forall writeSuccessWithdrawalsPcHasTrace
    writeSuccessWithdrawalsMemcpyBytePcs.
Proof.
  unfold writeSuccessWithdrawalsMemcpyBytePcs.
  constructor; [apply writeSuccessWithdrawalsMemcpyPcHasTrace with
    (trace := IslaTraces.write_success_02.a101d8.a101d8); cbn; tauto|].
  constructor; [apply writeSuccessWithdrawalsMemcpyPcHasTrace with
    (trace := IslaTraces.write_success_02.a101e0.a101e0); cbn; tauto|].
  constructor; [apply writeSuccessWithdrawalsMemcpyPcHasTrace with
    (trace := IslaTraces.write_success_02.a101e4.a101e4); cbn; tauto|].
  constructor; [apply writeSuccessWithdrawalsMemcpyPcHasTrace with
    (trace := IslaTraces.write_success_02.a101e8.a101e8); cbn; tauto|].
  constructor; [apply writeSuccessWithdrawalsMemcpyPcHasTrace with
    (trace := IslaTraces.write_success_02.a101ec.a101ec); cbn; tauto|].
  constructor; [apply writeSuccessWithdrawalsMemcpyPcHasTrace with
    (trace := IslaTraces.write_success_02.a101f0.a101f0); cbn; tauto|].
  constructor; [apply writeSuccessWithdrawalsMemcpyPcHasTrace with
    (trace := IslaTraces.write_success_02.a101f4.a101f4); cbn; tauto|].
  constructor.
Qed.

Lemma writeSuccessWithdrawalsOutputPcsHaveTraces :
  Forall writeSuccessWithdrawalsPcHasTrace writeSuccessWithdrawalsOutputPcs.
Proof.
  unfold writeSuccessWithdrawalsOutputPcs.
  constructor; [apply writeSuccessWithdrawalsOutputPcHasTrace with
    (trace := IslaTraces.write_success_01.a10190.a10190); cbn; tauto|].
  constructor; [apply writeSuccessWithdrawalsOutputPcHasTrace with
    (trace := IslaTraces.write_success_01.a10194.a10194); cbn; tauto|].
  constructor; [apply writeSuccessWithdrawalsOutputPcHasTrace with
    (trace := IslaTraces.write_success_01.a10198.a10198); cbn; tauto|].
  constructor; [apply writeSuccessWithdrawalsOutputPcHasTrace with
    (trace := IslaTraces.write_success_01.a1019c.a1019c); cbn; tauto|].
  constructor; [apply writeSuccessWithdrawalsOutputPcHasTrace with
    (trace := IslaTraces.write_success_01.a101a0.a101a0); cbn; tauto|].
  constructor.
Qed.

Lemma writeSuccessWithdrawalsIntegerPcsHaveTraces :
  Forall writeSuccessWithdrawalsPcHasTrace writeSuccessWithdrawalsIntegerPcs.
Proof.
  unfold writeSuccessWithdrawalsIntegerPcs.
  apply Forall_app. split.
  - constructor; [apply writeSuccessWithdrawalsIntegerPcHasTrace with (trace := IslaTraces.write_success_07.a15d10.a15d10); cbn; tauto|].
    constructor; [apply writeSuccessWithdrawalsIntegerPcHasTrace with (trace := IslaTraces.write_success_07.a15d14.a15d14); cbn; tauto|].
    constructor; [apply writeSuccessWithdrawalsIntegerPcHasTrace with (trace := IslaTraces.write_success_07.a15d18.a15d18); cbn; tauto|].
    constructor; [apply writeSuccessWithdrawalsIntegerPcHasTrace with (trace := IslaTraces.write_success_07.a15d1c.a15d1c); cbn; tauto|].
    constructor; [apply writeSuccessWithdrawalsIntegerPcHasTrace with (trace := IslaTraces.write_success_07.a15d20.a15d20); cbn; tauto|].
    constructor; [apply writeSuccessWithdrawalsIntegerPcHasTrace with (trace := IslaTraces.write_success_07.a15d24.a15d24); cbn; tauto|].
    constructor; [apply writeSuccessWithdrawalsIntegerPcHasTrace with (trace := IslaTraces.write_success_07.a15d28.a15d28); cbn; tauto|].
    constructor.
  - apply Forall_app. split.
    + exact writeSuccessWithdrawalsOutputPcsHaveTraces.
    + constructor; [apply writeSuccessWithdrawalsIntegerPcHasTrace with (trace := IslaTraces.write_success_07.a15d2c.a15d2c); cbn; tauto|].
      constructor; [apply writeSuccessWithdrawalsIntegerPcHasTrace with (trace := IslaTraces.write_success_07.a15d30.a15d30); cbn; tauto|].
      constructor; [apply writeSuccessWithdrawalsIntegerPcHasTrace with (trace := IslaTraces.write_success_07.a15d34.a15d34); cbn; tauto|].
      constructor.
Qed.

Lemma writeSuccessWithdrawalsMemcpy48PcsHaveTraces :
  Forall writeSuccessWithdrawalsPcHasTrace
    writeSuccessWithdrawalsMemcpy48Pcs.
Proof.
  unfold writeSuccessWithdrawalsMemcpy48Pcs.
  apply Forall_app. split.
  - constructor.
    + apply writeSuccessWithdrawalsMemcpyPcHasTrace with
        (trace := IslaTraces.write_success_02.a101d4.a101d4). cbn; tauto.
    + constructor.
  - apply Forall_app. split.
    + apply Forall_concat.
      assert (Hrepeat : forall count,
        Forall (Forall writeSuccessWithdrawalsPcHasTrace)
          (repeat writeSuccessWithdrawalsMemcpyBytePcs count)).
      { intro count. induction count; cbn; constructor; auto.
        exact writeSuccessWithdrawalsMemcpyBytePcsHaveTraces. }
      apply Hrepeat.
    + constructor.
      * apply writeSuccessWithdrawalsMemcpyPcHasTrace with
          (trace := IslaTraces.write_success_02.a101d8.a101d8). cbn; tauto.
      * constructor.
        -- apply writeSuccessWithdrawalsMemcpyPcHasTrace with
             (trace := IslaTraces.write_success_02.a101dc.a101dc). cbn; tauto.
        -- constructor.
Qed.

Ltac solve_write_success_withdrawals_main_pc :=
  unfold writeSuccessWithdrawalsPcHasTrace; eexists; left;
  first [ apply IslaTraces.write_success_blocks.Index.lookup_a15694
      | apply IslaTraces.write_success_blocks.Index.lookup_a15698
      | apply IslaTraces.write_success_blocks.Index.lookup_a1569c
      | apply IslaTraces.write_success_blocks.Index.lookup_a156a0
      | apply IslaTraces.write_success_blocks.Index.lookup_a156a4
      | apply IslaTraces.write_success_blocks.Index.lookup_a156a8
      | apply IslaTraces.write_success_blocks.Index.lookup_a156ac
      | apply IslaTraces.write_success_blocks.Index.lookup_a156b0
      | apply IslaTraces.write_success_blocks.Index.lookup_a156b4
      | apply IslaTraces.write_success_blocks.Index.lookup_a156b8
      | apply IslaTraces.write_success_blocks.Index.lookup_a156bc
      | apply IslaTraces.write_success_blocks.Index.lookup_a156c0
      | apply IslaTraces.write_success_blocks.Index.lookup_a156c4
      | apply IslaTraces.write_success_blocks.Index.lookup_a156c8
      | apply IslaTraces.write_success_blocks.Index.lookup_a156cc
      | apply IslaTraces.write_success_blocks.Index.lookup_a156d0
      | apply IslaTraces.write_success_blocks.Index.lookup_a156d4
      | apply IslaTraces.write_success_blocks.Index.lookup_a156d8
      | apply IslaTraces.write_success_blocks.Index.lookup_a156dc
      | apply IslaTraces.write_success_blocks.Index.lookup_a156e0
      | apply IslaTraces.write_success_blocks.Index.lookup_a156e4 ].

Ltac solve_write_success_withdrawals_main_pcs :=
  repeat (constructor; [solve_write_success_withdrawals_main_pc |]);
  constructor.

Lemma writeSuccessWithdrawalsIterationPcsHaveTraces :
  Forall writeSuccessWithdrawalsPcHasTrace
    writeSuccessWithdrawalsIterationPcs.
Proof.
  unfold writeSuccessWithdrawalsIterationPcs.
  apply Forall_app. split.
  - solve_write_success_withdrawals_main_pcs.
  - apply Forall_app. split.
    + exact writeSuccessWithdrawalsMemcpy48PcsHaveTraces.
    +
  apply Forall_app. split; [solve_write_success_withdrawals_main_pcs|].
  apply Forall_app. split; [exact writeSuccessWithdrawalsIntegerPcsHaveTraces|].
  apply Forall_app. split; [solve_write_success_withdrawals_main_pcs|].
  apply Forall_app. split; [exact writeSuccessWithdrawalsIntegerPcsHaveTraces|].
  apply Forall_app. split; [solve_write_success_withdrawals_main_pcs|].
  apply Forall_app. split; [exact writeSuccessWithdrawalsOutputPcsHaveTraces|].
  apply Forall_app. split; [solve_write_success_withdrawals_main_pcs|].
  apply Forall_app. split; [exact writeSuccessWithdrawalsIntegerPcsHaveTraces|].
  solve_write_success_withdrawals_main_pcs.
Qed.

Definition writeSuccessWithdrawalsIterationReflect {Frame}
    (machine : IslaState)
    (view : WriteSuccessWithdrawalsIterationState Frame) : Prop :=
  machine.1.(seq_nb_state) = false /\
  machine.1.(seq_regs) !! machine.1.(seq_pc_reg) =
    Some (RVal_Bits
      (Z_to_bv 64 (writeSuccessIterationPc view))) /\
  machine.1.(seq_regs) !! "x8" =
    Some (RVal_Bits
      (Z_to_bv 64 (writeSuccessIterationPointer view))) /\
  machine.1.(seq_regs) !! "x9" =
    Some (RVal_Bits
      (Z_to_bv 64 (Z.of_nat (writeSuccessIterationRemaining view)))) /\
  read_mem_list machine.2.(seq_mem)
    (writeSuccessIterationPointer view)
    (N.of_nat (length (writeSuccessIterationSuffix view))) =
      Some (writeSuccessIterationSuffix view).


Lemma writeSuccessWithdrawalsUnchangedStateRejected {Frame}
    (state : WriteSuccessWithdrawalsIterationState Frame) :
  ~ writeSuccessWithdrawalsIterationUpdate state state.
Proof.
  intros (_ & Hremaining & _). lia.
Qed.

Print Assumptions writeSuccessWithdrawalsIterationDecreases.
Print Assumptions writeSuccessWithdrawalsIterationCostChecked.
Print Assumptions writeSuccessWithdrawalsIterationPcsHaveTraces.
Print Assumptions writeSuccessWithdrawalsUnchangedStateRejected.

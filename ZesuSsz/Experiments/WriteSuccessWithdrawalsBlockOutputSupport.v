From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a10190.
Require Import IslaTraces.write_success_01.a10194.
Require Import IslaTraces.write_success_01.a10198.
Require Import IslaTraces.write_success_01.a1019c.
Require Import IslaTraces.write_success_01.a101a0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRun.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10194.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessOutputPortBase : bv 64 :=
  (writeSuccess10190Link + BV 64 18446744073709551400)%bv.

Lemma writeSuccessOutputPortAddresses :
  writeSuccess10198Address writeSuccessOutputPortBase = BV 64 0x2401a0c0 /\
  writeSuccess1019cAddress writeSuccessOutputPortBase = BV 64 0x2401a0c8.
Proof. vm_compute. split; apply bv_eq; reflexivity. Qed.


Lemma writeSuccessSingleBitsStructShape value :
  valu_has_shape value
    (StructShape [("bits", MaskShape 64 0x20000 0)]) ->
  exists bits : bv 64,
    value = RegVal_Struct [("bits", RVal_Bits bits)].
Proof.
  destruct value as [[| |[]|]| | | | | | | |] => //= Hshape.
  destruct Hshape as [Hlength Hfields].
  destruct l as [|[name field] rest]; cbn in Hlength; try lia.
  destruct rest as [|entry rest]; cbn in Hlength; try lia.
  cbn in Hfields. destruct Hfields as [[Hname Hfield] _]. subst name.
  apply valu_has_mask_shape in Hfield as (bits & -> & _).
  eexists. reflexivity.
Qed.

Lemma writeSuccessOutputRegisterFacts regs :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  exists (mstatusBits satp : bv 64) oldX5,
    regs !! "x5" = Some oldX5 /\
    regs !! "mstatus" = Some
      (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) /\
    regs !! "satp" = Some (RVal_Bits satp) /\
    writeSuccess10198SysRegs regs /\
    eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true).
Proof.
  intros (Hmstatus & Hshapes & Hgeneral).
  have Hx5 := Hgeneral "x5" ltac:(cbn; auto).
  destruct Hx5 as [x5 Hx5].
  unfold zesu_ram_sys_regs, zesu_sys_regs in Hshapes. cbn in Hshapes.
  repeat match goal with
  | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
  end.
  repeat match goal with
  | H : writeSuccessWithdrawalsOperationalRegisterShape _ _ |- _ =>
      cbn in H; destruct H as (? & ? & ?); subst
  end.
  apply writeSuccessSingleBitsStructShape in H14 as (mstatusBits & ->).
  apply valu_has_bits_shape in H0 as (satp & ->).
  exists mstatusBits, satp, (RVal_Bits x5).
  unfold writeSuccessWithdrawalsOperationalMstatus in Hmstatus.
  unfold writeSuccess10198SysRegs. repeat split; eassumption.
Qed.


Print Assumptions writeSuccessOutputPortAddresses.
Print Assumptions writeSuccessOutputRegisterFacts.

Lemma writeSuccessOutputMmioPermitted global address :
  (address = BV 64 0x2401a0c0 \/ address = BV 64 0x2401a0c8) ->
  set_Forall
    (fun item =>
      ~ (0x2401a0c0 <= bv_unsigned item < 0x2401a0d0)%Z)
    (dom global.(seq_mem)) ->
  writeSuccessStoreOutcomePermitted global address WriteSuccessStoreMmio.
Proof.
  intros Haddress Hdom. destruct Haddress as [-> | ->].
  - cbn. repeat split; try lia.
    + unfold read_mem, read_mem_list; cbn.
      have Hnone : global.(seq_mem) !! BV 64 0x2401a0c0 = None.
      { apply not_elem_of_dom. intros Hin. apply Hdom in Hin.
        vm_compute in Hin; naive_solver. }
      rewrite seqZ_cons; [|lia]. cbn.
      destruct (Z_to_bv_checked 64 (bv_unsigned (BV 64 0x2401a0c0)))
        as [key|] eqn:Hchecked; cbn; last reflexivity.
      apply Z_to_bv_checked_Some in Hchecked.
      have Hkey : key = BV 64 0x2401a0c0 by
        (apply bv_eq; rewrite <- Hchecked; bv_solve).
      subst key. rewrite Hnone. reflexivity.
    + bv_solve.
    + intros item Hitem. change (~ (604086464 <= bv_unsigned item < 604086472)%Z).
      intros Hrange. apply Hdom in Hitem. apply Hitem. lia.
  - cbn. repeat split; try lia.
    + unfold read_mem, read_mem_list; cbn.
      have Hnone : global.(seq_mem) !! BV 64 0x2401a0c8 = None.
      { apply not_elem_of_dom. intros Hin. apply Hdom in Hin.
        vm_compute in Hin; naive_solver. }
      rewrite seqZ_cons; [|lia]. cbn.
      destruct (Z_to_bv_checked 64 (bv_unsigned (BV 64 0x2401a0c8)))
        as [key|] eqn:Hchecked; cbn; last reflexivity.
      apply Z_to_bv_checked_Some in Hchecked.
      have Hkey : key = BV 64 0x2401a0c8 by
        (apply bv_eq; rewrite <- Hchecked; bv_solve).
      subst key. rewrite Hnone. reflexivity.
    + bv_solve.
    + intros item Hitem. change (~ (604086472 <= bv_unsigned item < 604086480)%Z).
      intros Hrange. apply Hdom in Hitem. apply Hitem. lia.
Qed.

Print Assumptions writeSuccessOutputMmioPermitted.


Lemma writeSuccessOutputStoreAssumes regs :
  regs !! "x5" = Some (RVal_Bits writeSuccessOutputPortBase) ->
  regs !! "rv_ram_base" = Some (RVal_Bits (BV 64 0x20000000)) ->
  regs !! "rv_ram_size" = Some (RVal_Bits (BV 64 0x20000000)) ->
  eval_a_exp regs writeSuccess10198Align = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess10198Lower = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess10198Upper = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess1019cAlign = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess1019cLower = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess1019cUpper = Some (Val_Bool true).
Proof.
  intros Hbase Hrambase Hramsize.
  unfold writeSuccess10198Align, writeSuccess10198Lower,
    writeSuccess10198Upper, writeSuccess1019cAlign,
    writeSuccess1019cLower, writeSuccess1019cUpper.
  cbn. rewrite !Hbase !Hrambase !Hramsize. cbn.
  repeat split; reflexivity.
Qed.

Print Assumptions writeSuccessOutputStoreAssumes.

Lemma writeSuccess10198MmioRecords regs global mstatusBits base satp value
    result :
  segmentRecords (writeSuccess10198Before regs global)
    (writeSuccess10198Observations regs global mstatusBits base satp value
      result WriteSuccessStoreMmio) =
  [(SWriteMem (writeSuccess10198Address base) (bv_to_bvn value),
    global.(seq_mem))].
Proof. reflexivity. Qed.

Lemma writeSuccess1019cMmioRecords regs global mstatusBits base satp value
    result :
  segmentRecords (writeSuccess1019cBefore regs global)
    (writeSuccess1019cObservations regs global mstatusBits base satp value
      result WriteSuccessStoreMmio) =
  [(SWriteMem (writeSuccess1019cAddress base) (bv_to_bvn value),
    global.(seq_mem))].
Proof. reflexivity. Qed.

Print Assumptions writeSuccess10198MmioRecords.
Print Assumptions writeSuccess1019cMmioRecords.

Lemma writeSuccessOutputReturnTargetExact ra :
  bv_extract 0 2 ra = BV 2 0 ->
  writeSuccess101a0Target ra = ra.
Proof.
  intros Halign.
  have Hbit : bv_extract 0 1 ra = BV 1 0.
  { bv_simplify. bv_simplify Halign.
    bitblast as i. by bitblast Halign with i. }
  unfold writeSuccess101a0Target.
  have -> : (ra + BV 64 0)%bv = ra by bv_solve.
  apply bv_eq. bv_simplify. bv_simplify Hbit.
  bitblast as i. by bitblast Hbit with i.
Qed.

Lemma writeSuccessOutputSilentRecords regs global sp ra returnTrace :
  bv_extract 0 2 ra = BV 2 0 ->
  global.(seq_instrs) !! ra = Some returnTrace ->
  segmentRecords (writeSuccess10190Before regs global)
      (writeSuccess10190Observations regs global) = [] /\
  segmentRecords (writeSuccess10194Before regs global)
      (writeSuccess10194Observations regs global sp) = [] /\
  segmentRecords (writeSuccess101a0Before regs global)
      (writeSuccess101a0Observations regs global ra) = [].
Proof.
  intros Halign Hreturn. repeat split; try reflexivity.
  unfold segmentRecords, writeSuccess101a0Observations,
    writeSuccess101a0PrefixObservations, writeSuccess101a0Locals,
    segmentRecordsFrom, writeSuccess101a0DoneLabels.
  cbn. rewrite (writeSuccessOutputReturnTargetExact ra Halign). rewrite Hreturn.
  reflexivity.
Qed.

Print Assumptions writeSuccessOutputSilentRecords.

Definition writeSuccessOutputRegs1 regs := writeSuccess10190Regs regs.
Definition writeSuccessOutputRegs2 regs :=
  writeSuccess10194Regs (writeSuccessOutputRegs1 regs) writeSuccess10190Link.
Definition writeSuccessOutputRegs3 regs :=
  writeSuccess10198Regs (writeSuccessOutputRegs2 regs).
Definition writeSuccessOutputRegs4 regs :=
  writeSuccess1019cRegs (writeSuccessOutputRegs3 regs).

Lemma writeSuccessOutputRegs2LookupOther regs reg :
  reg <> "PC" -> reg <> "x5" ->
  writeSuccessOutputRegs2 regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx5. unfold writeSuccessOutputRegs2.
  rewrite writeSuccess10194RegsLookupOther; [|exact Hpc|exact Hx5].
  unfold writeSuccessOutputRegs1.
  apply writeSuccess10190RegsLookupOther; assumption.
Qed.

Lemma writeSuccessOutputRegs3LookupOther regs reg :
  reg <> "PC" -> reg <> "x5" ->
  writeSuccessOutputRegs3 regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx5. unfold writeSuccessOutputRegs3.
  rewrite writeSuccess10198RegsLookupOther; last congruence.
  apply writeSuccessOutputRegs2LookupOther; assumption.
Qed.

Lemma writeSuccessOutputRegs4LookupOther regs reg :
  reg <> "PC" -> reg <> "x5" ->
  writeSuccessOutputRegs4 regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx5. unfold writeSuccessOutputRegs4.
  rewrite writeSuccess1019cRegsLookupOther; last congruence.
  apply writeSuccessOutputRegs3LookupOther; assumption.
Qed.

Lemma writeSuccessOutputRegs2Base regs :
  writeSuccessOutputRegs2 regs !! "x5" =
    Some (RVal_Bits writeSuccessOutputPortBase).
Proof. unfold writeSuccessOutputRegs2, writeSuccess10194Regs.
  rewrite lookup_insert_ne; last congruence. rewrite lookup_insert.
  reflexivity. Qed.

Print Assumptions writeSuccessOutputRegs2LookupOther.
Print Assumptions writeSuccessOutputRegs3LookupOther.
Print Assumptions writeSuccessOutputRegs4LookupOther.
Print Assumptions writeSuccessOutputRegs2Base.

Lemma writeSuccessOutputInstructionFacts global :
  writeSuccessWithdrawalsInstructionTable global ->
  global.(seq_instrs) !! Z_to_bv 64 0x10190 = Some a10190 /\
  global.(seq_instrs) !! Z_to_bv 64 0x10194 = Some a10194 /\
  global.(seq_instrs) !! Z_to_bv 64 0x10198 = Some a10198 /\
  global.(seq_instrs) !! Z_to_bv 64 0x1019c = Some a1019c /\
  global.(seq_instrs) !! Z_to_bv 64 0x101a0 = Some a101a0.
Proof.
  intros Htable. repeat split; apply Htable;
    unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap; cbn; tauto.
Qed.

Print Assumptions writeSuccessOutputInstructionFacts.

Lemma writeSuccessOutputBvnToBvSame n (value : bv n) :
  bvn_to_bv n (bv_to_bvn value) = Some value.
Proof.
  destruct value as [bits Hbits]. unfold bvn_to_bv. cbn.
  destruct (decide (n = n)) as [Heq|Hneq].
  - f_equal. symmetry. apply Eqdep_dec.eq_rect_eq_dec. apply N.eq_dec.
  - exfalso. apply Hneq. reflexivity.
Qed.

Lemma writeSuccessOutputReturnAlignmentEval (regs : reg_map) (ra : bv 64) :
  regs !! "x1" = Some (RVal_Bits ra) ->
  bv_extract 0 2 ra = BV 2 0 ->
  eval_a_exp regs writeSuccess101a0Alignment = Some (Val_Bool true).
Proof.
  intros Hx1 Halign. unfold writeSuccess101a0Alignment. cbn. rewrite Hx1.
  unfold read_accessor. cbn [mbind option_bind eval_unop].
  rewrite writeSuccessOutputBvnToBvSame. cbn.
  rewrite bool_decide_true; first reflexivity.
  change (bv_extract 0 2 ra = BV 2 0). exact Halign.
Qed.

Print Assumptions writeSuccessOutputReturnAlignmentEval.


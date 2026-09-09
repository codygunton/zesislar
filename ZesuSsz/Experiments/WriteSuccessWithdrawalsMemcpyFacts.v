From Coq Require Import Lia Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101d4.
Require Import IslaTraces.write_success_02.a101d8.
Require Import IslaTraces.write_success_02.a101dc.
Require Import IslaTraces.write_success_02.a101e0.
Require Import IslaTraces.write_success_02.a101e4.
Require Import IslaTraces.write_success_02.a101e8.
Require Import IslaTraces.write_success_02.a101ec.
Require Import IslaTraces.write_success_02.a101f0.
Require Import IslaTraces.write_success_02.a101f4.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.

Lemma writeSuccessMemcpyInstructionFacts global :
  writeSuccessWithdrawalsInstructionTable global ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d4 = Some a101d4 /\
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 /\
  global.(seq_instrs) !! Z_to_bv 64 0x101dc = Some a101dc /\
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 /\
  global.(seq_instrs) !! Z_to_bv 64 0x101e4 = Some a101e4 /\
  global.(seq_instrs) !! Z_to_bv 64 0x101e8 = Some a101e8 /\
  global.(seq_instrs) !! Z_to_bv 64 0x101ec = Some a101ec /\
  global.(seq_instrs) !! Z_to_bv 64 0x101f0 = Some a101f0 /\
  global.(seq_instrs) !! Z_to_bv 64 0x101f4 = Some a101f4.
Proof.
  intros Htable. repeat split; apply Htable;
    unfold writeSuccessWithdrawalsInstructionSource,
      writeSuccessWithdrawalsInstructionMap; cbn; tauto.
Qed.

Lemma writeSuccessMemcpySingleBitsStructShape value :
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

Lemma writeSuccessMemcpyRegisterFacts regs :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  exists (mstatusBits satp x13 x14 : bv 64),
    regs !! "x13" = Some (RVal_Bits x13) /\
    regs !! "x14" = Some (RVal_Bits x14) /\
    regs !! "mstatus" = Some
      (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) /\
    regs !! "satp" = Some (RVal_Bits satp) /\
    writeSuccess101e4SysRegs regs /\
    writeSuccess101f0SysRegs regs /\
    eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true).
Proof.
  intros (Hmstatus & Hshapes & Hgeneral).
  have Hx13 := Hgeneral "x13" ltac:(cbn; tauto).
  have Hx14 := Hgeneral "x14" ltac:(cbn; tauto).
  destruct Hx13 as [x13 Hx13]. destruct Hx14 as [x14 Hx14].
  unfold zesu_ram_sys_regs, zesu_sys_regs in Hshapes. cbn in Hshapes.
  repeat match goal with
  | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
  end.
  repeat match goal with
  | H : writeSuccessWithdrawalsOperationalRegisterShape _ _ |- _ =>
      cbn in H; destruct H as (? & ? & ?); subst
  end.
  apply writeSuccessMemcpySingleBitsStructShape in H14 as (mstatusBits & ->).
  apply valu_has_bits_shape in H0 as (satp & ->).
  exists mstatusBits, satp, x13, x14.
  unfold writeSuccessWithdrawalsOperationalMstatus in Hmstatus.
  unfold writeSuccess101e4SysRegs, writeSuccess101f0SysRegs.
  repeat split; eassumption.
Qed.

Print Assumptions writeSuccessMemcpyInstructionFacts.
Print Assumptions writeSuccessMemcpySingleBitsStructShape.
Print Assumptions writeSuccessMemcpyRegisterFacts.

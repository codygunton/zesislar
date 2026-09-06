From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIteration.

Import ListNotations.

Definition writeSuccessRegisterKindHasShape
    (regs : reg_map) (entry : reg_kind * valu_shape) : Prop :=
  match entry.1 with
  | KindReg register =>
      exists value, regs !! register = Some value /\
        valu_has_shape value entry.2
  | KindField register field =>
      exists root value,
        regs !! register = Some root /\
        read_accessor [Field field] root = Some value /\
        valu_has_shape value entry.2
  end.

Definition writeSuccessWithdrawalsArchitectureRegisters
    (regs : reg_map) : Prop :=
  Forall (writeSuccessRegisterKindHasShape regs) zesu_ram_sys_regs.

Definition writeSuccessWithdrawalsInstructionSource
    (pc : Z) (trace : isla_trace) : Prop :=
  IslaTraces.write_success_blocks.Index.lookup pc = Some trace \/
  In (pc, trace) IslaTraces.write_success_01.instrs.instr_map \/
  In (pc, trace) IslaTraces.write_success_02.instrs.instr_map \/
  In (pc, trace) IslaTraces.write_success_07.instrs.instr_map.

Definition writeSuccessWithdrawalsInstructionTable
    (global : seq_global_state) : Prop :=
  forall pc trace,
    writeSuccessWithdrawalsInstructionSource pc trace ->
    global.(seq_instrs) !! Z_to_bv 64 pc = Some trace.

Definition writeSuccessWithdrawalsStart
    (regs : reg_map) (global : seq_global_state) : IslaState :=
  ({| seq_trace := IslaTraces.write_success_90.a15694.a15694;
      seq_regs := regs;
      seq_pc_reg := "PC";
      seq_nb_state := false |}, global).

Definition writeSuccessWithdrawalsMstatusAssumption : a_exp :=
  AExp_Binop Eq
    (AExp_Manyop (Bvmanyarith Bvand)
      [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0x20000)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Bits (BV 64 0)) Mk_annot) Mk_annot.

Definition writeSuccessWithdrawalsConcreteEntry
    (machine : IslaState)
    (view : WriteSuccessWithdrawalsIterationState unit)
    (sp : bv 64) (base : Z) (total processed remaining : nat)
    (bytes prefix suffix scratch : list (bv 8)) : Prop :=
  exists regs global,
    machine = writeSuccessWithdrawalsStart regs global /\
    writeSuccessWithdrawalsInstructionTable global /\
    regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15694)) /\
    regs !! "x2" = Some (RVal_Bits sp) /\
    (exists oldX10, regs !! "x10" = Some oldX10) /\
    regs !! "x8" = Some (RVal_Bits
      (Z_to_bv 64 (writeSuccessIterationPointer view))) /\
    regs !! "x9" = Some (RVal_Bits
      (Z_to_bv 64 (Z.of_nat (writeSuccessIterationRemaining view)))) /\
    regs !! "x18" = Some (RVal_Bits (sp + BV 64 1768)%bv) /\
    eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption =
      Some (Val_Bool true) /\
    writeSuccessWithdrawalsArchitectureRegisters regs /\
    (forall register,
      In register
        ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x10"; "x11";
         "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x19"; "x20";
         "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27"; "x28";
         "x29"; "x30"; "x31"] ->
      exists value : bv 64, regs !! register = Some (RVal_Bits value)) /\
    read_mem_list global.(seq_mem) base (N.of_nat (length prefix)) =
      Some prefix /\
    read_mem_list global.(seq_mem) (writeSuccessIterationPointer view)
      (N.of_nat (length suffix)) = Some suffix /\
    read_mem_list global.(seq_mem) (bv_unsigned sp + 1744)
      (N.of_nat (length scratch)) = Some scratch /\
    (exists encoderScratch : list (bv 8),
      length encoderScratch = 16%nat /\
      read_mem_list global.(seq_mem) (bv_unsigned sp - 16)
        16%N = Some encoderScratch) /\
    set_Forall
      (fun address =>
        ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
      (dom global.(seq_mem)) /\
    view = {|
      writeSuccessIterationPc := 0x15694;
      writeSuccessIterationPointer := base + 48 * Z.of_nat processed;
      writeSuccessIterationProcessed := processed;
      writeSuccessIterationRemaining := S (S remaining);
      writeSuccessIterationSuffix := suffix;
      writeSuccessIterationFrame := tt |} /\
    total = (processed + S (S remaining))%nat /\
    bytes = prefix ++ suffix /\
    length prefix = (48 * processed)%nat /\
    length suffix = (48 * S (S remaining))%nat /\
    length scratch = 48%nat /\
    bv_unsigned sp `mod` 16 = 0 /\
    (0x20000000 <= bv_unsigned sp - 16)%Z /\
    (bv_unsigned sp + 1896 < 0x40000000)%Z /\
    (0x20000000 <= base)%Z /\
    (base + Z.of_nat (length bytes) < 0x40000000)%Z.

Lemma writeSuccessWithdrawalsConcreteEntryReflects machine view sp base
    total processed remaining bytes prefix suffix scratch :
  writeSuccessWithdrawalsConcreteEntry machine view sp base total processed
    remaining bytes prefix suffix scratch ->
  writeSuccessWithdrawalsIterationReflect machine view.
Proof.
  intros (regs & global & -> & Htable & Hpc & Hsp & Hx10 & Hpointer & Hcount &
    HscratchPointer & Hmstatus & Harchitecture & Hregisters & Hprefix & Hsuffix &
    Hscratch & HencoderScratch & Hmmio & Hview & Hrest).
  subst view.
  unfold writeSuccessWithdrawalsIterationReflect,
    writeSuccessWithdrawalsStart. cbn.
  repeat split; try assumption.
Qed.

Lemma writeSuccessWithdrawalsConcreteEntryBlockingRejected machine view sp base
    total processed remaining bytes prefix suffix scratch :
  writeSuccessWithdrawalsConcreteEntry machine view sp base total processed
    remaining bytes prefix suffix scratch ->
  machine.1.(seq_nb_state) <> true.
Proof.
  intros (regs & global & -> & _). discriminate.
Qed.

Lemma writeSuccessWithdrawalsConcreteEntryTrace machine view sp base total
    processed remaining bytes prefix suffix scratch :
  writeSuccessWithdrawalsConcreteEntry machine view sp base total processed
    remaining bytes prefix suffix scratch ->
  machine.1.(seq_trace) = IslaTraces.write_success_90.a15694.a15694.
Proof. intros (regs & global & -> & _). reflexivity. Qed.

Lemma writeSuccessWithdrawalsConcreteEntryCode machine view sp base total
    processed remaining bytes prefix suffix scratch :
  writeSuccessWithdrawalsConcreteEntry machine view sp base total processed
    remaining bytes prefix suffix scratch ->
  machine.2.(seq_instrs) !! Z_to_bv 64 0x15694 =
    Some IslaTraces.write_success_90.a15694.a15694.
Proof.
  intros (regs & global & -> & Htable & _).
  apply Htable. left.
  exact IslaTraces.write_success_blocks.Index.lookup_a15694.
Qed.

Lemma writeSuccessWithdrawalsConcreteEntryOneStep machine view sp base total
    processed remaining bytes prefix suffix scratch :
  writeSuccessWithdrawalsConcreteEntry machine view sp base total processed
    remaining bytes prefix suffix scratch ->
  exists labels nextLocal nextGlobal spawned,
    seq_step machine.1 machine.2 labels nextLocal nextGlobal spawned.
Proof.
  intros (regs & global & -> & Hentry).
  eexists. eexists. eexists. eexists.
  eapply SeqStep.
  - reflexivity.
  - apply DeclareConstBitVecS' with (b := BV 64 0).
  - simpl. repeat split; reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsConcreteEntryReflects.
Print Assumptions writeSuccessWithdrawalsConcreteEntryBlockingRejected.
Print Assumptions writeSuccessWithdrawalsConcreteEntryOneStep.
Print Assumptions writeSuccessWithdrawalsConcreteEntryCode.

Definition writeSuccessWithdrawalsFirstResultRegs
    (regs : reg_map) (sp : bv 64) : reg_map :=
  <[ "PC" := RVal_Bits (Z_to_bv 64 0x15698) ]> $
  <[ "x10" := RVal_Bits (sp + BV 64 1744)%bv ]> regs.

Definition writeSuccessWithdrawalsFirstDone regs sp : seq_local_state := {|
  seq_trace := tnil;
  seq_regs := writeSuccessWithdrawalsFirstResultRegs regs sp;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccessWithdrawalsFirstAfter regs sp : seq_local_state := {|
  seq_trace := IslaTraces.write_success_90.a15698.a15698;
  seq_regs := writeSuccessWithdrawalsFirstResultRegs regs sp;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Lemma writeSuccessWithdrawalsFirstPrefix regs global (sp : bv 64) (oldX10 : valu)
    (Hpc : regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15694)))
    (Hsp : regs !! "x2" = Some (RVal_Bits sp))
    (Hx10 : regs !! "x10" = Some oldX10)
    (Hmstatus : eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption =
      Some (Val_Bool true)) :
  exists observations,
    IslaInstructionPrefixPath (writeSuccessWithdrawalsStart regs global)
      observations (writeSuccessWithdrawalsFirstDone regs sp, global).
Proof.
  eexists.
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with
      (b := BV 64 0)|]. simpl. repeat split; reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply SeqStep; [reflexivity|eapply AssumeS with (b := true)|].
    - exact Hmstatus.
    - simpl. repeat split; reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with
      (b := Z_to_bv 64 0x15694)|]. simpl. repeat split; reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply SeqStep; [reflexivity|constructor|].
    simpl. exists (RVal_Bits (Z_to_bv 64 0x15694)).
    exists (RVal_Bits (Z_to_bv 64 0x15694)).
    exists (RVal_Bits (Z_to_bv 64 0x15694)).
    rewrite Hpc. simpl. repeat split; try reflexivity. left. auto. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply SeqStep; [reflexivity|econstructor; reflexivity|].
    simpl. repeat split; reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with (b := sp)|].
    simpl. repeat split; reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply SeqStep; [reflexivity|constructor|].
    simpl. exists (RVal_Bits sp), (RVal_Bits sp), (RVal_Bits sp).
    rewrite Hsp. simpl. repeat split; try reflexivity. left. auto. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply SeqStep; [reflexivity|econstructor; reflexivity|].
    simpl. repeat split; reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply SeqStep; [reflexivity|constructor|].
    simpl. exists oldX10.
    exists (RVal_Bits (sp + BV 64 1744)%bv).
    exists (RVal_Bits (sp + BV 64 1744)%bv).
    rewrite Hx10. repeat split; try reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply SeqStep; [reflexivity|constructor|].
    simpl. exists (RVal_Bits (Z_to_bv 64 0x15694)).
    exists (RVal_Bits (Z_to_bv 64 0x15694 + BV 64 4)%bv).
    exists (RVal_Bits (Z_to_bv 64 0x15694 + BV 64 4)%bv).
    rewrite lookup_insert_ne; last done. rewrite Hpc. simpl. repeat split; try reflexivity. }
  assert (Hpcnext :
    (Z_to_bv 64 0x15694 + BV 64 4)%bv = Z_to_bv 64 0x15698)
    by bv_solve.
  rewrite Hpcnext. apply IslaInstructionPrefixRefl.
Qed.

Lemma writeSuccessWithdrawalsFirstDoneStep regs global (sp : bv 64)
    (Htable : writeSuccessWithdrawalsInstructionTable global) :
  seq_step (writeSuccessWithdrawalsFirstDone regs sp) global []
    (writeSuccessWithdrawalsFirstAfter regs sp) global [].
Proof.
  eapply (SeqStep _ _
    (Some (LDone IslaTraces.write_success_90.a15698.a15698))
    IslaTraces.write_success_90.a15698.a15698 None).
  - reflexivity.
  - constructor.
  - simpl. split; first reflexivity.
    exists (Z_to_bv 64 0x15698). split.
    + unfold writeSuccessWithdrawalsFirstResultRegs. apply lookup_insert.
    + rewrite (Htable 0x15698 IslaTraces.write_success_90.a15698.a15698
        (or_introl IslaTraces.write_success_blocks.Index.lookup_a15698)).
      simpl. repeat split; reflexivity.
Qed.

Lemma writeSuccessWithdrawalsFirstAfterBoundary regs global (sp : bv 64)
    (Htable : writeSuccessWithdrawalsInstructionTable global) :
  IslaInstructionBoundary
    (writeSuccessWithdrawalsFirstAfter regs sp, global).
Proof.
  split; first reflexivity.
  exists (Z_to_bv 64 0x15698),
    IslaTraces.write_success_90.a15698.a15698.
  split.
  - unfold writeSuccessWithdrawalsFirstResultRegs. apply lookup_insert.
  - split; last reflexivity.
    apply Htable. left. exact IslaTraces.write_success_blocks.Index.lookup_a15698.
Qed.

Lemma writeSuccessWithdrawalsFirstInstructionSegment regs global (sp : bv 64)
    (oldX10 : valu) (Htable : writeSuccessWithdrawalsInstructionTable global)
    (Hpc : regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15694)))
    (Hsp : regs !! "x2" = Some (RVal_Bits sp))
    (Hx10 : regs !! "x10" = Some oldX10)
    (Hmstatus : eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption =
      Some (Val_Bool true)) :
  exists observations,
    IslaInstructionSegment (writeSuccessWithdrawalsStart regs global)
      observations (writeSuccessWithdrawalsFirstAfter regs sp, global).
Proof.
  destruct (writeSuccessWithdrawalsFirstPrefix regs global sp oldX10 Hpc Hsp Hx10 Hmstatus)
    as [prefix Hprefix].
  exists (prefix ++
    (({| microLabels := [];
         microAfter := (writeSuccessWithdrawalsFirstAfter regs sp, global) |})
      :: [])).
  eapply Build_IslaInstructionSegment
    with (instructionSegmentDoneSource :=
      (writeSuccessWithdrawalsFirstDone regs sp, global))
    (instructionSegmentPrefix := prefix)
    (instructionSegmentLabels := [])
    (instructionSegmentSpawned := []).
  - split; first reflexivity.
    exists (Z_to_bv 64 0x15694),
      IslaTraces.write_success_90.a15694.a15694.
    split; first exact Hpc. split; last reflexivity.
    apply Htable. left. exact IslaTraces.write_success_blocks.Index.lookup_a15694.
  - exact Hprefix.
  - reflexivity.
  - apply writeSuccessWithdrawalsFirstDoneStep. exact Htable.
  - reflexivity.
  - left. apply writeSuccessWithdrawalsFirstAfterBoundary. exact Htable.
Qed.

Lemma writeSuccessWithdrawalsConcreteEntryFirstInstruction machine view sp base
    total processed remaining bytes prefix suffix scratch :
  writeSuccessWithdrawalsConcreteEntry machine view sp base total processed
    remaining bytes prefix suffix scratch ->
  exists observations after,
    IslaInstructionSegment machine observations after.
Proof.
  intros (regs & global & -> & Htable & Hpc & Hsp & Hx10 & Hpointer & Hcount &
    Hx18 & Hmstatus & Harchitecture & Hregisters & Hrest).
  destruct Hx10 as [oldX10 Hx10].
  destruct (writeSuccessWithdrawalsFirstInstructionSegment regs global sp
    oldX10 Htable Hpc Hsp Hx10 Hmstatus) as [observations Hsegment].
  exists observations, (writeSuccessWithdrawalsFirstAfter regs sp, global).
  exact Hsegment.
Qed.

Lemma writeSuccessWithdrawalsConcreteEntryRunOne machine view sp base total
    processed remaining bytes prefix suffix scratch :
  writeSuccessWithdrawalsConcreteEntry machine view sp base total processed
    remaining bytes prefix suffix scratch ->
  exists segments after,
    IslaInstructionRun 1 machine segments after.
Proof.
  intros Hentry.
  destruct (writeSuccessWithdrawalsConcreteEntryFirstInstruction machine view sp
    base total processed remaining bytes prefix suffix scratch Hentry)
    as (observations & after & Hsegment).
  exists [observations], after.
  econstructor; first exact Hsegment. constructor.
Qed.

Print Assumptions writeSuccessWithdrawalsFirstPrefix.
Print Assumptions writeSuccessWithdrawalsFirstInstructionSegment.
Print Assumptions writeSuccessWithdrawalsConcreteEntryFirstInstruction.
Print Assumptions writeSuccessWithdrawalsConcreteEntryRunOne.

Lemma writeSuccessWithdrawalsFirstInstructionCanBlock regs global
    (Hpc : regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15694)))
    (Hmstatus : eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption =
      Some (Val_Bool true)) :
  exists observations blockedLocal,
    IslaInstructionPrefixPath (writeSuccessWithdrawalsStart regs global)
      observations (blockedLocal, global) /\
    blockedLocal.(seq_nb_state) = true.
Proof.
  eexists. eexists. split.
  - eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with
        (b := BV 64 0)|]. simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|eapply AssumeS with (b := true)|].
      - exact Hmstatus.
      - simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with
        (b := Z_to_bv 64 0x15694)|]. simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists (RVal_Bits (Z_to_bv 64 0x15694)).
      exists (RVal_Bits (Z_to_bv 64 0x15694)).
      exists (RVal_Bits (Z_to_bv 64 0x15694)).
      rewrite Hpc. simpl. repeat split; try reflexivity. right. reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
Qed.

Lemma writeSuccessWithdrawalsConcreteEntryCanBlock machine view sp base total
    processed remaining bytes prefix suffix scratch :
  writeSuccessWithdrawalsConcreteEntry machine view sp base total processed
    remaining bytes prefix suffix scratch ->
  exists observations blockedLocal,
    IslaInstructionPrefixPath machine observations (blockedLocal, machine.2) /\
    blockedLocal.(seq_nb_state) = true.
Proof.
  intros (regs & global & -> & Htable & Hpc & Hsp & Hx10 & Hpointer & Hcount &
    Hx18 & Hmstatus & Harchitecture & Hregisters & Hrest).
  exact (writeSuccessWithdrawalsFirstInstructionCanBlock regs global Hpc Hmstatus).
Qed.

Lemma writeSuccessWithdrawalsBlockedPrefixCannotComplete machine observations
    blockedLocal global :
  IslaInstructionPrefixPath machine observations (blockedLocal, global) ->
  blockedLocal.(seq_nb_state) = true ->
  forall tailObservations after,
    tailObservations <> [] ->
    ~ IslaInstructionPrefixPath (blockedLocal, global) tailObservations after.
Proof.
  intros Hprefix Hblocked tailObservations after Hnonempty Htail.
  inversion Htail; subst.
  - contradiction.
  - eapply seqStepFromNonblockingImpossible; eauto.
Qed.

Print Assumptions writeSuccessWithdrawalsFirstInstructionCanBlock.
Print Assumptions writeSuccessWithdrawalsConcreteEntryCanBlock.
Print Assumptions writeSuccessWithdrawalsBlockedPrefixCannotComplete.

Lemma writeSuccessWithdrawalsMstatusInsert regs register value
    (Hregister : register <> "mstatus") :
  eval_a_exp (<[register := value]> regs)
    writeSuccessWithdrawalsMstatusAssumption =
  eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption.
Proof.
  unfold writeSuccessWithdrawalsMstatusAssumption.
  cbn. rewrite lookup_insert_ne; done.
Qed.

Lemma writeSuccessWithdrawalsMstatusAfterFirst regs sp :
  eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption =
    Some (Val_Bool true) ->
  eval_a_exp (writeSuccessWithdrawalsFirstResultRegs regs sp)
    writeSuccessWithdrawalsMstatusAssumption = Some (Val_Bool true).
Proof.
  intro Hmstatus. unfold writeSuccessWithdrawalsFirstResultRegs.
  rewrite !writeSuccessWithdrawalsMstatusInsert; done.
Qed.

Definition writeSuccessWithdrawalsSecondResultRegs regs sp : reg_map :=
  <[ "PC" := RVal_Bits (Z_to_bv 64 0x1569c) ]> $
  <[ "x12" := RVal_Bits (BV 64 48) ]> $
  writeSuccessWithdrawalsFirstResultRegs regs sp.

Definition writeSuccessWithdrawalsSecondDone regs sp : seq_local_state := {|
  seq_trace := tnil;
  seq_regs := writeSuccessWithdrawalsSecondResultRegs regs sp;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccessWithdrawalsSecondAfter regs sp : seq_local_state := {|
  seq_trace := IslaTraces.write_success_90.a1569c.a1569c;
  seq_regs := writeSuccessWithdrawalsSecondResultRegs regs sp;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Lemma writeSuccessWithdrawalsSecondInstructionSegment regs global sp oldX12
    (Htable : writeSuccessWithdrawalsInstructionTable global)
    (Hx12 : regs !! "x12" = Some oldX12)
    (Hmstatus : eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption =
      Some (Val_Bool true)) :
  exists observations,
    IslaInstructionSegment (writeSuccessWithdrawalsFirstAfter regs sp, global)
      observations (writeSuccessWithdrawalsSecondAfter regs sp, global).
Proof.
  assert (Hpc : (writeSuccessWithdrawalsFirstResultRegs regs sp) !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x15698))).
  { unfold writeSuccessWithdrawalsFirstResultRegs. apply lookup_insert. }
  assert (Hx12' : (writeSuccessWithdrawalsFirstResultRegs regs sp) !! "x12" =
      Some oldX12).
  { unfold writeSuccessWithdrawalsFirstResultRegs.
    rewrite !lookup_insert_ne; done. }
  assert (Hmstatus' := writeSuccessWithdrawalsMstatusAfterFirst regs sp Hmstatus).
  eexists.
  eapply Build_IslaInstructionSegment with
    (instructionSegmentDoneSource :=
      (writeSuccessWithdrawalsSecondDone regs sp, global))
    (instructionSegmentLabels := []) (instructionSegmentSpawned := []).
  - apply writeSuccessWithdrawalsFirstAfterBoundary. exact Htable.
  - eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with
        (b := BV 64 0)|]. simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|eapply AssumeS with (b := true)|].
      - exact Hmstatus'.
      - simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with
        (b := Z_to_bv 64 0x15698)|]. simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists (RVal_Bits (Z_to_bv 64 0x15698)).
      exists (RVal_Bits (Z_to_bv 64 0x15698)).
      exists (RVal_Bits (Z_to_bv 64 0x15698)).
      rewrite Hpc. simpl. repeat split; try reflexivity. left. auto. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|econstructor; reflexivity|].
      simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists oldX12, (RVal_Bits (BV 64 48)),
        (RVal_Bits (BV 64 48)).
      rewrite Hx12'. repeat split; try reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists (RVal_Bits (Z_to_bv 64 0x15698)).
      exists (RVal_Bits (Z_to_bv 64 0x15698 + BV 64 4)%bv).
      exists (RVal_Bits (Z_to_bv 64 0x15698 + BV 64 4)%bv).
      rewrite lookup_insert_ne; last done. rewrite Hpc.
      simpl. repeat split; try reflexivity. }
    assert (Hpcnext :
      (Z_to_bv 64 0x15698 + BV 64 4)%bv = Z_to_bv 64 0x1569c)
      by bv_solve.
    rewrite Hpcnext. apply IslaInstructionPrefixRefl.
  - reflexivity.
  - eapply (SeqStep _ _
      (Some (LDone IslaTraces.write_success_90.a1569c.a1569c))
      IslaTraces.write_success_90.a1569c.a1569c None).
    + reflexivity.
    + constructor.
    + simpl. split; first reflexivity.
      exists (Z_to_bv 64 0x1569c). split.
      * unfold writeSuccessWithdrawalsSecondResultRegs. apply lookup_insert.
      * rewrite (Htable 0x1569c IslaTraces.write_success_90.a1569c.a1569c
          (or_introl IslaTraces.write_success_blocks.Index.lookup_a1569c)).
        simpl. repeat split; reflexivity.
  - reflexivity.
  - left. split; first reflexivity.
    exists (Z_to_bv 64 0x1569c), IslaTraces.write_success_90.a1569c.a1569c.
    split.
    + unfold writeSuccessWithdrawalsSecondResultRegs. apply lookup_insert.
    + split; last reflexivity. apply Htable. left.
      exact IslaTraces.write_success_blocks.Index.lookup_a1569c.
Qed.

Print Assumptions writeSuccessWithdrawalsMstatusAfterFirst.
Print Assumptions writeSuccessWithdrawalsSecondInstructionSegment.

Lemma writeSuccessWithdrawalsConcreteEntryRunTwo machine view sp base total
    processed remaining bytes prefix suffix scratch :
  writeSuccessWithdrawalsConcreteEntry machine view sp base total processed
    remaining bytes prefix suffix scratch ->
  exists segments after,
    IslaInstructionRun 2 machine segments after.
Proof.
  intros Hentry.
  destruct Hentry as
    (regs & global & Hmachine & Htable & Hpc & Hsp & Hx10 & Hpointer &
     Hcount & Hx18 & Hmstatus & Harchitecture & Hregisters & Hrest).
  subst machine. destruct Hx10 as [oldX10 Hx10].
  destruct (Hregisters "x12") as [x12 Hx12]; first (cbn; tauto).
  destruct (writeSuccessWithdrawalsFirstInstructionSegment regs global sp
    oldX10 Htable Hpc Hsp Hx10 Hmstatus) as [first Hfirst].
  destruct (writeSuccessWithdrawalsSecondInstructionSegment regs global sp
    (RVal_Bits x12) Htable Hx12 Hmstatus) as [second Hsecond].
  exists [first; second], (writeSuccessWithdrawalsSecondAfter regs sp, global).
  econstructor; first exact Hfirst.
  econstructor; first exact Hsecond. constructor.
Qed.

Print Assumptions writeSuccessWithdrawalsConcreteEntryRunTwo.

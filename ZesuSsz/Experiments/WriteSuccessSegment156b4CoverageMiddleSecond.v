From Coq Require Import Eqdep_dec Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4CoverageMiddleUpper.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4CoverageMiddlePc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4CoverageMiddleAddress.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4CoverageMiddleMstatus.

Definition writeSuccess156b4MiddleSecondObservations regs global
    mstatusBits address :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess156b4TraceUpper mstatusBits address;
     writeSuccess156b4Trace16 mstatusBits address;
     writeSuccess156b4Trace17 mstatusBits address;
     writeSuccess156b4Trace18 mstatusBits address;
     writeSuccess156b4Trace19 mstatusBits address;
     writeSuccess156b4Trace20 mstatusBits address;
     writeSuccess156b4Trace21 mstatusBits address].

Lemma segment_156b4_middle_second_covered regs global
    (declMstatus declAddress actualMstatus actualAddress : bv 64)
    prefix15 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b4)) ->
  regs !! "x2" = Some (RVal_Bits actualAddress) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits actualMstatus)]) ->
  eval_a_exp regs writeSuccess156b4Upper = Some (Val_Bool true) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess156b4Trace15 declMstatus declAddress) regs, global)
    prefix15 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  declMstatus = actualMstatus /\
  declAddress = actualAddress /\
  exists prefix21,
    IslaInstructionPrefixPath
      (writeSuccess15694Local
        (writeSuccess156b4Trace21 actualMstatus actualAddress) regs, global)
      prefix21 done /\
    prefix15 = writeSuccess156b4MiddleSecondObservations regs global
      actualMstatus actualAddress ++ prefix21.
Proof.
  intros Hpc Hx2 Hmstatus Hupper Hprefix Hnil Hdone.
  destruct (segment_156b4_middle_upper_covered regs global declMstatus declAddress
    prefix15 done labels spawned after Hupper Hprefix Hnil Hdone) as
    (prefixUpper & HpUpper & HobsUpper).
  destruct (segment_156b4_middle_pc_covered regs global declMstatus declAddress
    prefixUpper done labels spawned after Hpc HpUpper Hnil Hdone) as
    (prefix17 & Hp17 & HobsPc).
  destruct (segment_156b4_middle_address_covered regs global declMstatus
    declAddress actualAddress prefix17 done labels spawned after Hx2 Hp17 Hnil Hdone) as
    (Haddress & prefix20 & Hp20 & HobsAddress).
  subst declAddress.
  destruct (segment_156b4_middle_mstatus_covered regs global declMstatus
    actualMstatus actualAddress prefix20 done labels spawned after Hmstatus Hp20 Hnil Hdone) as
    (HmstatusEq & prefix21 & Hp21 & HobsMstatus).
  subst declMstatus. repeat split; try reflexivity. exists prefix21.
  split; first exact Hp21. rewrite HobsUpper HobsPc HobsAddress HobsMstatus.
  unfold writeSuccess156b4MiddleSecondObservations. cbn. reflexivity.

Qed.

Print Assumptions segment_156b4_middle_second_covered.

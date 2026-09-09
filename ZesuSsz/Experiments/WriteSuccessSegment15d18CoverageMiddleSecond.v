From Coq Require Import Eqdep_dec Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18CoverageMiddleUpper.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18CoverageMiddlePc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18CoverageMiddleAddress.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18CoverageMiddleMstatus.

Definition writeSuccess15d18MiddleSecondObservations regs global
    mstatusBits address :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess15d18TraceUpper mstatusBits address;
     writeSuccess15d18Trace16 mstatusBits address;
     writeSuccess15d18Trace17 mstatusBits address;
     writeSuccess15d18Trace18 mstatusBits address;
     writeSuccess15d18Trace19 mstatusBits address;
     writeSuccess15d18Trace20 mstatusBits address;
     writeSuccess15d18Trace21 mstatusBits address].

Lemma segment_15d18_middle_second_covered regs global
    (declMstatus declAddress actualMstatus actualAddress : bv 64)
    prefix15 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d18)) ->
  regs !! "x2" = Some (RVal_Bits actualAddress) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits actualMstatus)]) ->
  eval_a_exp regs writeSuccess15d18Upper = Some (Val_Bool true) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess15d18Trace15 declMstatus declAddress) regs, global)
    prefix15 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  declMstatus = actualMstatus /\
  declAddress = actualAddress /\
  exists prefix21,
    IslaInstructionPrefixPath
      (writeSuccess15694Local
        (writeSuccess15d18Trace21 actualMstatus actualAddress) regs, global)
      prefix21 done /\
    prefix15 = writeSuccess15d18MiddleSecondObservations regs global
      actualMstatus actualAddress ++ prefix21.
Proof.
  intros Hpc Hx2 Hmstatus Hupper Hprefix Hnil Hdone.
  destruct (segment_15d18_middle_upper_covered regs global declMstatus declAddress
    prefix15 done labels spawned after Hupper Hprefix Hnil Hdone) as
    (prefixUpper & HpUpper & HobsUpper).
  destruct (segment_15d18_middle_pc_covered regs global declMstatus declAddress
    prefixUpper done labels spawned after Hpc HpUpper Hnil Hdone) as
    (prefix17 & Hp17 & HobsPc).
  destruct (segment_15d18_middle_address_covered regs global declMstatus
    declAddress actualAddress prefix17 done labels spawned after Hx2 Hp17 Hnil Hdone) as
    (Haddress & prefix20 & Hp20 & HobsAddress).
  subst declAddress.
  destruct (segment_15d18_middle_mstatus_covered regs global declMstatus
    actualMstatus actualAddress prefix20 done labels spawned after Hmstatus Hp20 Hnil Hdone) as
    (HmstatusEq & prefix21 & Hp21 & HobsMstatus).
  subst declMstatus. repeat split; try reflexivity. exists prefix21.
  split; first exact Hp21. rewrite HobsUpper HobsPc HobsAddress HobsMstatus.
  unfold writeSuccess15d18MiddleSecondObservations. cbn. reflexivity.

Qed.

Print Assumptions segment_15d18_middle_second_covered.

Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.DecodeHeap.
Require Import ZesuSsz.Proofs.Main.PrefixToDecodeEntry.
Require Import ZesuSsz.Proofs.Main.SuccessOutcome.
Require Import ZesuSsz.Proofs.Main.FailureAfterConcreteDecode.
Require Import ZesuSsz.Proofs.Main.SuccessResources.
Require Import ZesuSsz.Proofs.Main.SuccessFinish.
Require Import ZesuSsz.Proofs.Main.FailureAfterDecode.
Require Import ZesuSsz.Proofs.Main.DecodeTail.
Require Import ZesuSsz.Proofs.Main.Dispatch.
Require Import ZesuSsz.Proofs.Main.OutcomeCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.
Require Import ZesuSsz.Proofs.ZkvmExit.TraceContract.

Definition MainTerminalOutcome : Type :=
 (DecodeBoundaryOutcome WriteSuccessObservation * ByteString)%type.
Definition mainWholeAllows
 (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
 (writeAllows : WriteSuccessArgs WriteSuccessObservation -> ByteString -> Prop)
 (args : DecodeBoundaryArgs) (outcome : MainTerminalOutcome) : Prop :=
 allows args outcome.1 /\
 match outcome.1 with
 | DecodeBoundaryFailure => outcome.2 = failureObservation
 | DecodeBoundarySuccess observation => writeAllows (mainWriterArgs args observation) outcome.2
 end.
Definition mainConcreteDecodeModel
 (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
 (decodeTail successExitTail : DecodeBoundaryArgs -> spec) :
 IslarisContractModel DecodeBoundaryArgs (DecodeBoundaryOutcome WriteSuccessObservation) := {|
 islarisContractAllows := allows;
 islarisContractStep := fun _ nextPc => nextPc = 0x14cfc;
 islarisContractResources := fun Sigma HG HT =>
  @mainDecodeConcreteResources Sigma HG HT decodeTail successExitTail
|}.
Definition mainSuccessOutcomeCode `{!islaG Sigma} `{!threadG} (tail : spec) : iProp Sigma :=
 (([∗ list] i ∈ mainDispatchInstrs, instr i.1 (Some i.2)) ∗
  ([∗ list] i ∈ main_write_success_instrs, instr i.1 (Some i.2)) ∗
  writeSuccessNativeCode ∗
  ([∗ list] i ∈ main_success_exit_instrs, instr i.1 (Some i.2)) ∗
  islarisCode _ _ (zkvmExitTailResources tail True%I))%I.
Definition mainWholeResources `{!islaG Sigma} `{!threadG}
 (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
 (outputRelation : WriteSuccessOutputRelation WriteSuccessObservation) (tail : spec)
 (a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13 : bv 64) :
 IslarisContractResources DecodeBoundaryArgs MainTerminalOutcome := {|
 islarisCode :=
  (islarisCode _ _ (mainToDecodeEntryResources
    (mainDecodeUnionTail allows
     (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
     (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail))
    (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
    a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13) ∗
   mainSuccessOutcomeCode tail ∗
   islarisCode _ _ (mainFailureAfterDecodeResources tail
    (BV 64 0) (BV 64 0x14cfc) (BV 16 1) True%I))%I;
 islarisEntry := islarisEntry _ _ (mainToDecodeEntryResources
   (mainDecodeUnionTail allows
    (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
    (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail))
   (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
   a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13);
 islarisExit := fun args outcome =>
  match outcome.1 with
  | DecodeBoundarySuccess observation =>
    islarisExit _ _ (mainSuccessOutcomeResources allows outputRelation tail args observation)
     tt outcome.2
  | DecodeBoundaryFailure =>
    (⌜outcome.2 = failureObservation⌝ ∗
     islarisExit _ _ (mainFailureAfterConcreteDecodeResources allows
      (fun _ => scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
      tail args) tt tt)%I
  end
|}.

Definition mainWholeModel
 (allows : DecodeBoundaryArgs -> DecodeBoundaryOutcome WriteSuccessObservation -> Prop)
 (writeAllows : WriteSuccessArgs WriteSuccessObservation -> ByteString -> Prop)
 (outputRelation : WriteSuccessOutputRelation WriteSuccessObservation) (tail : spec)
 (a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13 : bv 64) :
 IslarisContractModel DecodeBoundaryArgs MainTerminalOutcome := {|
 islarisContractAllows := mainWholeAllows allows writeAllows;
 islarisContractStep := fun _ nextPc => nextPc = 0x101d0;
 islarisContractResources := fun Sigma HG HT =>
  @mainWholeResources Sigma HG HT allows outputRelation tail
   a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13
|}.

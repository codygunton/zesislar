Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Lookup.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Remove Hints subsume_instr_pre_zesu_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessSuffixRootOtherRegisters : list string :=
  ["x3"; "x4"; "x6"; "x7"; "x8"; "x9";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x18"; "x19";
   "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessSuffixRootFrame `{!islaG Sigma} `{!threadG}
    (sp root : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      writeSuccessSuffixRootOtherRegisters) ∗
   (bv_unsigned sp + 1000) ↦ₘ root ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixRootFrame) := I.

Definition writeSuccessSuffixAt1572c `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp root oldData oldSize : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x1572c) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
    "x10" ↦ᵣ RVal_Bits oldData ∗
    "x11" ↦ᵣ RVal_Bits oldSize ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeOutputEventsAny (sp + BV 64 1000)%bv (BV 64 32) tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
    writeSuccessSuffixRootFrame sp root P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixAt1572c) := I.

Definition writeSuccessSuffixAt1573c `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp root : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
    writeSuccessSuffixRootFrame sp root P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixAt1573c) := I.

Ltac run_write_success_suffix_root :=
  lazymatch goal with
  | |- instr_body 0x1573c _ => idtac
  | _ =>
      first
        [ progress iEval (unfold zesuWriteOutputCallSpec, zesu_c_call)
        | liAStep
        | progress prepare_sidecond
        | reflexivity
        | vm_compute
        | bv_solve
        | lia ];
      run_write_success_suffix_root
  end.

Lemma write_success_suffix_root_output
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x1573c (writeSuccessSuffixAt1573c P) -∗
  instr_body 0x1572c (writeSuccessSuffixAt1572c P).
Proof.
  move => *.
  iStartProof. iIntros "_ #Hlookup #Hcode #Houtput Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try iExists (tail, 0x1573c, sp, root, tt)ₗ.
  all: try cbn.
  all: try unLET.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  all: try liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try bv_solve.
  all: try lia.
  all: iSplit; last done.
  all: iIntros "Hpost".
  all: iDestruct "Hpost" as
    "(Hsys & Htmp & Hsaved & H10 & H11 & H2 & Hstack & Hmmio & Htrace & _)".
  all: iEval (rewrite /writeSuccessSuffixAt1573c).
  all: iExists sp, root, tail.
  all: iFrame.
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
  Unshelve.
  all: lazymatch goal with |- ?G => fail "suffix root residual" G end.
Qed.

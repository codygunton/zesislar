Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessSuffixBytesOtherRegisters : list string :=
  ["x3"; "x4"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
   "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessSuffixBytes158f0Frame `{!islaG Sigma} `{!threadG}
    (sp data size : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) :
    iProp Sigma :=
  (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      writeSuccessSuffixBytesOtherRegisters) ∗
   (bv_unsigned sp + 936) ↦ₘ data ∗
   (bv_unsigned sp + 944) ↦ₘ size ∗
   P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytes158f0Frame) := I.

Definition writeSuccessSuffixAt158f0 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits oldS0 ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEventsAny data size tail)) ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
    writeSuccessSuffixBytes158f0Frame sp data size bytes P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixAt158f0) := I.

Definition writeSuccessSuffixAt15900 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15900) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits oldS0 ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
    writeSuccessSuffixBytes158f0Frame sp data size bytes P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixAt15900) := I.

Lemma write_success_suffix_bytes_158f0
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x15900 (writeSuccessSuffixAt15900 P) -∗
  instr_body 0x158f0 (writeSuccessSuffixAt158f0 P).
Proof.
  move => *.
  iStartProof. iIntros "_ #Hlookup #Hcode #Hbytes Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve. all: try prepare_sidecond.
  all: try assumption.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try iExists
    (tail, bytes, 0x15900, oldS1, oldS0, sp, size, data, tt)ₗ.
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
  all: iEval (rewrite /writeSuccessSuffixAt15900).
  all: iEval (rewrite /writeSuccessSuffixBytes158f0Frame).
  all: iExists sp, data, size, oldS0, oldS1, bytes, tail.
  all: iFrame.
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
  Unshelve.
  all: iSplit; last done.
  all: iIntros "Hpost".
  all: iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack & Hdata &
      Hmmio & Htrace & _)".
  all: iEval (rewrite /writeSuccessSuffixAt15900).
  all: iEval (rewrite /writeSuccessSuffixBytes158f0Frame).
  all: iExists sp, data, size, oldS0, oldS1, bytes, tail.
  all: iFrame.
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
  Unshelve.
  all: have Hreturn : Z_to_bv 64 88320 = BV 64 88320 by bv_solve.
  all: rewrite -Hreturn.
  all: try iRename select (_ ↦ₘ data)%I into "HdescData".
  all: try iRename select (_ ↦ₘ size)%I into "HdescSize".
  all: have Haddr936 :
    bv_unsigned (sp + BV 64 936)%bv = bv_unsigned sp + 936 by bv_solve.
  all: have Haddr944 :
    bv_unsigned (sp + BV 64 944)%bv = bv_unsigned sp + 944 by bv_solve.
  all: iEval (rewrite Haddr936) in "HdescData".
  all: iEval (rewrite Haddr944) in "HdescSize".
  all: rewrite /reg_col; cbn.
  all: iFrame "HdescData HdescSize".
  all: iFrame.
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
  Unshelve.
  all: lazymatch goal with |- ?G => fail "suffix bytes residual" G end.
Qed.

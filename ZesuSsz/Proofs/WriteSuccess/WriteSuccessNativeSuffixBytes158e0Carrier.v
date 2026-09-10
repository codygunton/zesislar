From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessSuffixBytes158e0CarrierFrame `{!islaG Sigma} `{!threadG}
    (sp data size : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) :
    iProp Sigma :=
  (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      ["x3"; "x4"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
       "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
       "x26"; "x27"; "x28"; "x29"; "x30"; "x31"]) ∗
   (bv_unsigned sp + 920) ↦ₘ data ∗
   (bv_unsigned sp + 928) ↦ₘ size ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytes158e0CarrierFrame) := I.

Definition writeSuccessSuffixBytesAt158e0Carrier `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (data size oldS0 oldS1 : bv 64) (bytes : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits oldS0 ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents data size tail)) ∗
    bv_unsigned data ↦ₘ∗ bytes ∗ ⌜bv_unsigned size = length bytes⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
    writeSuccessSuffixBytes158e0CarrierFrame sp data size bytes P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt158e0Carrier) := I.

Definition writeSuccessSuffixBytesAt158f0Carrier `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (data size oldS0 oldS1 : bv 64) (bytes : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x158f0) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits oldS0 ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗ bv_unsigned data ↦ₘ∗ bytes ∗
    mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
    writeSuccessSuffixBytes158e0CarrierFrame sp data size bytes P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt158f0Carrier) := I.

Definition writeSuccessSuffixBytesAt158e0CarrierData `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
    (trace : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x8" ↦ᵣ RVal_Bits oldS0 ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
   "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace
     (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
       (writeOutputEvents data size trace)) ∗
   bv_unsigned data ↦ₘ∗ bytes ∗ ⌜bv_unsigned size = length bytes⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < 0x40000000⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x3"; "x4"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
      "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
      "x26"; "x27"; "x28"; "x29"; "x30"; "x31"]) ∗
   (bv_unsigned sp + 920) ↦ₘ data ∗
   (bv_unsigned sp + 928) ↦ₘ size ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt158e0CarrierData) := I.

Definition writeSuccessSuffixBytesAt158f0CarrierExactData `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
    (trace : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x158f0) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x8" ↦ᵣ RVal_Bits oldS0 ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
   "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace trace ∗ bv_unsigned data ↦ₘ∗ bytes ∗
   ⌜bv_unsigned size = length bytes⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < 0x40000000⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x3"; "x4"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
      "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
      "x26"; "x27"; "x28"; "x29"; "x30"; "x31"]) ∗
   (bv_unsigned sp + 920) ↦ₘ data ∗
   (bv_unsigned sp + (920 + 8)) ↦ₘ size ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt158f0CarrierExactData) := I.

Lemma write_success_suffix_bytes_158e0_carrier
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (P : iProp Sigma)
    (data size oldS0 oldS1 : bv 64) (bytes : list (bv 8)) (trace : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x158f0
    (writeSuccessSuffixBytesAt158f0CarrierExactData sp data size oldS0 oldS1
      bytes trace P) -∗
  instr_body 0x158e0
    (writeSuccessSuffixBytesAt158e0CarrierData sp data size oldS0 oldS1 bytes
      trace P).
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
  all: iExists
    (trace, bytes, 0x158f0, oldS1, oldS0, sp, size, data, tt)ₗ.
  all: try cbn.
  all: try unLET.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  all: try liARun.
  Unshelve. all: try prepare_sidecond.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try bv_solve.
  all: try lia.
  all: iSplit; last done.
  all: iIntros "Hpost".
  all: iEval (rewrite /writeSuccessSuffixBytesAt158e0CarrierData).
  all: iFrame.
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
  Unshelve.
  all: try iExists
    (trace, bytes, 0x158f0, oldS1, oldS0, sp, size, data, tt)ₗ.
  all: try cbn.
  all: try unLET.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  all: try liARun.
  all: have Hreturn : Z_to_bv 64 88304 = BV 64 88304 by bv_solve.
  all: try rewrite -Hreturn.
  all: try iRename select (_ ↦ₘ data)%I into "HdescData".
  all: try iRename select (_ ↦ₘ size)%I into "HdescSize".
  all: have Haddr920 :
    bv_unsigned (sp + BV 64 920)%bv = bv_unsigned sp + 920 by bv_solve.
  all: have Haddr928 :
    bv_unsigned (sp + BV 64 928)%bv = bv_unsigned sp + 928 by bv_solve.
  all: iEval (rewrite Haddr920) in "HdescData".
  all: iEval (rewrite Haddr928) in "HdescSize".
  all: rewrite /reg_col; cbn.
  all: iFrame "HdescData HdescSize".
  all: iFrame.
  Unshelve. all: try prepare_sidecond.
  all: try bv_solve.
Qed.

Definition writeSuccessSuffixBytesCarrierShapeReg `{!islaG Sigma} `{!threadG}
    (r : string) : iProp Sigma :=
  r ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝).

Definition writeSuccessSuffixBytesCarrierExactReg `{!islaG Sigma} `{!threadG}
    (r : string) (v : bv 64) : iProp Sigma :=
  r ↦ᵣ RVal_Bits v.

Definition writeSuccessSuffixBytesCarrierState `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (x1 x5 x6 : iProp Sigma)
    (x10 x11 : bv 64 -> iProp Sigma)
    (event : bv 64 -> bv 64 -> spec -> spec) (offset : Z)
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (data size oldS0 oldS1 : bv 64) (bytes : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗ x1 ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ x5 ∗ x6 ∗
    "x8" ↦ᵣ RVal_Bits oldS0 ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
    (x10 data) ∗ (x11 size) ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
    spec_trace (event data size tail) ∗ bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      ["x3"; "x4"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
       "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
       "x26"; "x27"; "x28"; "x29"; "x30"; "x31"]) ∗
    (bv_unsigned sp + offset) ↦ₘ data ∗
    (bv_unsigned sp + (offset + 8)) ↦ₘ size ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytesCarrierState) := I.

Definition writeSuccessSuffixBytesCarrierExactState `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
    (trace : spec) (x1 x5 x6 : iProp Sigma) (offset : Z) (P : iProp Sigma) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ x1 ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ x5 ∗ x6 ∗
   "x8" ↦ᵣ RVal_Bits oldS0 ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
   "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace trace ∗ bv_unsigned data ↦ₘ∗ bytes ∗
   ⌜bv_unsigned size = length bytes⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < 0x40000000⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x3"; "x4"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
      "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
      "x26"; "x27"; "x28"; "x29"; "x30"; "x31"]) ∗
   (bv_unsigned sp + offset) ↦ₘ data ∗
   (bv_unsigned sp + (offset + 8)) ↦ₘ size ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytesCarrierExactState) := I.

Definition writeSuccessSuffixBytesCarrierDataState `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
    (trace : spec) (x1 x5 x6 : iProp Sigma)
    (x10 x11 : bv 64 -> iProp Sigma) (offset : Z) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ x1 ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ x5 ∗ x6 ∗
   "x8" ↦ᵣ RVal_Bits oldS0 ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
   (x10 data) ∗ (x11 size) ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace trace ∗ bv_unsigned data ↦ₘ∗ bytes ∗
   ⌜bv_unsigned size = length bytes⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < 0x40000000⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x3"; "x4"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
      "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
      "x26"; "x27"; "x28"; "x29"; "x30"; "x31"]) ∗
   (bv_unsigned sp + offset) ↦ₘ data ∗
   (bv_unsigned sp + (offset + 8)) ↦ₘ size ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytesCarrierDataState) := I.

Definition writeSuccessSuffixBytesAt15900CarrierData `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
    (trace : spec) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierDataState sp data size oldS0 oldS1 bytes trace
    (writeSuccessSuffixBytesCarrierShapeReg "x1")
    (writeSuccessSuffixBytesCarrierShapeReg "x5")
    (writeSuccessSuffixBytesCarrierShapeReg "x6")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x10")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x11") 936 P.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15900CarrierData) := I.

Definition writeSuccessSuffixBytesAt158f0CarrierData `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
    (trace : spec) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierDataState sp data size oldS0 oldS1 bytes trace
    (writeSuccessSuffixBytesCarrierExactReg "x1" (BV 64 0x158f0))
    (writeSuccessSuffixBytesCarrierExactReg "x5" (BV 64 0x2401a0b8))
    (writeSuccessSuffixBytesCarrierShapeReg "x6")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x10")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x11") 920 P.

Definition writeSuccessSuffixBytesAt15910CarrierData `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
    (trace : spec) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierDataState sp data size oldS0 oldS1 bytes trace
    (writeSuccessSuffixBytesCarrierShapeReg "x1")
    (writeSuccessSuffixBytesCarrierShapeReg "x5")
    (writeSuccessSuffixBytesCarrierShapeReg "x6")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x10")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x11") 952 P.

Definition writeSuccessSuffixBytesAt15920CarrierData `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
    (trace : spec) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierDataState sp data size oldS0 oldS1 bytes trace
    (writeSuccessSuffixBytesCarrierShapeReg "x1")
    (writeSuccessSuffixBytesCarrierShapeReg "x5")
    (writeSuccessSuffixBytesCarrierShapeReg "x6")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x10")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x11") 968 P.

Definition writeSuccessSuffixBytesAt15930CarrierData `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
    (trace : spec) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierDataState sp data size oldS0 oldS1 bytes trace
    (writeSuccessSuffixBytesCarrierExactReg "x1" (BV 64 0x15930))
    (writeSuccessSuffixBytesCarrierExactReg "x5" (BV 64 0x2401a0b8))
    (writeSuccessSuffixBytesCarrierShapeReg "x6")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x10")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x11") 984 P.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt158f0CarrierData) := I.
Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15910CarrierData) := I.
Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15920CarrierData) := I.
Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15930CarrierData) := I.

Definition writeSuccessSuffixBytesAt15900CarrierExactData `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
    (trace : spec) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierExactState sp data size oldS0 oldS1 bytes trace
    (writeSuccessSuffixBytesCarrierExactReg "x1" (BV 64 0x15900))
    (writeSuccessSuffixBytesCarrierExactReg "x5" (BV 64 0x2401a0b8))
    (writeSuccessSuffixBytesCarrierShapeReg "x6") 936 P.

Definition writeSuccessSuffixBytesAt15910CarrierExactData `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
    (trace : spec) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierExactState sp data size oldS0 oldS1 bytes trace
    (writeSuccessSuffixBytesCarrierExactReg "x1" (BV 64 0x15910))
    (writeSuccessSuffixBytesCarrierExactReg "x5" (BV 64 0x2401a0b8))
    (writeSuccessSuffixBytesCarrierShapeReg "x6") 952 P.

Definition writeSuccessSuffixBytesAt15920CarrierExactData `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
    (trace : spec) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierExactState sp data size oldS0 oldS1 bytes trace
    (writeSuccessSuffixBytesCarrierExactReg "x1" (BV 64 0x15920))
    (writeSuccessSuffixBytesCarrierExactReg "x5" (BV 64 0x2401a0b8))
    (writeSuccessSuffixBytesCarrierShapeReg "x6") 968 P.

Definition writeSuccessSuffixBytesAt15930CarrierExactData `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
    (trace : spec) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierExactState sp data size oldS0 oldS1 bytes trace
    (writeSuccessSuffixBytesCarrierExactReg "x1" (BV 64 0x15930))
    (writeSuccessSuffixBytesCarrierExactReg "x5" (BV 64 0x2401a0b8))
    (writeSuccessSuffixBytesCarrierShapeReg "x6") 984 P.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15900CarrierExactData) := I.
Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15910CarrierExactData) := I.
Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15920CarrierExactData) := I.
Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15930CarrierExactData) := I.

Definition writeSuccessSuffixBytesAt158f0CarrierNext `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierState sp
    (writeSuccessSuffixBytesCarrierExactReg "x1" (BV 64 0x158f0))
    (writeSuccessSuffixBytesCarrierExactReg "x5" (BV 64 0x2401a0b8))
    (writeSuccessSuffixBytesCarrierShapeReg "x6")
    (fun data => writeSuccessSuffixBytesCarrierExactReg "x10" data)
    (fun size => writeSuccessSuffixBytesCarrierExactReg "x11" size)
    (fun _ _ tail => tail) 920 P.

Definition writeSuccessSuffixBytesAt15900Carrier `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierState sp
    (writeSuccessSuffixBytesCarrierShapeReg "x1")
    (writeSuccessSuffixBytesCarrierShapeReg "x5")
    (writeSuccessSuffixBytesCarrierShapeReg "x6")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x10")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x11")
    (fun data size tail =>
      writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents data size tail)) 936 P.

Definition writeSuccessSuffixBytesAt15900CarrierExact `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierState sp
    (writeSuccessSuffixBytesCarrierExactReg "x1" (BV 64 0x15900))
    (writeSuccessSuffixBytesCarrierExactReg "x5" (BV 64 0x2401a0b8))
    (writeSuccessSuffixBytesCarrierShapeReg "x6")
    (fun data => writeSuccessSuffixBytesCarrierExactReg "x10" data)
    (fun size => writeSuccessSuffixBytesCarrierExactReg "x11" size)
    (fun _ _ tail => tail) 936 P.

Definition writeSuccessSuffixBytesAt15910Carrier `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierState sp
    (writeSuccessSuffixBytesCarrierShapeReg "x1")
    (writeSuccessSuffixBytesCarrierShapeReg "x5")
    (writeSuccessSuffixBytesCarrierShapeReg "x6")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x10")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x11")
    (fun data size tail =>
      writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents data size tail)) 952 P.

Definition writeSuccessSuffixBytesAt15910CarrierExact `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierState sp
    (writeSuccessSuffixBytesCarrierExactReg "x1" (BV 64 0x15910))
    (writeSuccessSuffixBytesCarrierExactReg "x5" (BV 64 0x2401a0b8))
    (writeSuccessSuffixBytesCarrierShapeReg "x6")
    (fun data => writeSuccessSuffixBytesCarrierExactReg "x10" data)
    (fun size => writeSuccessSuffixBytesCarrierExactReg "x11" size)
    (fun _ _ tail => tail) 952 P.

Definition writeSuccessSuffixBytesAt15920Carrier `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierState sp
    (writeSuccessSuffixBytesCarrierShapeReg "x1")
    (writeSuccessSuffixBytesCarrierShapeReg "x5")
    (writeSuccessSuffixBytesCarrierShapeReg "x6")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x10")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x11")
    (fun data size tail =>
      writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents data size tail)) 968 P.

Definition writeSuccessSuffixBytesAt15920CarrierExact `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierState sp
    (writeSuccessSuffixBytesCarrierExactReg "x1" (BV 64 0x15920))
    (writeSuccessSuffixBytesCarrierExactReg "x5" (BV 64 0x2401a0b8))
    (writeSuccessSuffixBytesCarrierShapeReg "x6")
    (fun data => writeSuccessSuffixBytesCarrierExactReg "x10" data)
    (fun size => writeSuccessSuffixBytesCarrierExactReg "x11" size)
    (fun _ _ tail => tail) 968 P.

Definition writeSuccessSuffixBytesAt15930Carrier `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierState sp
    (writeSuccessSuffixBytesCarrierExactReg "x1" (BV 64 0x15930))
    (writeSuccessSuffixBytesCarrierExactReg "x5" (BV 64 0x2401a0b8))
    (writeSuccessSuffixBytesCarrierShapeReg "x6")
    (fun data => writeSuccessSuffixBytesCarrierExactReg "x10" data)
    (fun size => writeSuccessSuffixBytesCarrierExactReg "x11" size)
    (fun _ _ tail => tail) 984 P.

Definition writeSuccessSuffixBytesAt15930CarrierShape `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessSuffixBytesCarrierState sp
    (writeSuccessSuffixBytesCarrierShapeReg "x1")
    (writeSuccessSuffixBytesCarrierShapeReg "x5")
    (writeSuccessSuffixBytesCarrierShapeReg "x6")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x10")
    (fun _ => writeSuccessSuffixBytesCarrierShapeReg "x11")
    (fun data size tail =>
      writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents data size tail)) 984 P.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt158f0CarrierNext) := I.
Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15900Carrier) := I.
Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15900CarrierExact) := I.
Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15910Carrier) := I.
Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15910CarrierExact) := I.
Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15920Carrier) := I.
Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15920CarrierExact) := I.
Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15930Carrier) := I.
Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAt15930CarrierShape) := I.

Lemma write_success_suffix_bytes_158f0_carrier
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (P : iProp Sigma)
    (data size oldS0 oldS1 : bv 64) (bytes : list (bv 8)) (trace : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x15900
    (writeSuccessSuffixBytesAt15900CarrierExactData sp data size oldS0 oldS1
      bytes trace P) -∗
  instr_body 0x158f0
    (writeSuccessSuffixBytesAt15900CarrierData sp data size oldS0 oldS1
      bytes
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents data size trace)) P).
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
  all: iExists
    (trace, bytes, 0x15900, oldS1, oldS0, sp, size, data, tt)ₗ.
  all: try cbn.
  all: try unLET.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  all: try liARun.
  Unshelve. all: try prepare_sidecond.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try bv_solve.
  all: try lia.
  all: iSplit; last done.
  all: iIntros "Hpost".
  all: iEval (rewrite /writeSuccessSuffixBytesAt15900CarrierData
    /writeSuccessSuffixBytesCarrierDataState).
  all: iFrame.
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
  Unshelve.
  all: try iExists
    (trace, bytes, 0x15900, oldS1, oldS0, sp, size, data, tt)ₗ.
  all: try cbn.
  all: try unLET.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  all: try liARun.
  all: have Hreturn : Z_to_bv 64 88320 = BV 64 88320 by bv_solve.
  all: try rewrite -Hreturn.
  all: try iRename select (_ ↦ₘ data)%I into "HdescData".
  all: try iRename select (_ ↦ₘ size)%I into "HdescSize".
  all: have Haddr936 :
    bv_unsigned (sp + BV 64 936)%bv = bv_unsigned sp + 936 by bv_solve.
  all: have Haddr944 :
    bv_unsigned (sp + BV 64 944)%bv = bv_unsigned sp + 944 by bv_solve.
  all: have Haddr944Frame :
    bv_unsigned sp + 936 + 8 = bv_unsigned sp + 944 by lia.
  all: iEval (rewrite Haddr936) in "HdescData".
  all: iEval (rewrite Haddr944) in "HdescSize".
  all: rewrite /reg_col; cbn.
  all: iFrame "HdescData HdescSize".
  all: iFrame.
  Unshelve. all: try prepare_sidecond.
  all: try bv_solve.
Qed.

Lemma write_success_suffix_bytes_15900_carrier
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (P : iProp Sigma)
    (data size oldS0 oldS1 : bv 64) (bytes : list (bv 8)) (trace : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x15910
    (writeSuccessSuffixBytesAt15910CarrierExactData sp data size oldS0 oldS1
      bytes trace P) -∗
  instr_body 0x15900
    (writeSuccessSuffixBytesAt15910CarrierData sp data size oldS0 oldS1
      bytes
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents data size trace)) P).
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
  all: iExists
    (trace, bytes, 0x15910, oldS1, oldS0, sp, size, data, tt)ₗ.
  all: try cbn.
  all: try unLET.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  all: try liARun.
  Unshelve. all: try prepare_sidecond.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try bv_solve.
  all: try lia.
  all: iSplit; last done.
  all: iIntros "Hpost".
  all: iEval (rewrite /writeSuccessSuffixBytesAt15910CarrierData
    /writeSuccessSuffixBytesCarrierDataState).
  all: iFrame.
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
  Unshelve.
  all: try iExists
    (trace, bytes, 0x15910, oldS1, oldS0, sp, size, data, tt)ₗ.
  all: try cbn.
  all: try unLET.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  all: try liARun.
  all: have Hreturn : Z_to_bv 64 88336 = BV 64 88336 by bv_solve.
  all: try rewrite -Hreturn.
  all: try iRename select (_ ↦ₘ data)%I into "HdescData".
  all: try iRename select (_ ↦ₘ size)%I into "HdescSize".
  all: have Haddr952 :
    bv_unsigned (sp + BV 64 952)%bv = bv_unsigned sp + 952 by bv_solve.
  all: have Haddr960 :
    bv_unsigned (sp + BV 64 960)%bv = bv_unsigned sp + 960 by bv_solve.
  all: iEval (rewrite Haddr952) in "HdescData".
  all: iEval (rewrite Haddr960) in "HdescSize".
  all: rewrite /reg_col; cbn.
  all: iFrame "HdescData HdescSize".
  all: iFrame.
  Unshelve. all: try prepare_sidecond.
  all: try bv_solve.
Qed.

Lemma write_success_suffix_bytes_15910_carrier
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (P : iProp Sigma)
    (data size oldS0 oldS1 : bv 64) (bytes : list (bv 8)) (trace : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x15920
    (writeSuccessSuffixBytesAt15920CarrierExactData sp data size oldS0 oldS1
      bytes trace P) -∗
  instr_body 0x15910
    (writeSuccessSuffixBytesAt15920CarrierData sp data size oldS0 oldS1
      bytes
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents data size trace)) P).
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
  all: iExists
    (trace, bytes, 0x15920, oldS1, oldS0, sp, size, data, tt)ₗ.
  all: try cbn.
  all: try unLET.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  all: try liARun.
  Unshelve. all: try prepare_sidecond.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try bv_solve.
  all: try lia.
  all: iSplit; last done.
  all: iIntros "Hpost".
  all: iEval (rewrite /writeSuccessSuffixBytesAt15920CarrierData
    /writeSuccessSuffixBytesCarrierDataState).
  all: iFrame.
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
  Unshelve.
  all: try iExists
    (trace, bytes, 0x15920, oldS1, oldS0, sp, size, data, tt)ₗ.
  all: try cbn.
  all: try unLET.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  all: try liARun.
  all: have Hreturn : Z_to_bv 64 88352 = BV 64 88352 by bv_solve.
  all: try rewrite -Hreturn.
  all: try iRename select (_ ↦ₘ data)%I into "HdescData".
  all: try iRename select (_ ↦ₘ size)%I into "HdescSize".
  all: have Haddr968 :
    bv_unsigned (sp + BV 64 968)%bv = bv_unsigned sp + 968 by bv_solve.
  all: have Haddr976 :
    bv_unsigned (sp + BV 64 976)%bv = bv_unsigned sp + 976 by bv_solve.
  all: iEval (rewrite Haddr968) in "HdescData".
  all: iEval (rewrite Haddr976) in "HdescSize".
  all: rewrite /reg_col; cbn.
  all: iFrame "HdescData HdescSize".
  all: iFrame.
  Unshelve. all: try prepare_sidecond.
  all: try bv_solve.
Qed.

Lemma write_success_suffix_bytes_15920_carrier
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x15930 (writeSuccessSuffixBytesAt15930Carrier sp P) -∗
  instr_body 0x15920 (writeSuccessSuffixBytesAt15930CarrierShape sp P).
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
    (tail, bytes, 0x15930, oldS1, oldS0, sp, size, data, tt)ₗ.
  all: try cbn.
  all: try unLET.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  all: try liARun.
  Unshelve. all: try prepare_sidecond.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try bv_solve.
  all: try lia.
  all: iSplit; last done.
  all: iIntros "Hpost".
  all: iEval (rewrite /writeSuccessSuffixBytesAt15930Carrier
    /writeSuccessSuffixBytesCarrierState).
  all: iExists data, size, oldS0, oldS1, bytes, tail.
  all: iFrame.
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
  Unshelve.
  all: iSplit; last done.
  all: iIntros "Hpost".
  all: iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack & Hdata &
      Hmmio & Htrace & _)".
  all: iEval (rewrite /writeSuccessSuffixBytesAt15930Carrier
    /writeSuccessSuffixBytesCarrierState).
  all: iExists data, size, oldS0, oldS1, bytes, tail.
  all: iFrame.
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
  Unshelve.
  all: have Hreturn : Z_to_bv 64 88368 = BV 64 88368 by bv_solve.
  all: rewrite -Hreturn.
  all: try iRename select (_ ↦ₘ data)%I into "HdescData".
  all: try iRename select (_ ↦ₘ size)%I into "HdescSize".
  all: have Haddr984 :
    bv_unsigned (sp + BV 64 984)%bv = bv_unsigned sp + 984 by bv_solve.
  all: have Haddr992 :
    bv_unsigned (sp + BV 64 992)%bv = bv_unsigned sp + 992 by bv_solve.
  all: iEval (rewrite Haddr984) in "HdescData".
  all: iEval (rewrite Haddr992) in "HdescSize".
  all: rewrite /reg_col; cbn.
  all: iFrame "HdescData HdescSize".
  all: iFrame.
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
  Unshelve.
  all: lazymatch goal with |- ?G => fail "suffix bytes carrier residual" G end.
Qed.

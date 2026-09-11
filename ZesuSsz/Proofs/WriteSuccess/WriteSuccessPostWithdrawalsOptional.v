Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Import ListNotations.

Definition writeSuccessPostWithdrawalsSaved : list string :=
  ["x3"; "x4"; "x6"; "x7"; "x8"; "x9";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x18"; "x19";
   "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessPostWithdrawalsAt1571c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp data size root : bv 64) (bytes : list (bv 8))
      (saved : list valu) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    reg_col (zip_with (fun register value =>
      (KindReg register, ExactShape value))
      writeSuccessPostWithdrawalsSaved saved) ∗
    ⌜length saved = length writeSuccessPostWithdrawalsSaved⌝ ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
    (bv_unsigned sp + 1168) ↦ₘ data ∗
    (bv_unsigned sp + 1176) ↦ₘ size ∗
    (bv_unsigned sp + 1000) ↦ₘ root ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEventsAny data size tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawalsAt1571c) := I.

Definition writeSuccessPostWithdrawalsAt15700
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp optionalValue optionalTag data size root : bv 64)
      (bytes : list (bv 8)) (saved : list valu) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15700) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    reg_col (zip_with (fun register value =>
      (KindReg register, ExactShape value))
      writeSuccessPostWithdrawalsSaved saved) ∗
    ⌜length saved = length writeSuccessPostWithdrawalsSaved⌝ ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
    (bv_unsigned sp + 1152) ↦ₘ optionalValue ∗
    (bv_unsigned sp + 1160) ↦ₘ optionalTag ∗
    (bv_unsigned sp + 1168) ↦ₘ data ∗
    (bv_unsigned sp + 1176) ↦ₘ size ∗
    (bv_unsigned sp + 1000) ↦ₘ root ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    mmio_range 0x2401a0c0 16 ∗
    ((⌜bv_extract 0 8 optionalTag = BV 8 0⌝ ∗
       spec_trace (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
         (writeOutputEventsAny data size tail))) ∨
     (⌜bv_extract 0 8 optionalTag <> BV 8 0⌝ ∗
       spec_trace (writeOutputEventsAny (sp - BV 64 25)%bv (BV 64 1)
         (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
           (writeOutputEventsAny data size tail))))) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawalsAt15700) := I.

Definition writeSuccessPostWithdrawalsAt15718
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp optionalValue optionalTag data size root : bv 64)
      (bytes : list (bv 8)) (saved : list valu) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15714) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
    "x10" ↦ᵣ RVal_Bits (sp + BV 64 1624)%bv ∗
    "x11" ↦ᵣ RVal_Bits optionalTag ∗
    reg_col (zip_with (fun register value =>
      (KindReg register, ExactShape value))
      writeSuccessPostWithdrawalsSaved saved) ∗
    ⌜length saved = length writeSuccessPostWithdrawalsSaved⌝ ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    (bv_unsigned sp + 1624) ↦ₘ optionalValue ∗
    (bv_unsigned sp + 1632) ↦ₘ optionalTag ∗
    (bv_unsigned sp + 1152) ↦ₘ optionalValue ∗
    (bv_unsigned sp + 1160) ↦ₘ optionalTag ∗
    (bv_unsigned sp + 1168) ↦ₘ data ∗
    (bv_unsigned sp + 1176) ↦ₘ size ∗
    (bv_unsigned sp + 1000) ↦ₘ root ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    mmio_range 0x2401a0c0 16 ∗
    ((⌜bv_extract 0 8 optionalTag = BV 8 0⌝ ∗
       spec_trace (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
         (writeOutputEventsAny data size tail))) ∨
     (⌜bv_extract 0 8 optionalTag <> BV 8 0⌝ ∗
       spec_trace (writeOutputEventsAny (sp - BV 64 25)%bv (BV 64 1)
         (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
           (writeOutputEventsAny data size tail))))) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawalsAt15718) := I.

Definition writeSuccessPostWithdrawals15700State
    `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (saved : list valu) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15700) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   reg_col (zip_with (fun register value =>
     (KindReg register, ExactShape value))
     writeSuccessPostWithdrawalsSaved saved) ∗
   ⌜length saved = length writeSuccessPostWithdrawalsSaved⌝ ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   (bv_unsigned sp + 1152) ↦ₘ optionalValue ∗
   (bv_unsigned sp + 1160) ↦ₘ optionalTag ∗
   (bv_unsigned sp + 1168) ↦ₘ data ∗ (bv_unsigned sp + 1176) ↦ₘ size ∗
   (bv_unsigned sp + 1000) ↦ₘ root ∗ bv_unsigned data ↦ₘ∗ bytes ∗
   ⌜bv_unsigned size = length bytes⌝ ∗ mmio_range 0x2401a0c0 16 ∗
   ((⌜bv_extract 0 8 optionalTag = BV 8 0⌝ ∗
      spec_trace (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
        (writeOutputEventsAny data size tail))) ∨
    (⌜bv_extract 0 8 optionalTag <> BV 8 0⌝ ∗
      spec_trace (writeOutputEventsAny (sp - BV 64 25)%bv (BV 64 1)
        (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
          (writeOutputEventsAny data size tail))))) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < 0x40000000⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.

Definition writeSuccessPostWithdrawals15718State
    `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (saved : list valu) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15714) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1624)%bv ∗
   "x11" ↦ᵣ RVal_Bits optionalTag ∗
   reg_col (zip_with (fun register value =>
     (KindReg register, ExactShape value))
     writeSuccessPostWithdrawalsSaved saved) ∗
   ⌜length saved = length writeSuccessPostWithdrawalsSaved⌝ ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   (bv_unsigned sp + 1624) ↦ₘ optionalValue ∗
   (bv_unsigned sp + 1632) ↦ₘ optionalTag ∗
   (bv_unsigned sp + 1152) ↦ₘ optionalValue ∗
   (bv_unsigned sp + 1160) ↦ₘ optionalTag ∗
   (bv_unsigned sp + 1168) ↦ₘ data ∗ (bv_unsigned sp + 1176) ↦ₘ size ∗
   (bv_unsigned sp + 1000) ↦ₘ root ∗ bv_unsigned data ↦ₘ∗ bytes ∗
   ⌜bv_unsigned size = length bytes⌝ ∗ mmio_range 0x2401a0c0 16 ∗
   ((⌜bv_extract 0 8 optionalTag = BV 8 0⌝ ∗
      spec_trace (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
        (writeOutputEventsAny data size tail))) ∨
    (⌜bv_extract 0 8 optionalTag <> BV 8 0⌝ ∗
      spec_trace (writeOutputEventsAny (sp - BV 64 25)%bv (BV 64 1)
        (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
          (writeOutputEventsAny data size tail))))) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < 0x40000000⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawals15700State) := I.
Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawals15718State) := I.

Lemma block_15700 `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (saved : list valu) (tail : spec)
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15718
    (writeSuccessPostWithdrawals15718State sp optionalValue optionalTag
      data size root bytes saved tail P) -∗
  instr_body 0x15700
    (writeSuccessPostWithdrawals15700State sp optionalValue optionalTag
      data size root bytes saved tail P).
Proof.
  move => *.
  iStartProof. iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try zesu_finish.
  all: lazymatch goal with |- ?G => fail "block_15700 residual" G end.
Qed.

Print Assumptions block_15700.

From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.

Lemma reg_col_exact_bv_to_bits `{!islaG Sigma} `{!threadG}
    (registers : list string) (values : list (bv 64)) :
  length registers = length values ->
  reg_col (zip_with (fun register value =>
      (KindReg register, ExactShape value)) registers
    ((fun value : bv 64 => RVal_Bits value) <$> values)) -∗
  reg_col ((fun register => (KindReg register, BitsShape 64)) <$> registers).
Proof.
  revert values. induction registers as [|register registers IH];
    intros [|value values] Hlength; simpl in Hlength; try lia.
  - iIntros "_". rewrite reg_col_nil. done.
  - rewrite !reg_col_cons. iIntros "[Hhead Htail]".
    iDestruct "Hhead" as (actual Hactual) "Hregister".
    simpl in Hactual. subst actual.
    iSplitL "Hregister".
    { iExists (RVal_Bits value). iFrame. done. }
    iApply (IH values); [lia | iExact "Htail"].
Qed.

Definition zesu_call_ret `{!islaG Sigma} `{!threadG}
    (stack_size : Z) (regs : list valu) (ret sp : bv 64)
    (Q : list (bv 64) -> iProp Sigma) : iProp Sigma :=
  reg_col zesu_ram_sys_regs ∗
  reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
    (["x1"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17"] ++ tmp_registers)) ∗
  reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
    ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
     "x22"; "x23"; "x24"; "x25"; "x26"; "x27"] regs) ∗
  "x10" ↦ᵣ: fun r10 => ∃ b10 : bv 64, ⌜r10 = RVal_Bits b10⌝ ∗
  "x11" ↦ᵣ: fun r11 => ∃ b11 : bv 64, ⌜r11 = RVal_Bits b11⌝ ∗
  "x2" ↦ᵣ RVal_Bits sp ∗
  (bv_unsigned sp - stack_size) ↦ₘ? stack_size ∗ Q [b10; b11].

Global Instance : LithiumUnfold (@zesu_call_ret) := I.

Definition zesu_call `{!islaG Sigma} `{!threadG} (stack_size : Z)
    (P : list (bv 64) -> bv 64 ->
      ((list (bv 64) -> iProp Sigma) -> iProp Sigma) -> iProp Sigma) :
    iProp Sigma :=
  ∃ (sp ret : bv 64),
  reg_col zesu_ram_sys_regs ∗
  reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
  "x10" ↦ᵣ: fun r10 => ∃ b10 : bv 64, ⌜r10 = RVal_Bits b10⌝ ∗
  "x11" ↦ᵣ: fun r11 => ∃ b11 : bv 64, ⌜r11 = RVal_Bits b11⌝ ∗
  "x12" ↦ᵣ: fun r12 => ∃ b12 : bv 64, ⌜r12 = RVal_Bits b12⌝ ∗
  "x13" ↦ᵣ: fun r13 => ∃ b13 : bv 64, ⌜r13 = RVal_Bits b13⌝ ∗
  "x14" ↦ᵣ: fun r14 => ∃ b14 : bv 64, ⌜r14 = RVal_Bits b14⌝ ∗
  "x15" ↦ᵣ: fun r15 => ∃ b15 : bv 64, ⌜r15 = RVal_Bits b15⌝ ∗
  "x16" ↦ᵣ: fun r16 => ∃ b16 : bv 64, ⌜r16 = RVal_Bits b16⌝ ∗
  "x17" ↦ᵣ: fun r17 => ∃ b17 : bv 64, ⌜r17 = RVal_Bits b17⌝ ∗
  "x8" ↦ᵣ: fun r8 => ⌜valu_has_shape r8 (BitsShape 64)⌝ ∗
  "x9" ↦ᵣ: fun r9 => ⌜valu_has_shape r9 (BitsShape 64)⌝ ∗
  "x18" ↦ᵣ: fun r18 => ⌜valu_has_shape r18 (BitsShape 64)⌝ ∗
  "x19" ↦ᵣ: fun r19 => ⌜valu_has_shape r19 (BitsShape 64)⌝ ∗
  "x20" ↦ᵣ: fun r20 => ⌜valu_has_shape r20 (BitsShape 64)⌝ ∗
  "x21" ↦ᵣ: fun r21 => ⌜valu_has_shape r21 (BitsShape 64)⌝ ∗
  "x22" ↦ᵣ: fun r22 => ⌜valu_has_shape r22 (BitsShape 64)⌝ ∗
  "x23" ↦ᵣ: fun r23 => ⌜valu_has_shape r23 (BitsShape 64)⌝ ∗
  "x24" ↦ᵣ: fun r24 => ⌜valu_has_shape r24 (BitsShape 64)⌝ ∗
  "x25" ↦ᵣ: fun r25 => ⌜valu_has_shape r25 (BitsShape 64)⌝ ∗
  "x26" ↦ᵣ: fun r26 => ⌜valu_has_shape r26 (BitsShape 64)⌝ ∗
  "x27" ↦ᵣ: fun r27 => ⌜valu_has_shape r27 (BitsShape 64)⌝ ∗
  "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
  ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
  ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗ ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
  ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
  ⌜0x20000000 <= bv_unsigned sp - stack_size /\
    bv_unsigned sp < 0x40000000⌝ ∗
  (bv_unsigned sp - stack_size) ↦ₘ? stack_size ∗
  P [b10; b11; b12; b13; b14; b15; b16; b17] sp (fun Q =>
    instr_pre (bv_unsigned ret)
      (zesu_call_ret stack_size
        [r8; r9; r18; r19; r20; r21; r22; r23; r24; r25; r26; r27]
        ret sp Q)).

Global Instance : LithiumUnfold (@zesu_call) := I.

Notation zesu_c_call := zesu_call.
Notation zesu_c_call_ret := zesu_call_ret.

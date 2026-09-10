From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition zesu_c_call_ret `{!islaG Sigma} `{!threadG}
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

Global Instance : LithiumUnfold (@zesu_c_call_ret) := I.

Definition zesu_c_call `{!islaG Sigma} `{!threadG} (stack_size : Z)
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
      (zesu_c_call_ret stack_size
        [r8; r9; r18; r19; r20; r21; r22; r23; r24; r25; r26; r27]
        ret sp Q)).

Global Instance : LithiumUnfold (@zesu_c_call) := I.

Lemma zesu_c_call_ret_16_to_32 `{!islaG Sigma} `{!threadG}
    (regs : list valu) (ret sp : bv 64) (Q : list (bv 64) -> iProp Sigma) :
  instr_pre (bv_unsigned ret) (zesu_c_call_ret 32 regs ret sp Q) -∗
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret 16 regs ret sp (fun args =>
      (bv_unsigned sp - 32) ↦ₘ? 16 ∗ Q args)).
Proof.
  iStartProof. iIntros "Hret".
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hret"); [done | done |].
  iEval (unfold zesu_c_call_ret).
  iIntros "(Hsys & Htmp & Hsaved & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10 & Hrest)".
  iDestruct "Hrest" as (r11) "(H11 & Hrest)".
  iDestruct "Hrest" as (b11) "(%Hr11 & H2 & Hupper & Hlower & HQ)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "Hsys Htmp Hsaved H10 H11 H2".
  iExists b10. iSplit; first done.
  iExists b11. iSplit; first done.
  iFrame "HQ".
  iApply (mem_mapsto_uninit_combine 16 with "Hlower"); first lia.
  have -> : bv_unsigned sp - 32 + 16 = bv_unsigned sp - 16 by lia.
  iExact "Hupper".
Qed.

Lemma zesu_c_call_ret_frame `{!islaG Sigma} `{!threadG}
    (stack_size : Z) (regs : list valu) (ret sp : bv 64)
    (F : iProp Sigma) (Q : list (bv 64) -> iProp Sigma) :
  instr_pre (bv_unsigned ret)
    (zesu_c_call_ret stack_size regs ret sp (fun args => F ∗ Q args)) -∗
  F -∗
  instr_pre (bv_unsigned ret) (zesu_c_call_ret stack_size regs ret sp Q).
Proof.
  iStartProof. iIntros "Hret HF".
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
    with "Hret"); [done | done |].
  iEval (unfold zesu_c_call_ret).
  iIntros "(Hsys & Htmp & Hsaved & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10 & Hrest)".
  iDestruct "Hrest" as (r11) "(H11 & Hrest)".
  iDestruct "Hrest" as (b11) "(%Hr11 & H2 & Hstack & HQ)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "Hsys Htmp Hsaved H10 H11 H2 Hstack".
  iExists b10. iSplit; first done.
  iExists b11. iSplit; first done.
  iFrame.
Qed.

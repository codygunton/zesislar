Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPayloadCall.

Import ListNotations.

Definition writeSuccessBooleanWord (present : bool) : bv 64 :=
  if present then BV 64 1 else BV 64 0.

Definition writeSuccessBooleanPayload (present : bool) : list (bv 8) :=
  writeSuccessPrivateBytes [if present then 1 else 0].

Definition writeSuccessBooleanCallRegShapes : list (reg_kind * valu_shape) :=
  [(KindReg "x6", BitsShape 64); (KindReg "x7", BitsShape 64);
   (KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64);
   (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
   (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64);
   (KindReg "x16", BitsShape 64); (KindReg "x17", BitsShape 64);
   (KindReg "x18", BitsShape 64); (KindReg "x19", BitsShape 64);
   (KindReg "x20", BitsShape 64); (KindReg "x21", BitsShape 64);
   (KindReg "x22", BitsShape 64); (KindReg "x23", BitsShape 64);
   (KindReg "x24", BitsShape 64); (KindReg "x25", BitsShape 64);
   (KindReg "x26", BitsShape 64); (KindReg "x27", BitsShape 64);
   (KindReg "x28", BitsShape 64); (KindReg "x29", BitsShape 64);
   (KindReg "x30", BitsShape 64); (KindReg "x31", BitsShape 64)].

Definition zesuEncoderBooleanPayloadCallSpec `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (∃ (present : bool) (sp ret : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessBooleanCallRegShapes ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    ("x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
    "x10" ↦ᵣ RVal_Bits (writeSuccessBooleanWord present) ∗
    ("x11" ↦ᵣ: fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
      (writeSuccessBooleanPayload present) tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
    instr_pre (bv_unsigned ret)
      (reg_col zesu_ram_sys_regs ∗
       reg_col writeSuccessBooleanCallRegShapes ∗
       "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       ("x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
       ("x10" ↦ᵣ: fun r10 => ⌜valu_has_shape r10 (BitsShape 64)⌝) ∗
       ("x11" ↦ᵣ: fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝) ∗
       (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range 0x2401a0c0 16 ∗
       spec_trace tail ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@zesuEncoderBooleanPayloadCallSpec) := I.

Definition encoderBooleanPayloadSpec `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_x11 stackByte stackRa : bv 64),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessBooleanCallRegShapes ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits value ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
    (bv_unsigned sp - 16) ↦ₘ? 7 ∗
    (bv_unsigned sp - 9) ↦ₘ (bv_extract 0 8 stackByte) ∗
    (bv_unsigned sp - 8) ↦ₘ stackRa ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
      [bv_extract 0 8 (bv_and value (BV 64 1))] tail) ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (reg_col zesu_ram_sys_regs ∗
       reg_col writeSuccessBooleanCallRegShapes ∗
       "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       ("x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
       ("x10" ↦ᵣ: fun r10 => ⌜valu_has_shape r10 (BitsShape 64)⌝) ∗
       ("x11" ↦ᵣ: fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝) ∗
       (bv_unsigned sp - 16) ↦ₘ? 7 ∗
       (bv_unsigned sp - 9) ↦ₘ
         (bv_extract 0 8 (bv_and value (BV 64 1))) ∗
       (bv_unsigned sp - 8) ↦ₘ ret ∗
       mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@encoderBooleanPayloadSpec) := I.

#[local] Hint Rewrite (@bv_sign_extend_idemp 64) :
  lithium_rewrite isla_coq_rewrite.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Ltac run_exact_boolean_prefix :=
  lazymatch goal with
  | |- instr_body 0x15bb8 _ => idtac
  | _ => first [liAStep | prepare_sidecond | bv_solve | lia];
      run_exact_boolean_prefix
  end.

Lemma writeSuccessBooleanStackAddress sp :
  bv_unsigned (sp + BV 64 18446744073709551600 + BV 64 7)%bv =
  bv_unsigned (sp - BV 64 9)%bv.
Proof. bv_solve. Qed.

Lemma writeSuccessBooleanArrayStart sp :
  0x20000000 <= bv_unsigned sp - 16 ->
  IslarisMemory.array_region_start 8
    (bv_unsigned (sp + BV 64 18446744073709551600 + BV 64 7)%bv)
    (bv_unsigned sp - 9) = 0%nat.
Proof. intros Hmin.
  rewrite /IslarisMemory.array_region_start writeSuccessBooleanStackAddress.
  replace (bv_unsigned (sp - BV 64 9)%bv) with (bv_unsigned sp - 9) by
    bv_solve.
  rewrite Z.sub_diag. reflexivity.
Qed.

Lemma writeSuccessBooleanNoWrap sp :
  0x20000000 <= bv_unsigned sp - 16 ->
  bv_unsigned (sp - BV 64 9)%bv = bv_unsigned sp - 9.
Proof. intros Hmin. bv_solve. Qed.

Lemma encoder_boolean_payload_correct `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  instr_body 0x15b9c (encoderBooleanPayloadSpec value sp ret tail P).
Proof.
  move => * /=. iStartProof. iIntros "_ #Hcode #Houtput".
  iEval (simpl) in "Hcode".
  iDestruct "Hcode" as
    "(#Hi0 & #Hi1 & #Hi2 & #Hi3 & #Hi4 & #Hi5 & #Hi6 & #Hi7 & #Hi8 &
      #Hi9 & #Hi10 & _)".
  liARun.
  Unshelve. all: prepare_sidecond; try assumption;
    try (bv_simplify_arith select (bv_extract 0 4 sp = _));
    try (bv_simplify_arith select (bv_extract 0 3 sp = _));
    try rewrite bv_sign_extend_idemp; try bv_solve; try lia; try iFrame.
  Unshelve.
  all: try iRename select ((bv_unsigned sp - 16) ↦ₘ? 7)%I into "Hlow".
  all: try iRename select (spec_trace
    (writeOutputEvents (sp - 9)%bv (BV 64 1)
      [bv_extract 0 8 (bv_and value (BV 64 1))] tail))%I into "Htrace".
  all: try iRename select (instr_pre (bv_unsigned ret) _)%I into "Hreturn".
  all: try iRename select (_ ↦ₘ ret)%I into "Hra".
  all: try iRename select (mmio_range 0x2401a0c0 16)%I into "Hmmio".
  all: try iFrame "Hlow Hra".
  all: try iEval (rewrite reg_col_nil).
  all: try iExists (tail, tt)ₗ.
  all: try (iSplit; [iPureIntro; spec_solver |]).
  all: try (iSplit; [iPureIntro; reflexivity |]).
  all: try liARun.
  Unshelve. all: prepare_sidecond; try assumption;
    try (bv_simplify_arith select (bv_extract 0 3 sp = _));
    try rewrite bv_sign_extend_idemp; try bv_solve; try lia;
    try simplify_eq; try (symmetry; assumption); try congruence; try iFrame.
  all: try (rewrite writeSuccessBooleanStackAddress; reflexivity).
  all: try (rewrite writeSuccessBooleanStackAddress
    /IslarisMemory.array_region_start Z.sub_diag; cbn; lia).
  all: lazymatch goal with
  | |- bv_unsigned ?sp0 - 9 = _ =>
      rewrite (writeSuccessBooleanArrayStart sp0); [|lia]; cbn;
      rewrite writeSuccessBooleanStackAddress
        (writeSuccessBooleanNoWrap sp0); lia
  | _ => idtac
  end.
  all: try (rewrite writeSuccessBooleanArrayStart; [|lia]; reflexivity).
  all: lazymatch goal with |- ?G => fail "exact boolean core" G end.
Qed.

Print Assumptions encoder_boolean_payload_correct.

Lemma writeSuccessBooleanPayload_word present :
  [bv_extract 0 8
    (bv_and (writeSuccessBooleanWord present) (BV 64 1))] =
  writeSuccessBooleanPayload present.
Proof. destruct present; reflexivity. Qed.

Lemma zesu_encoder_boolean_payload_call_correct
    `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  instr_body 0x15b9c zesuEncoderBooleanPayloadCallSpec.
Proof.
  iStartProof. iIntros "#Hcode #Houtput".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /zesuEncoderBooleanPayloadCallSpec.
  iDestruct "Hentry" as (present sp ret tail)
    "(Hsys & Hregs & H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace &
      %Halign & %Hmin & %Hmax & %Hret0 & %Hret1 & %Hret2 & Hnext & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5".
  iDestruct "H5" as (r5) "[H5 %Hr5]".
  apply valu_has_bits_shape in Hr5 as (b5 & ->).
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H11".
  iDestruct "H11" as (r11) "[H11 %Hr11]".
  apply valu_has_bits_shape in Hr11 as (b11 & ->).
  iEval (rewrite <- instr_pre'_eq) in "Houtput".
  iPoseProof (encoder_boolean_payload_correct
    (writeSuccessBooleanWord present) sp ret tail True%I with
    "Hcode Houtput") as "Hbody".
  iDestruct (mem_mapsto_uninit_split 7 with "Hstack") as
    "[Hlow Hrest]"; first lia.
  iDestruct (mem_mapsto_uninit_split 1 with "Hrest") as
    "[Hbyte Hra]"; first lia.
  iEval (replace (bv_unsigned sp - 16 + 7) with
    (bv_unsigned sp - 9) by lia) in "Hbyte".
  iEval (replace (bv_unsigned sp - 16 + 7 + 1) with
    (bv_unsigned sp - 8) by lia) in "Hra".
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hbyte") as
    (nByte stackByte HnByte) "Hbyte".
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hra") as
    (nRa stackRa HnRa) "Hra".
  cbn in HnByte, HnRa. subst nByte nRa.
  iAssert (instr_pre (bv_unsigned ret)
      (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessBooleanCallRegShapes ∗
       "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       ("x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
       ("x10" ↦ᵣ: fun r10 => ⌜valu_has_shape r10 (BitsShape 64)⌝) ∗
       ("x11" ↦ᵣ: fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝) ∗
       (bv_unsigned sp - 16) ↦ₘ? 7 ∗
       (bv_unsigned sp - 9) ↦ₘ
         (bv_extract 0 8
           (bv_and (writeSuccessBooleanWord present) (BV 64 1))) ∗
       (bv_unsigned sp - 8) ↦ₘ ret ∗ mmio_range 0x2401a0c0 16 ∗
       spec_trace tail ∗ True))%I with "[Hnext]" as "Hreturn".
  { iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret) true true
      with "Hnext"); [done | done |].
    iIntros "Hpost".
    iDestruct "Hpost" as
      "(Hsys & Hregs & H1 & H2 & H5 & H10 & H11 & Hlow & Hbyte & Hra &
        Hmmio & Htrace & _)".
    iDestruct (mem_mapsto_mapsto_to_uninit with "Hbyte") as "Hbyte".
    iDestruct (mem_mapsto_mapsto_to_uninit with "Hra") as "Hra".
    iEval (replace (bv_unsigned sp - 9) with
      (bv_unsigned sp - 16 + 7) by lia) in "Hbyte".
    iEval (replace (bv_unsigned sp - 8) with
      (bv_unsigned sp - 16 + 8) by lia) in "Hra".
    iAssert ((bv_unsigned sp - 16) ↦ₘ? 8)%I with "[Hlow Hbyte]"
      as "Hlower".
    { iApply (mem_mapsto_uninit_combine 7 (bv_unsigned sp - 16)
        (DfracOwn 1) 8 with "Hlow Hbyte"); lia. }
    iAssert ((bv_unsigned sp - 16) ↦ₘ? 16)%I with "[Hlower Hra]"
      as "Hstack".
    { iApply (mem_mapsto_uninit_combine 8 (bv_unsigned sp - 16)
        (DfracOwn 1) 16 with "Hlower Hra"); lia. }
    iFrame. }
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /encoderBooleanPayloadSpec.
  iExists b5, b11, (bv_zero_extend 64 stackByte), stackRa.
  have HbyteExtend :
      bv_extract 0 8 (bv_zero_extend 64 stackByte) = stackByte by
    bv_simplify; done.
  rewrite HbyteExtend.
  rewrite -writeSuccessBooleanPayload_word.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  all: try (iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret)
    true true with "Hreturn"); [done | done |]; iIntros "Hpost";
    iDestruct "Hpost" as
      "(Hsys & Hregs & H1 & H2 & H5 & H10 & H11 & Hlow & Hbyte & Hra &
        Hmmio & Htrace & _ & _)"; iFrame).
  all: lazymatch goal with |- ?G => fail "boolean adapter" G end.
Qed.

Print Assumptions zesu_encoder_boolean_payload_call_correct.

Lemma zesu_encoder_boolean_payload_call_pre
    `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanPayloadCallSpec.
Proof.
  iStartProof. iIntros "#HbooleanCode #Houtput". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_boolean_payload_call_correct; iAssumption.
Qed.

Print Assumptions zesu_encoder_boolean_payload_call_pre.

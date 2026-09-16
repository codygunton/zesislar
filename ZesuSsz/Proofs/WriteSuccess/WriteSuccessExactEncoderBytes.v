Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_06 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderInt.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.

Definition encoderBytesExactOutputResources `{!islaG Sigma} `{!threadG}
    (size sp ret : bv 64) (old_s0 old_s1 stack2 : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (("x6" ↦ᵣ: fun r6 => ⌜valu_has_shape r6 (BitsShape 64)⌝) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x8" ↦ᵣ RVal_Bits old_s0 ∗ "x9" ↦ᵣ RVal_Bits old_s1 ∗
   bv_unsigned (sp - BV 64 48)%bv ↦ₘ∗
     writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)) ∗
   (bv_unsigned sp - 40) ↦ₘ (BV 64 0x15c90) ∗
   (bv_unsigned sp - 32) ↦ₘ stack2 ∗
   (bv_unsigned sp - 24) ↦ₘ old_s1 ∗
   (bv_unsigned sp - 16) ↦ₘ old_s0 ∗
   (bv_unsigned sp - 8) ↦ₘ ret ∗ P)%I.

Definition encoderBytesExactPost `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (old_x6 old_s0 old_s1 stack2 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
   bv_unsigned data ↦ₘ∗ bytes ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
   encoderBytesExactOutputResources size sp ret old_s0 old_s1 stack2 P ∗
   True)%I.

Definition encoderBytesExactSuffixFrame `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (old_x6 old_s0 old_s1 stack2 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x6" ↦ᵣ RVal_Bits old_x6 ∗
   "x8" ↦ᵣ RVal_Bits size ∗ "x9" ↦ᵣ RVal_Bits data ∗
   (bv_unsigned sp - 32) ↦ₘ stack2 ∗
   (bv_unsigned sp - 24) ↦ₘ old_s1 ∗
   (bv_unsigned sp - 16) ↦ₘ old_s0 ∗
   (bv_unsigned sp - 8) ↦ₘ ret ∗
   bv_unsigned data ↦ₘ∗ bytes ∗
   ⌜bv_unsigned size = length bytes⌝ ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
   ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
   instr_pre (bv_unsigned ret)
     (encoderBytesExactPost data size sp ret bytes
       old_x6 old_s0 old_s1 stack2 tail P) ∗ True)%I.

Definition encoderBytesExactOutputFrame `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (old_x6 old_s0 old_s1 stack2 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  encoderBytesExactOutputResources size sp ret old_s0 old_s1 stack2 P.

Definition encoderBytesExactSuffixSpec `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (old_x6 old_s0 old_s1 stack2 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15c90) ∗
   "x2" ↦ᵣ RVal_Bits (sp - BV 64 32)%bv ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 48)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   bv_unsigned (sp - BV 64 48)%bv ↦ₘ∗
     writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)) ∗
   (bv_unsigned sp - 40) ↦ₘ (BV 64 0x15c90) ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents data size bytes tail) ∗
   encoderBytesExactSuffixFrame data size sp ret bytes
     old_x6 old_s0 old_s1 stack2 tail P ∗ True)%I.

Definition encoderBytesExactSpec `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_x6 old_s0 old_s1
       stack0 stack1 stack2 stack3 stack4 stack5 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x8" ↦ᵣ RVal_Bits old_s0 ∗ "x9" ↦ᵣ RVal_Bits old_s1 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    (bv_unsigned sp - 48) ↦ₘ stack0 ∗
    (bv_unsigned sp - 40) ↦ₘ stack1 ∗
    (bv_unsigned sp - 32) ↦ₘ stack2 ∗
    (bv_unsigned sp - 24) ↦ₘ stack3 ∗
    (bv_unsigned sp - 16) ↦ₘ stack4 ∗
    (bv_unsigned sp - 8) ↦ₘ stack5 ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)))
        (writeOutputEvents data size bytes tail)) ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (encoderBytesExactPost data size sp ret bytes
        old_x6 old_s0 old_s1 stack2 tail P))%I.

Global Instance : LithiumUnfold (@encoderBytesExactOutputResources) := I.
Global Instance : LithiumUnfold (@encoderBytesExactPost) := I.
Global Instance : LithiumUnfold (@encoderBytesExactSuffixFrame) := I.
Global Instance : LithiumUnfold (@encoderBytesExactOutputFrame) := I.
Global Instance : LithiumUnfold (@encoderBytesExactSuffixSpec) := I.
Global Instance : LithiumUnfold (@encoderBytesExactSpec) := I.

#[local] Hint Rewrite bv_sign_extend_64_idemp : isla_coq_rewrite.

Lemma encoder_bytes_exact_suffix_correct `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (old_x6 old_s0 old_s1 stack2 : bv 64)
    (tail : spec) (P : iProp Sigma) :
  instr 0x15c90 (Some a15c90) -∗ instr 0x15c94 (Some a15c94) -∗
  instr 0x15c98 (Some a15c98) -∗ instr 0x15c9c (Some a15c9c) -∗
  instr 0x15ca0 (Some a15ca0) -∗ instr 0x15ca4 (Some a15ca4) -∗
  instr 0x15ca8 (Some a15ca8) -∗ instr 0x15cac (Some a15cac) -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c90 (encoderBytesExactSuffixSpec data size sp ret bytes
    old_x6 old_s0 old_s1 stack2 tail P).
Proof.
  iStartProof. iIntros "#H90 #H94 #H98 #H9c #Ha0 #Ha4 #Ha8 #Hac #HoutputCode".
  iAssert (□ instr_pre 0x10190
    (writeOutputTraceSpec data size ret bytes tail
      (encoderBytesExactOutputFrame data size sp ret bytes
        old_x6 old_s0 old_s1 stack2 tail P)))%I as "#Houtput".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply write_output_trace_correct. iExact "HoutputCode". }
  liARun.
  Unshelve. all: prepare_sidecond; try assumption; try rewrite bv_sign_extend_idemp;
    try bv_solve; try lia.
  all: try (bv_simplify_arith select (bv_extract 0 4 sp = _)).
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try bv_solve.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  all: try (change (Z.to_N (bv_unsigned size) =
    Z.to_N (Z.of_nat (length bytes))); f_equal; lia).
  Unshelve. all: try liARun.
  all: try (unfold encoderBytesExactPost, encoderBytesExactOutputFrame;
    reflexivity).
  all: try (rewrite /encoderBytesExactOutputResources
    /encoderBytesExactPost; iFrame).
  all: try unLET.
  all: zesu_run.
Qed.

Definition encoderBytesIntExactCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (data size sp ret : bv 64) (bytes : list (bv 8))
      (old_x6 old_s0 old_s1 stack2 : bv 64) (tail : spec) (P : iProp Sigma),
    encoderIntExactSpec size (sp - BV 64 32)%bv (BV 64 0x15c90)
      (writeOutputEvents data size bytes tail)
      (encoderBytesExactSuffixFrame data size sp ret bytes
        old_x6 old_s0 old_s1 stack2 tail P))%I.

Global Instance : LithiumUnfold (@encoderBytesIntExactCallSpec) := I.

Lemma encoder_bytes_int_exact_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 encoderBytesIntExactCallSpec.
Proof.
  iStartProof. iIntros "#HintCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext. rewrite instr_pre'_eq.
  iIntros "Hspec". iDestruct "Hspec" as
    (data size sp ret bytes old_x6 old_s0 old_s1 stack2 tail P) "Hspec".
  iPoseProof (encoder_int_exact_correct size (sp - BV 64 32)%bv
    (BV 64 0x15c90) (writeOutputEvents data size bytes tail)
    (encoderBytesExactSuffixFrame data size sp ret bytes
      old_x6 old_s0 old_s1 stack2 tail P) with
    "HintCode HoutputCode") as "Hbody".
  rewrite instr_pre'_eq. iApply ("Hbody" with "Hspec").
Qed.

Lemma encoder_bytes_exact_correct `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c6c (encoderBytesExactSpec data size sp ret bytes tail P).
Proof.
  move => * /=. iStartProof.
  iIntros "_ #HbytesCode #HintCode #HoutputCode".
  iPoseProof (encoder_bytes_int_exact_call_pre with
    "HintCode HoutputCode") as "#Hint".
  iEval (simpl) in "HbytesCode".
  iDestruct "HbytesCode" as
    "(#H00 & #H04 & #H08 & #H0c & #H10 & #H14 & #H18 & #H1c &
      #H20 & #H24 & #H28 & #H2c & #H30 & #H34 & #H38 & #H3c & #H40 & _)".
  liARun.
  iAssert (□ instr_pre 0x15c90
    (encoderBytesExactSuffixSpec data size sp ret bytes
      old_x6 old_s0 old_s1 stack2 tail P))%I as "#Hsuffix".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply (encoder_bytes_exact_suffix_correct with
      "H24 H28 H2c H30 H34 H38 H3c H40 HoutputCode"). }
  iClear "H24 H28 H2c H30 H34 H38 H3c H40 HintCode HoutputCode".
  iExists (P, tail, stack2, old_s1, old_s0, old_x6, bytes,
    ret, sp, size, data, tt)ₗ.
  liARun.
  Unshelve. all: prepare_sidecond; try assumption;
    try (bv_simplify_arith select (bv_extract 0 4 sp = _));
    try (bv_simplify_arith select (bv_extract 0 3 sp = _));
    try rewrite bv_sign_extend_idemp; try bv_solve; try lia.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  all: try (replace (bv_unsigned (sp - BV 64 32 - BV 64 16)%bv)
    with (bv_unsigned (sp - BV 64 48)%bv) by bv_solve; reflexivity).
  Unshelve. all: try exact inhabitant.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Print Assumptions encoder_bytes_exact_correct.

Definition encoderBytesExactCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (data size sp ret : bv 64) (bytes : list (bv 8))
      (tail : spec) (P : iProp Sigma),
    encoderBytesExactSpec data size sp ret bytes tail P)%I.

Global Instance : LithiumUnfold (@encoderBytesExactCallSpec) := I.

Lemma encoder_bytes_exact_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c6c encoderBytesExactCallSpec.
Proof.
  iStartProof. iIntros "#HbytesCode #HintCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext. rewrite instr_pre'_eq.
  iIntros "Hspec". iDestruct "Hspec" as (data size sp ret bytes tail P) "Hspec".
  iPoseProof (encoder_bytes_exact_correct data size sp ret bytes tail P with
    "HbytesCode HintCode HoutputCode") as "Hbody".
  rewrite instr_pre'_eq. iApply ("Hbody" with "Hspec").
Qed.

Print Assumptions encoder_bytes_exact_call_pre.

Definition encoderBytesExactReturn `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (old_x6 old_s0 old_s1 stack2 : bv 64) (tail : spec) : iProp Sigma :=
  encoderBytesExactPost data size sp ret bytes
    old_x6 old_s0 old_s1 stack2 tail True%I.

Definition zesuEncoderBytesExactCallSpec `{!islaG Sigma} `{!threadG}
    : iProp Sigma :=
  (∃ (data size sp ret : bv 64) (bytes : list (bv 8))
      (old_x5 old_x6 old_s0 old_s1
       stack0 stack1 stack2 stack3 stack4 stack5 : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x8" ↦ᵣ RVal_Bits old_s0 ∗ "x9" ↦ᵣ RVal_Bits old_s1 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    (bv_unsigned sp - 48) ↦ₘ stack0 ∗
    (bv_unsigned sp - 40) ↦ₘ stack1 ∗
    (bv_unsigned sp - 32) ↦ₘ stack2 ∗
    (bv_unsigned sp - 24) ↦ₘ stack3 ∗
    (bv_unsigned sp - 16) ↦ₘ stack4 ∗
    (bv_unsigned sp - 8) ↦ₘ stack5 ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)))
        (writeOutputEvents data size bytes tail)) ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < machineRamEnd defaultMap⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
    instr_pre (bv_unsigned ret)
      (encoderBytesExactReturn data size sp ret bytes
        old_x6 old_s0 old_s1 stack2 tail) ∗ True)%I.

Global Instance : LithiumUnfold (@encoderBytesExactReturn) := I.
Global Instance : LithiumUnfold (@zesuEncoderBytesExactCallSpec) := I.

Lemma encoder_bytes_exact_entry_to_framed `{!islaG Sigma} `{!threadG} :
  zesuEncoderBytesExactCallSpec -∗
  ∃ (data size sp ret : bv 64) (bytes : list (bv 8)) (tail : spec),
    encoderBytesExactSpec data size sp ret bytes tail True%I.
Proof.
  iStartProof. iIntros "Hexact".
  iEval (unfold zesuEncoderBytesExactCallSpec) in "Hexact".
  iDestruct "Hexact" as
    (data size sp ret bytes old_x5 old_x6 old_s0 old_s1
      stack0 stack1 stack2 stack3 stack4 stack5 tail)
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack0 &
      Hstack1 & Hstack2 & Hstack3 & Hstack4 & Hstack5 & Hbytes & %Hsize &
      Hmmio & Htrace & %Hsp4 & %Hsp3 & %Hlower & %Hupper & %Hret0 &
      %Hret1 & %Hret2 & Hreturn & _)".
  iExists data, size, sp, ret, bytes, tail.
  iEval (unfold encoderBytesExactSpec).
  iExists old_x5, old_x6, old_s0, old_s1,
    stack0, stack1, stack2, stack3, stack4, stack5.
  iEval (unfold encoderBytesExactReturn) in "Hreturn".
  iFrame.
  repeat iSplit; iPureIntro; assumption.
Qed.

Print Assumptions encoder_bytes_exact_entry_to_framed.

Lemma encoder_bytes_exact_entry_from_framed `{!islaG Sigma} `{!threadG} :
  (∃ (data size sp ret : bv 64) (bytes : list (bv 8)) (tail : spec),
    encoderBytesExactSpec data size sp ret bytes tail True%I) -∗
  zesuEncoderBytesExactCallSpec.
Proof.
  iStartProof. iIntros "Hframed".
  iDestruct "Hframed" as (data size sp ret bytes tail) "Hframed".
  iEval (unfold encoderBytesExactSpec) in "Hframed".
  iDestruct "Hframed" as
    (old_x5 old_x6 old_s0 old_s1 stack0 stack1 stack2 stack3 stack4 stack5)
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack0 &
      Hstack1 & Hstack2 & Hstack3 & Hstack4 & Hstack5 & Hbytes & %Hsize &
      Hmmio & Htrace & %Hsp4 & %Hsp3 & %Hlower & %Hupper & %Hret0 &
      %Hret1 & %Hret2 & Hreturn)".
  iEval (unfold zesuEncoderBytesExactCallSpec).
  iExists data, size, sp, ret, bytes, old_x5, old_x6, old_s0, old_s1,
    stack0, stack1, stack2, stack3, stack4, stack5, tail.
  iEval (unfold encoderBytesExactReturn).
  iFrame.
  iDestruct "Hreturn" as "[_ Hreturn]".
  repeat (iSplit; first (iPureIntro; assumption)).
  iFrame.
Qed.

Lemma encoder_bytes_exact_entry_equiv `{!islaG Sigma} `{!threadG} :
  zesuEncoderBytesExactCallSpec ⊣⊢
  (∃ (data size sp ret : bv 64) (bytes : list (bv 8)) (tail : spec),
    encoderBytesExactSpec data size sp ret bytes tail True%I).
Proof.
  iSplit.
  - iApply encoder_bytes_exact_entry_to_framed.
  - iApply encoder_bytes_exact_entry_from_framed.
Qed.

Print Assumptions encoder_bytes_exact_entry_equiv.

Lemma encoder_bytes_exact_body_from_framed `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c6c zesuEncoderBytesExactCallSpec.
Proof.
  iStartProof. iIntros "HbytesCode HintCode HoutputCode".
  rewrite instr_pre'_eq. iIntros "Hexact".
  iDestruct (encoder_bytes_exact_entry_to_framed with "Hexact") as
    (data size sp ret bytes tail) "Hframed".
  iPoseProof (encoder_bytes_exact_correct data size sp ret bytes tail True%I
    with "HbytesCode HintCode HoutputCode") as "Hbody".
  rewrite instr_pre'_eq. iApply ("Hbody" with "Hframed").
Qed.

Print Assumptions encoder_bytes_exact_body_from_framed.

Lemma zesu_encoder_bytes_exact_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c6c zesuEncoderBytesExactCallSpec.
Proof.
  iStartProof. iIntros "HbytesCode HintCode HoutputCode".
  iApply (encoder_bytes_exact_body_from_framed with
    "HbytesCode HintCode HoutputCode").
Qed.

Print Assumptions zesu_encoder_bytes_exact_call_correct.

Lemma zesu_encoder_bytes_exact_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c6c zesuEncoderBytesExactCallSpec.
Proof.
  iStartProof. iIntros "#HbytesCode #HintCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply (zesu_encoder_bytes_exact_call_correct with
    "HbytesCode HintCode HoutputCode").
Qed.

Print Assumptions zesu_encoder_bytes_exact_call_pre.

Lemma encoder_bytes_uninit_48_to_words `{!islaG Sigma} (sp : bv 64) :
  (bv_unsigned sp - 48) ↦ₘ? 48 -∗
  ∃ w0 w1 w2 w3 w4 w5 : bv 64,
    (bv_unsigned sp - 48) ↦ₘ w0 ∗ (bv_unsigned sp - 40) ↦ₘ w1 ∗
    (bv_unsigned sp - 32) ↦ₘ w2 ∗ (bv_unsigned sp - 24) ↦ₘ w3 ∗
    (bv_unsigned sp - 16) ↦ₘ w4 ∗ (bv_unsigned sp - 8) ↦ₘ w5.
Proof.
  iIntros "Hstack".
  iDestruct (mem_mapsto_uninit_split 8 with "Hstack") as "[H0 Hstack]"; [lia|].
  iEval (replace (bv_unsigned sp - 48 + 8) with (bv_unsigned sp - 40) by lia) in "Hstack".
  iDestruct (mem_mapsto_uninit_split 8 with "Hstack") as "[H1 Hstack]"; [lia|].
  iEval (replace (bv_unsigned sp - 40 + 8) with (bv_unsigned sp - 32) by lia) in "Hstack".
  iDestruct (mem_mapsto_uninit_split 8 with "Hstack") as "[H2 Hstack]"; [lia|].
  iEval (replace (bv_unsigned sp - 32 + 8) with (bv_unsigned sp - 24) by lia) in "Hstack".
  iDestruct (mem_mapsto_uninit_split 8 with "Hstack") as "[H3 Hstack]"; [lia|].
  iEval (replace (bv_unsigned sp - 24 + 8) with (bv_unsigned sp - 16) by lia) in "Hstack".
  iDestruct (mem_mapsto_uninit_split 8 with "Hstack") as "[H4 H5]"; [lia|].
  iEval (replace (bv_unsigned sp - 16 + 8) with (bv_unsigned sp - 8) by lia) in "H5".
  iDestruct (mem_mapsto_uninit_to_mapsto with "H0") as (? w0 ->) "H0".
  iDestruct (mem_mapsto_uninit_to_mapsto with "H1") as (? w1 ->) "H1".
  iDestruct (mem_mapsto_uninit_to_mapsto with "H2") as (? w2 ->) "H2".
  iDestruct (mem_mapsto_uninit_to_mapsto with "H3") as (? w3 ->) "H3".
  iDestruct (mem_mapsto_uninit_to_mapsto with "H4") as (? w4 ->) "H4".
  iDestruct (mem_mapsto_uninit_to_mapsto with "H5") as (? w5 ->) "H5".
  iExists w0, w1, w2, w3, w4, w5. iFrame.
Qed.

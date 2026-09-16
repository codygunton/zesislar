Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeBooleanResume.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeJumpHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeCallSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneCallSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneCall.
From IslaTraces.write_success_04 Require Import instrs.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.

Import ZesuSsz.Automation.Calls.FramedContinuations.

Definition encoderOptionalU64ExactReturn `{!islaG Sigma} `{!threadG}
    (pointer sp ret old_x8 : bv 64) (bytes : list (bv 8))
    (tail : spec) (outcome : option (bv 64)) : iProp Sigma :=
  match outcome with
  | Some _ => optionalU64SomeExactPost sp ret old_x8 tail
      (optionalU64SomeExactSourceFrame pointer bytes True)
  | None => optionalU64NoneExactCallPost pointer sp ret bytes tail
      ("x8" ↦ᵣ RVal_Bits old_x8)
  end.

Definition zesuEncoderOptionalU64ExactCallSpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (pointer sp ret old_x5 old_x6 old_x8 old_x11 : bv 64)
      (tag : bv 8) (bytes : list (bv 8)) (tail : spec)
      (outcome : option (bv 64)),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x8" ↦ᵣ RVal_Bits old_x8 ∗ "x10" ↦ᵣ RVal_Bits pointer ∗
    "x11" ↦ᵣ RVal_Bits old_x11 ∗
    (bv_unsigned sp - 32) ↦ₘ? 32 ∗ bv_unsigned pointer ↦ₘ∗ bytes ∗
    ⌜bytes !! 8%nat = Some tag⌝ ∗
    ⌜match outcome with
      | Some value => tag <> BV 8 0 /\
          value = Z_to_bv 64 (little_endian_to_bv 8 (take 8 bytes)) /\
          (8 <= length bytes)%nat /\ bv_extract 0 3 pointer = BV 3 0
      | None => tag = BV 8 0
      end⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned pointer⌝ ∗
    ⌜bv_unsigned pointer + Z.of_nat (length bytes) < machineRamEnd defaultMap⌝ ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (match outcome with
       | Some value =>
           writeOutputEvents (sp - BV 64 25)%bv (BV 64 1)
             (writeSuccessBooleanWordPayload (BV 64 1))
             (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
               (writeSuccessPrivateBytes
                 (writeSuccessEncodeU64 (bv_unsigned value))) tail)
       | None =>
           writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
             (writeSuccessBooleanWordPayload (BV 64 0)) tail
       end) ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned sp - 32⌝ ∗
    ⌜bv_unsigned sp < machineRamEnd defaultMap⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
    instr_pre (bv_unsigned ret)
      (encoderOptionalU64ExactReturn pointer sp ret old_x8 bytes tail outcome) ∗
    True)%I.

Global Instance : LithiumUnfold (@encoderOptionalU64ExactReturn) := I.
Global Instance : LithiumUnfold (@zesuEncoderOptionalU64ExactCallSpec) := I.

Lemma encoder_optional_u64_exact_body_from_framed
    `{!islaG Sigma} `{!threadG} :
  (∀ (pointer value sp ret old_x5 old_x6 old_x8 old_x11 : bv 64)
     (tag : bv 8) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma),
     instr_body 0x15bc8 (optionalU64SomeExactCallEntry pointer value sp ret
       old_x5 old_x6 old_x8 old_x11 tag bytes tail P)) -∗
  (∀ (pointer sp ret old_x5 old_x6 old_x11 : bv 64)
     (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma),
     instr_body 0x15bc8 (optionalU64NoneExactCallEntry pointer sp ret
       old_x5 old_x6 old_x11 bytes tail P)) -∗
  instr_body 0x15bc8 zesuEncoderOptionalU64ExactCallSpec.
Proof.
  iStartProof. iIntros "Hsome Hnone".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (unfold zesuEncoderOptionalU64ExactCallSpec) in "Hentry".
  iDestruct "Hentry" as
    (pointer sp ret old_x5 old_x6 old_x8 old_x11 tag bytes tail outcome)
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H10 & H11 & Hstack & Hsource &
      %Htag & %Houtcome & %Hlower & %Hupper & Hmmio & Htrace &
      %Hsp4 & %Hmin & %Hmax & %Hret0 & %Hret1 & %Hret2 & Hreturn & _)".
  destruct outcome as [value|].
  - destruct Houtcome as (Hnonzero & Hvalue & Hlength & Hpointer).
    iSpecialize ("Hsome" $! pointer value sp ret old_x5 old_x6 old_x8
      old_x11 tag bytes tail True%I).
    rewrite instr_pre'_eq. iApply "Hsome".
    rewrite /optionalU64SomeExactCallEntry
      /optionalU64SomeExactCallContext /encoderOptionalU64ExactReturn /=.
    zesu_run.
    all: try (bv_simplify Hsp4; bv_solve).
    iSplit; first (rewrite instr_pre'_eq; iExact "Hreturn"). done.
  - subst tag.
    iSpecialize ("Hnone" $! pointer sp ret old_x5 old_x6 old_x11 bytes tail
      ("x8" ↦ᵣ RVal_Bits old_x8)%I).
    rewrite instr_pre'_eq. iApply "Hnone".
    rewrite /optionalU64NoneExactCallEntry /encoderOptionalU64ExactReturn /=.
    zesu_run.
    iSplit; first (rewrite instr_pre'_eq; iExact "Hreturn"). done.
Qed.

Lemma zesu_encoder_optional_u64_exact_call_correct
    `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bc8 zesuEncoderOptionalU64ExactCallSpec.
Proof.
  iStartProof. iIntros "#Hoptional #Hboolean #Hint #Houtput".
  iApply encoder_optional_u64_exact_body_from_framed.
  - iIntros (pointer value sp ret old_x5 old_x6 old_x8 old_x11 tag bytes tail P).
    iApply (optional_u64_some_exact_call_correct with
      "Hoptional Hboolean Hint Houtput").
  - iIntros (pointer sp ret old_x5 old_x6 old_x11 bytes tail P).
    iApply (optional_u64_none_exact_call_correct with
      "Hoptional Hboolean Houtput").
Qed.

Lemma zesu_encoder_optional_u64_exact_call_pre
    `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64ExactCallSpec.
Proof.
  iStartProof. iIntros "#Hoptional #Hboolean #Hint #Houtput".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_optional_u64_exact_call_correct; iAssumption.
Qed.

Lemma encoder_optional_u64_exact_some_return_frame
    `{!islaG Sigma} `{!threadG}
    (pointer value sp ret old_x8 : bv 64) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  encoderOptionalU64ExactReturn pointer sp ret old_x8 bytes tail (Some value) ∗ P -∗
  optionalU64SomeExactPost sp ret old_x8 tail
    (optionalU64SomeExactSourceFrame pointer bytes P).
Proof.
  iStartProof. iIntros "[Hreturn HP]".
  rewrite /encoderOptionalU64ExactReturn /optionalU64SomeExactPost
    /optionalU64SomeExactSourceFrame /=.
  iDestruct "Hreturn" as
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H10 & H11 & Hstack & Hmmio &
      Htrace & Hsource & _)".
  iDestruct "Hsource" as "(Hsource & _ & _)".
  iFrame "∗".
Qed.

Lemma encoder_optional_u64_exact_some_adapter_from_closed
    `{!islaG Sigma} `{!threadG}
    (pointer value sp ret old_x5 old_x6 old_x8 old_x11 : bv 64)
    (tag : bv 8) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_body 0x15bc8 zesuEncoderOptionalU64ExactCallSpec -∗
  instr_body 0x15bc8 (optionalU64SomeExactCallEntry pointer value sp ret
    old_x5 old_x6 old_x8 old_x11 tag bytes tail P).
Proof.
  iStartProof. iIntros "Hcallee".
  iApply (instr_pre_wand 0x15bc8 0x15bc8 false false with "Hcallee");
    [done | done |].
  iIntros "Hentry". iDestruct "Hentry" as
    "(Hsys & H1 & H2 & H8 & H10 & H11 & Hsource & Hstack & %Htag &
      %Hnonzero & %Hvalue & %Hlength & %Hpointer & %Hlower & %Hupper &
      %Hsp4 & %Hmin & %Hmax & Hcontext & _)".
  iDestruct "Hcontext" as
    "(H5 & H6 & Hmmio & Htrace & %HcontextSp4 & %Halign & %HcontextMin &
      %HcontextMax & %Hret0 & %Hret1 & %Hret2 & HP & Hnext & _)".
  iExists pointer, sp, ret, old_x5, old_x6, old_x8, old_x11, tag, bytes,
    tail, (Some value).
  zesu_run.
  iSplit.
  - iIntros "Hreturn".
    iApply encoder_optional_u64_exact_some_return_frame.
    iFrame "Hreturn HP".
  - done.
  Unshelve. exact old_x8.
Qed.

Lemma encoder_optional_u64_exact_none_return_frame
    `{!islaG Sigma} `{!threadG}
    (pointer sp ret old_x8 : bv 64) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  encoderOptionalU64ExactReturn pointer sp ret old_x8 bytes tail None ∗ P -∗
  optionalU64NoneExactCallPost pointer sp ret bytes tail
    (("x8" ↦ᵣ RVal_Bits old_x8) ∗ P).
Proof.
  iStartProof. iIntros "[Hreturn HP]".
  rewrite /encoderOptionalU64ExactReturn /optionalU64NoneExactCallPost
    /optionalU64NoneObjectFrame /=.
  iDestruct "Hreturn" as
    "(Hsys & H1 & H2 & H5 & H6 & H10 & H11 & Hstack & Hmmio & Htrace &
      Hsource & _)".
  iDestruct "Hsource" as "(Hsource & H8 & _)".
  iFrame "∗".
Qed.

Lemma encoder_optional_u64_exact_none_adapter_from_closed
    `{!islaG Sigma} `{!threadG}
    (pointer sp ret old_x5 old_x6 old_x8 old_x11 : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_body 0x15bc8 zesuEncoderOptionalU64ExactCallSpec -∗
  instr_body 0x15bc8 (optionalU64NoneExactCallEntry pointer sp ret old_x5
    old_x6 old_x11 bytes tail (("x8" ↦ᵣ RVal_Bits old_x8) ∗ P)).
Proof.
  iStartProof. iIntros "Hcallee".
  iApply (instr_pre_wand 0x15bc8 0x15bc8 false false with "Hcallee");
    [done | done |].
  iIntros "Hentry". iDestruct "Hentry" as
    "(Hsys & H1 & H2 & H5 & H6 & H10 & H11 & Hstack & Hsource & %Htag &
      %Hlower & %Hupper & Hmmio & Htrace & %Hsp4 & %Hsp3 & %Hmin & %Hmax &
      %Hret0 & %Hret1 & %Hret2 & HP & Hnext & _)".
  iDestruct "HP" as "[H8 HP]".
  iExists pointer, sp, ret, old_x5, old_x6, old_x8, old_x11, (BV 8 0),
    bytes, tail, None.
  zesu_run.
  iSplit.
  - iIntros "Hreturn".
    iApply encoder_optional_u64_exact_none_return_frame.
    iFrame "Hreturn HP".
  - done.
Qed.

Print Assumptions encoder_optional_u64_exact_body_from_framed.
Print Assumptions zesu_encoder_optional_u64_exact_call_correct.
Print Assumptions zesu_encoder_optional_u64_exact_call_pre.
Print Assumptions encoder_optional_u64_exact_some_return_frame.
Print Assumptions encoder_optional_u64_exact_some_adapter_from_closed.
Print Assumptions encoder_optional_u64_exact_none_return_frame.
Print Assumptions encoder_optional_u64_exact_none_adapter_from_closed.

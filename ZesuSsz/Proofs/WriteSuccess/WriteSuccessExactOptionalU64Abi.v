Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Calls.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64AbiSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeCallSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneCallSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneCall.
From IslaTraces.write_success_04 Require Import instrs.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.

Import ZesuSsz.Automation.Calls.FramedContinuations.

Lemma optional_u64_some_exact_abi_adapter `{!islaG Sigma} `{!threadG} :
  (∀ (pointer value sp ret old5 old6 old8 old11 : bv 64)
     (tag : bv 8) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma),
     instr_body 0x15bc8 (optionalU64SomeExactCallEntry pointer value sp ret
       old5 old6 old8 old11 tag bytes tail P)) -∗
  instr_body 0x15bc8 zesuEncoderOptionalU64ExactSomeCallSpec.
Proof.
  iStartProof. iIntros "Hcaller".
  rewrite instr_pre'_eq. iIntros "Hspec".
  iEval (unfold zesuEncoderOptionalU64ExactSomeCallSpec) in "Hspec".
  zesu_unpack_call "Hspec".
  iDestruct "Hrest" as (value tag tail)
    "(Hvalue & Htagmem & %Htag & %Hdataalign & %Hdatamin &
      %Hdatamax & Hmmio & Htrace & Hret)".
  subst r10 r11 r12 r13 r14 r15 r16 r17.
  apply valu_has_bits_shape in Hr8 as (b8 & ->).
  iEval (rewrite /tmp_registers reg_col_cons reg_col_cons) in "Htmp".
  iDestruct "Htmp" as "(H5 & H6 & Htmp)".
  iDestruct "H5" as (r5 Hr5) "R5".
  iDestruct "H6" as (r6 Hr6) "R6".
  apply valu_has_bits_shape in Hr5 as (b5 & ->).
  apply valu_has_bits_shape in Hr6 as (b6 & ->).
  iSpecialize ("Hcaller" $! b10 value sp ret b5 b6 b8 b11 tag
    (bytes_of_u64s [value] ++ [tag]) tail
    (@zesu_call_preserved_frame Sigma islaG0 H r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
      b12 b13 b14 b15 b16 b17)).
  iApply "Hcaller".
  zesu_run.
  Unshelve. all: zesu_finish.
Qed.
Print Assumptions optional_u64_some_exact_abi_adapter.

Lemma optional_u64_none_exact_abi_adapter `{!islaG Sigma} `{!threadG} :
  (∀ (pointer sp ret old5 old6 old11 : bv 64)
     (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma),
     instr_body 0x15bc8 (optionalU64NoneExactCallEntry pointer sp ret
       old5 old6 old11 bytes tail P)) -∗
  instr_body 0x15bc8 zesuEncoderOptionalU64ExactNoneCallSpec.
Proof.
  iStartProof. iIntros "Hcaller".
  rewrite instr_pre'_eq. iIntros "Hspec".
  iEval (unfold zesuEncoderOptionalU64ExactNoneCallSpec) in "Hspec".
  zesu_unpack_call "Hspec".
  iDestruct "Hrest" as (value tag tail)
    "(Hvalue & Htagmem & %Htag & %Hdataalign & %Hdatamin &
      %Hdatamax & Hmmio & Htrace & Hret)".
  subst r10 r11 r12 r13 r14 r15 r16 r17 tag.
  apply valu_has_bits_shape in Hr8 as (b8 & ->).
  iEval (rewrite /tmp_registers reg_col_cons reg_col_cons) in "Htmp".
  iDestruct "Htmp" as "(H5 & H6 & Htmp)".
  iDestruct "H5" as (r5 Hr5) "R5".
  iDestruct "H6" as (r6 Hr6) "R6".
  apply valu_has_bits_shape in Hr5 as (b5 & ->).
  apply valu_has_bits_shape in Hr6 as (b6 & ->).
  iSpecialize ("Hcaller" $! b10 sp ret b5 b6 b11
    (bytes_of_u64s [value] ++ [BV 8 0]) tail
    ("x8" ↦ᵣ RVal_Bits b8 ∗
      @zesu_call_preserved_frame Sigma islaG0 H r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27
        b12 b13 b14 b15 b16 b17)%I).
  iApply "Hcaller".
  zesu_run.
  Unshelve. all: zesu_finish.
Qed.
Print Assumptions optional_u64_none_exact_abi_adapter.

Lemma optional_u64_some_exact_abi_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bc8 zesuEncoderOptionalU64ExactSomeCallSpec.
Proof.
  iStartProof. iIntros "#Hoptional #Hboolean #Hint #Houtput".
  iApply optional_u64_some_exact_abi_adapter.
  iIntros (pointer value sp ret old5 old6 old8 old11 tag bytes tail P).
  iApply optional_u64_some_exact_call_correct; iAssumption.
Qed.
Print Assumptions optional_u64_some_exact_abi_correct.

Lemma optional_u64_none_exact_abi_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bc8 zesuEncoderOptionalU64ExactNoneCallSpec.
Proof.
  iStartProof. iIntros "#Hoptional #Hboolean #Hint #Houtput".
  iApply optional_u64_none_exact_abi_adapter.
  iIntros (pointer sp ret old5 old6 old11 bytes tail P).
  iApply optional_u64_none_exact_call_correct; iAssumption.
Qed.
Print Assumptions optional_u64_none_exact_abi_correct.

Lemma optional_u64_exact_abi_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bc8 zesuEncoderOptionalU64ExactPayloadCallSpec.
Proof.
  iStartProof. iIntros "#Hoptional #Hboolean #Hint #Houtput".
  iPoseProof (optional_u64_some_exact_abi_correct
    with "Hoptional Hboolean Hint Houtput") as "HsomeBody".
  iPoseProof (optional_u64_none_exact_abi_correct
    with "Hoptional Hboolean Hint Houtput") as "HnoneBody".
  iEval (rewrite instr_pre'_eq) in "HsomeBody HnoneBody".
  rewrite instr_pre'_eq /zesuEncoderOptionalU64ExactPayloadCallSpec.
  iIntros "[Hsome | Hnone]".
  - iApply "HsomeBody". iExact "Hsome".
  - iApply "HnoneBody". iExact "Hnone".
Qed.
Print Assumptions optional_u64_exact_abi_correct.

Lemma optional_u64_exact_abi_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64ExactPayloadCallSpec.
Proof.
  iStartProof. iIntros "#Hoptional #Hboolean #Hint #Houtput".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply optional_u64_exact_abi_correct; iAssumption.
Qed.
Print Assumptions optional_u64_exact_abi_pre.

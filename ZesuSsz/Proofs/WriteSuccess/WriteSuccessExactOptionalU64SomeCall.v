Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomePrefix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeBooleanJump.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeBooleanResume.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeResume.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeJumpHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeCallSpec.
From IslaTraces.write_success_04 Require Import instrs.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.

Lemma optional_u64_some_exact_call_correct `{!islaG Sigma} `{!threadG}
    (pointer value sp ret old_x5 old_x6 old_x8 old_x11 : bv 64)
    (tag : bv 8) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bc8 (optionalU64SomeExactCallEntry pointer value sp ret old_x5
    old_x6 old_x8 old_x11 tag bytes tail P).
Proof.
  iStartProof. iIntros "#Hoptional #Hboolean #Hint #Houtput".
  iDestruct (big_sepL_take_drop _ _ 2 with "Hoptional") as "[#Hbranch #HafterBranch]".
  iDestruct (big_sepL_take_drop _ _ 6 with "HafterBranch") as "[#Hprefix #HafterPrefix]".
  iDestruct (big_sepL_take_drop _ _ 1 with "HafterPrefix") as "[#HjumpCode #HafterJump]".
  iDestruct (big_sepL_take_drop _ _ 6 with "HafterJump") as "[#Hsuffix _]".
  iPoseProof (optional_u64_some_exact_resume value sp ret (BV 64 (mapIoContextAddress defaultMap))
    old_x6 old_x8 (sp - BV 64 25)%bv (BV 64 1) tail
    (optionalU64SomeExactBooleanScratch sp
      (optionalU64SomeExactSourceFrame pointer bytes P))
    with "Hsuffix Hint Houtput") as "Hresume".
  iPoseProof (optional_u64_some_exact_boolean_resume_handoff with "Hresume") as "Hreturn".
  iPoseProof (encoder_boolean_exact_framed_correct (BV 64 1) (sp - BV 64 16)%bv
    (BV 64 0x15bec) old_x5 (bv_zero_extend 64 tag) _
    (optionalU64SomeExactBooleanResumeFrame value sp ret old_x6 old_x8 tail
      (optionalU64SomeExactSourceFrame pointer bytes P))
    with "Hboolean Houtput") as "HbooleanBody".
  iPoseProof (optional_u64_some_exact_boolean_jump with "[HjumpCode] HbooleanBody") as "Hjump".
  { iEval (simpl) in "HjumpCode". iDestruct "HjumpCode" as "[$ _]". }
  iPoseProof (optional_u64_some_exact_jump_handoff with "Hjump Hreturn") as "Hhandoff".
  iPoseProof (optional_u64_some_exact_entry_to_boolean_jump pointer value sp ret
    old_x8 old_x11 tag bytes (optionalU64SomeExactCallContext pointer value sp ret
      old_x5 old_x6 old_x8 bytes tail P) with "Hbranch Hprefix") as "Hentry".
  iApply (optional_u64_some_exact_call_entry with "Hentry Hhandoff").
Qed.

Print Assumptions optional_u64_some_exact_call_correct.

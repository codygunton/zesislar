Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsU256 WriteSuccessExactAuthorizationsThirdU256
  WriteSuccessExactAuthorizationsU256Next WriteSuccessExactAuthorizationsBodyPost
  WriteSuccessExactAuthorizationsPhases.

Lemma authorization_last_u256_correct `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  length bytes = 144%nat ->
  ([∗ list] instruction ∈ IslaTraces.write_success_81.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15614 (authorizationBodyPost sp bytes tail P) -∗
  instr_body 0x155fc (authorizationU256Post sp bytes 32 (BV 64 0x155fc)
    (authorizationExactPhaseEvents 5 sp bytes tail)
    ("x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗ P ∗ True)%I).
Proof.
  intros Hlen. iStartProof. iIntros "#Hcaller #Hencoder #Houtput Hfinal".
  iAssert (instr_pre 0x15614 (authorizationU256Post sp bytes 64 (BV 64 0x15614)
    tail ("x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗ P ∗ True)%I))
    with "[Hfinal]" as "Hnext".
  { iApply (instr_pre_wand 0x15614 0x15614 false true with "Hfinal"); [done | done |].
    iIntros "Hpost". iApply (authorization_u256_to_body_post with "Hpost"). }
  iPoseProof (authorization_third_u256_correct sp (BV 64 0x155fc) (BV 64 0x2401a0b8)
    bytes tail ("x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗ P ∗ True)%I
    with "Hcaller Hencoder Houtput") as "Hcallee".
  iApply (instr_pre_wand 0x155fc 0x155fc false false with "Hcallee"); [done | done |].
  iIntros "Hpost". iEval (rewrite (authorization_phase_five sp bytes tail Hlen)
    authorization_phase_six) in "Hpost".
  iApply (authorization_u256_to_next_u256 sp bytes 32 (BV 64 0x155fc)
    64 (BV 64 0x15614) tail
    ("x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗ P ∗ True)%I with "Hpost Hnext").
Qed.
Print Assumptions authorization_last_u256_correct.

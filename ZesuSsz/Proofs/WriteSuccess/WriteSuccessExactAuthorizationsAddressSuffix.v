Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsU256 WriteSuccessExactAuthorizationsNonceSuffix
  WriteSuccessExactAuthorizationsBodyPost WriteSuccessExactAuthorizationsAddressEntry
  WriteSuccessExactAuthorizationsOutputWhole WriteSuccessExactAuthorizationsPhases.

Lemma authorization_address_suffix_correct `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  length bytes = 144%nat ->
  ([∗ list] instruction ∈ IslaTraces.write_success_77.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_78.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_79.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_80.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_81.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15614 (authorizationBodyPost sp bytes tail P) -∗
  instr_body 0x155bc (authorizationU256Post sp bytes 0 (BV 64 0x155bc)
    (authorizationExactPhaseEvents 1 sp bytes tail)
    ("x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗ P ∗ True)%I).
Proof.
  intros Hlen. iStartProof. iIntros "#Haddress #Hnonce #Hv #Hr #Hs #HencoderInt #HencoderU256 #Houtput Hfinal".
  iPoseProof (authorization_nonce_suffix_correct sp bytes tail P Hlen
    with "Hnonce Hv Hr Hs HencoderInt HencoderU256 Houtput Hfinal") as "Hlast".
  iPoseProof (authorization_whole_output_correct sp (BV 64 0x155bc) (BV 64 0x2401a0b8)
    (sp - BV 64 48)%bv (BV 64 32) bytes (authorizationExactPhaseEvents 2 sp bytes tail)
    (authorizationAddressCallerFrame sp P) with "Haddress Houtput Hlast") as "Hcallee".
  iApply (instr_pre_wand 0x155bc 0x155bc false false with "Hcallee"); [done | done |].
  iIntros "Hpost". iEval (rewrite authorization_phase_one) in "Hpost".
  iApply (authorization_u256_to_address with "Hpost").
Qed.
Print Assumptions authorization_address_suffix_correct.

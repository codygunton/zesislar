Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsInt WriteSuccessExactAuthorizationsVSuffix
  WriteSuccessExactAuthorizationsBodyPost WriteSuccessExactAuthorizationsAddressInt
  WriteSuccessExactAuthorizationsAddressEntry WriteSuccessExactAuthorizationsOutputWhole
  WriteSuccessExactAuthorizationsPhases.

Lemma authorization_nonce_suffix_correct `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  length bytes = 144%nat ->
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
  instr_body 0x155cc (authorizationWholeOutputPost sp bytes
    (authorizationExactPhaseEvents 2 sp bytes tail) (authorizationAddressCallerFrame sp P)).
Proof.
  intros Hlen. iStartProof. iIntros "#Hnonce #Hv #Hr #Hs #HencoderInt #HencoderU256 #Houtput Hfinal".
  iPoseProof (authorization_v_suffix_correct sp bytes tail P Hlen
    with "Hv Hr Hs HencoderInt HencoderU256 Houtput Hfinal") as "Hlast".
  iAssert (instr_pre 0x155d8 (authorizationIntPost sp bytes (BV 64 0x155d8)
    (authorizationExactPhaseEvents 3 sp bytes tail) (authorizationIntCallerFrame sp P)))
    with "[Hlast]" as "Hnext".
  { iApply (instr_pre_wand 0x155d8 0x155d8 false true with "Hlast"); [done | done |]. iIntros "$". }
  iPoseProof (authorization_first_int_correct sp (BV 64 0x155cc) (BV 64 0x2401a0b8)
    (BV 64 20) bytes (authorizationExactPhaseEvents 3 sp bytes tail)
    (authorizationIntCallerFrame sp P) with "Hnonce HencoderInt Houtput") as "Hcallee".
  iApply (instr_pre_wand 0x155cc 0x155cc false false with "Hcallee"); [done | done |].
  iIntros "Hpost". iEval (rewrite (authorization_phase_two sp bytes tail Hlen)) in "Hpost".
  iApply (authorization_address_to_int sp bytes _ P Hlen with "Hpost Hnext").
Qed.
Print Assumptions authorization_nonce_suffix_correct.

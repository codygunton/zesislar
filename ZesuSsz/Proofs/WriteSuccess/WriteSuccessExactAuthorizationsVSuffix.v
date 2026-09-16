Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsInt WriteSuccessExactAuthorizationsSecondInt
  WriteSuccessExactAuthorizationsIntNext WriteSuccessExactAuthorizationsU256Suffix
  WriteSuccessExactAuthorizationsBodyPost WriteSuccessExactAuthorizationsAddressInt
  WriteSuccessExactAuthorizationsPhases.

Lemma authorization_v_suffix_correct `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  length bytes = 144%nat ->
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
  instr_body 0x155d8 (authorizationIntPost sp bytes (BV 64 0x155d8)
    (authorizationExactPhaseEvents 3 sp bytes tail) (authorizationIntCallerFrame sp P)).
Proof.
  intros Hlen. iStartProof. iIntros "#Hv #Hr #Hs #HencoderInt #HencoderU256 #Houtput Hfinal".
  iPoseProof (authorization_u256_suffix_correct sp bytes tail P Hlen
    with "Hr Hs HencoderU256 Houtput Hfinal") as "Hlast".
  iAssert (instr_pre 0x155e4 (authorizationIntPost sp bytes (BV 64 0x155e4)
    (authorizationExactPhaseEvents 4 sp bytes tail) (authorizationIntCallerFrame sp P)))
    with "[Hlast]" as "Hnext".
  { iApply (instr_pre_wand 0x155e4 0x155e4 false true with "Hlast"); [done | done |]. iIntros "$". }
  iPoseProof (authorization_second_int_correct sp (BV 64 0x155d8) (BV 64 (mapIoContextAddress defaultMap))
    (BV 64 8) bytes (authorizationExactPhaseEvents 4 sp bytes tail)
    (authorizationIntCallerFrame sp P) with "Hv HencoderInt Houtput") as "Hcallee".
  iApply (instr_pre_wand 0x155d8 0x155d8 false false with "Hcallee"); [done | done |].
  iIntros "Hpost". iEval (rewrite (authorization_phase_three sp bytes tail Hlen)) in "Hpost".
  iApply (authorization_int_to_second_int with "Hpost Hnext").
Qed.
Print Assumptions authorization_v_suffix_correct.

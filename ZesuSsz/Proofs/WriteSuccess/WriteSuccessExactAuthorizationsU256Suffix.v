Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsU256 WriteSuccessExactAuthorizationsInt
  WriteSuccessExactAuthorizationsIntU256 WriteSuccessExactAuthorizationsSecondU256
  WriteSuccessExactAuthorizationsLastU256 WriteSuccessExactAuthorizationsBodyPost
  WriteSuccessExactAuthorizationsAddressInt WriteSuccessExactAuthorizationsPhases.

Lemma authorization_u256_suffix_correct `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  length bytes = 144%nat ->
  ([∗ list] instruction ∈ IslaTraces.write_success_80.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_81.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15614 (authorizationBodyPost sp bytes tail P) -∗
  instr_body 0x155e4 (authorizationIntPost sp bytes (BV 64 0x155e4)
    (authorizationExactPhaseEvents 4 sp bytes tail) (authorizationIntCallerFrame sp P)).
Proof.
  intros Hlen. iStartProof. iIntros "#Hsecond #Hthird #Hencoder #Houtput Hfinal".
  iPoseProof (authorization_last_u256_correct sp bytes tail P Hlen
    with "Hthird Hencoder Houtput Hfinal") as "Hlast".
  iAssert (instr_pre 0x155fc (authorizationU256Post sp bytes 32 (BV 64 0x155fc)
    (authorizationExactPhaseEvents 5 sp bytes tail)
    ("x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗ P ∗ True)%I))
    with "[Hlast]" as "Hnext".
  { iApply (instr_pre_wand 0x155fc 0x155fc false true with "Hlast"); [done | done |]. iIntros "$". }
  iPoseProof (authorization_second_u256_correct sp (BV 64 0x155e4) (BV 64 (mapIoContextAddress defaultMap))
    bytes (authorizationExactPhaseEvents 5 sp bytes tail)
    ("x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗ P ∗ True)%I
    with "Hsecond Hencoder Houtput") as "Hcallee".
  iApply (instr_pre_wand 0x155e4 0x155e4 false false with "Hcallee"); [done | done |].
  iIntros "Hpost". iEval (rewrite (authorization_phase_four sp bytes tail Hlen)) in "Hpost".
  iApply (authorization_int_to_u256 with "Hpost Hnext").
Qed.
Print Assumptions authorization_u256_suffix_correct.

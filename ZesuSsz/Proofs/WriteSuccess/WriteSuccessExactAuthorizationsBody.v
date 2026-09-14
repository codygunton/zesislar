Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsU256 WriteSuccessExactAuthorizationsAddressSuffix
  WriteSuccessExactAuthorizationsBodyPost WriteSuccessExactAuthorizationsModel
  WriteSuccessExactAuthorizationsPhases.

Definition authorizationBodyEntry `{!islaG Sigma} `{!threadG}
    (sp oldra old5 : bv 64) (bytes : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
   (bv_unsigned sp + 1744) ↦ₘ∗ bytes ∗ (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactAuthorizationItemEvents sp bytes tail) ∗
   ⌜length bytes = 144%nat⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= bv_unsigned sp - 48)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationBodyEntry) := I.

Lemma authorization_body_correct `{!islaG Sigma} `{!threadG}
    sp oldra old5 bytes tail (P : iProp Sigma) :
  length bytes = 144%nat ->
  ([∗ list] instruction ∈ IslaTraces.write_success_76.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
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
  instr_body 0x155a4 (authorizationBodyEntry sp oldra old5 bytes tail P).
Proof.
  intros Hlen. iStartProof. iIntros "#Hchain #Haddress #Hnonce #Hv #Hr #Hs #HencoderInt #HencoderU256 #Houtput Hfinal".
  iPoseProof (authorization_address_suffix_correct sp bytes tail P Hlen
    with "Haddress Hnonce Hv Hr Hs HencoderInt HencoderU256 Houtput Hfinal") as "Hlast".
  iAssert (instr_pre 0x155bc (authorizationU256Post sp bytes 0 (BV 64 0x155bc)
    (authorizationExactPhaseEvents 1 sp bytes tail)
    ("x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗ P ∗ True)%I))
    with "[Hlast]" as "Hnext".
  { iApply (instr_pre_wand 0x155bc 0x155bc false true with "Hlast"); [done | done |]. iIntros "$". }
  iPoseProof (authorization_first_u256_correct sp oldra old5 bytes
    (authorizationExactPhaseEvents 1 sp bytes tail)
    ("x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗ P ∗ True)%I
    with "Hchain HencoderU256 Houtput") as "Hcallee".
  iApply (instr_pre_wand 0x155a4 0x155a4 false false with "Hcallee"); [done | done |].
  iIntros "Hentry". iDestruct "Hentry" as
    "(Hsys & Hsp & H1 & H5 & H8 & Hwords & Hbytes & Hscratch & Hmmio & Htrace & %Hsize & %Halign & %Hlow & %Hhigh & HP & _)".
  iEval (rewrite -authorization_phase_item (authorization_phase_zero sp bytes tail Hlen)) in "Htrace".
  unfold authorizationU256Entry. iFrame. repeat iSplit; done.
Qed.
Print Assumptions authorization_body_correct.

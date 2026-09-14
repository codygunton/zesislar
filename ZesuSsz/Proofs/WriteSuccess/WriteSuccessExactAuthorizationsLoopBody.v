Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsLoopSpec WriteSuccessExactAuthorizationsTailNative
  WriteSuccessExactAuthorizationsBodyTail WriteSuccessExactAuthorizationsCopyBody
  WriteSuccessExactAuthorizationsCopyEntry WriteSuccessExactAuthorizationsBody
  WriteSuccessExactAuthorizationsCopy WriteSuccessExactAuthorizationsFacts
  WriteSuccessExactAuthorizationsModel.

Lemma authorization_loop_body `{!islaG Sigma} `{!threadG}
    sp base rows source tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_75.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
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
  ([∗ list] instruction ∈ IslaTraces.write_success_82.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15590 (authorizationLoopSpec sp base rows source tail P) -∗
  instr_body 0x15590 (authorizationLoopSpec sp base rows source tail P).
Proof.
  iStartProof. iIntros "#H75 #H76 #H77 #H78 #H79 #H80 #H81 #H82 #Hcopy #Hint #Hu256 #Houtput #IH".
  iEval (rewrite instr_pre'_eq). iIntros "Hentry".
  iEval (unfold authorizationLoopSpec) in "Hentry".
  iDestruct "Hentry" as (prefix row rest pointer oldra old5) "(Hsys & H1 & H5 & H9 & H18 & Hpayload & _)".
  iDestruct "Hpayload" as "(Hsp & H8 & Hregs & Hsource & Hcopybytes & Hscratch & Hmmio & Htrace & HP & %Hfacts & Hexit & _)".
  pose proof (authorization_facts_layout sp pointer base rows prefix row rest source Hfacts)
    as (Hprefix & Hrow & Hslice & Hlength).
  iAssert (authorizationLoopPayload sp pointer base rows prefix row rest source tail P)
    with "[Hsp H8 Hregs Hsource Hcopybytes Hscratch Hmmio Htrace HP Hexit]" as "Hpayload".
  { unfold authorizationLoopPayload. iFrame. done. }
  iPoseProof (authorization_tail_native sp pointer base rows prefix row rest source tail P
    with "H82 IH") as "Htail".
  iPoseProof (instr_pre_wand 0x15614 0x15614 false false with "Htail []") as "Hlast".
  1: done. 1: reflexivity.
  { iIntros "Hpost". iApply (authorization_body_to_tail with "Hpost"). }
  iPoseProof (authorization_body_correct sp (BV 64 0x155a4) old5 row
    (writeSuccessExactAuthorizationEvents sp rest tail)
    (authorizationBodyFrame sp pointer base rows prefix row rest source tail P) Hrow
    with "H76 H77 H78 H79 H80 H81 Hint Hu256 Houtput Hlast") as "Hbody".
  iPoseProof (instr_pre_wand 0x155a4 0x155a4 false true with "Hbody []") as "Hnext".
  1: done. 1: reflexivity.
  { iIntros "Hpost". iApply (authorization_copy_to_body with "Hpost"). }
  iPoseProof (authorization_loop_to_copy sp pointer oldra old5 base rows prefix row rest source tail P
    with "[Hsys H1 H5 H9 H18 Hpayload Hnext]") as "Hcopyentry".
  { iFrame "Hsys H1 H5 H9 H18 Hpayload Hnext". }
  iPoseProof (authorization_copy_correct sp pointer oldra base (144 * length prefix) source
    (authorizationCopyCallerFrame sp pointer old5 base rows prefix row rest source tail P)
    with "H75 Hcopy") as "Hbodycopy".
  iEval (rewrite instr_pre'_eq) in "Hbodycopy".
  iApply ("Hbodycopy" with "Hcopyentry").
Qed.
Print Assumptions authorization_loop_body.

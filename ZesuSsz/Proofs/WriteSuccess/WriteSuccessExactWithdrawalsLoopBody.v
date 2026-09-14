Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsLoopSpec WriteSuccessExactWithdrawalsTailLoop
  WriteSuccessExactWithdrawalsFieldsTail WriteSuccessExactWithdrawalsCopyFields
  WriteSuccessExactWithdrawalsCopyEntry WriteSuccessExactWithdrawalsFields
  WriteSuccessExactWithdrawalsCopy WriteSuccessExactWithdrawalsModel.
Lemma withdrawal_loop_body `{!islaG Sigma} `{!threadG}
    sp base rows source tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_90.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_91.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_92.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_93.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_94.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_95.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15694 (withdrawalLoopSpec sp base rows source tail P) -∗
  instr_body 0x15694 (withdrawalLoopSpec sp base rows source tail P).
Proof.
  iStartProof. iIntros "#H90 #H91 #H92 #H93 #H94 #H95 #Hcopy #Hint #Houtput #IH".
  iEval (rewrite instr_pre'_eq). iIntros "Hentry".
  iEval (unfold withdrawalLoopSpec) in "Hentry".
  iDestruct "Hentry" as (prefix row rest pointer oldra old5) "(Hsys & H1 & H5 & H8 & H9 & Hpayload & _)".
  iDestruct "Hpayload" as "(Hsp & H18 & Hregs & Hsource & Hcopybytes & Hscratch & Hmmio & Htrace & HP & %Hfacts & Hexit & _)".
  pose proof (withdrawal_facts_layout sp pointer base rows prefix row rest source Hfacts)
    as (Hprefix & Hrow & Hslice & Hlength).
  iAssert (withdrawalLoopPayload sp pointer base rows prefix row rest source tail P)
    with "[Hsp H18 Hregs Hsource Hcopybytes Hscratch Hmmio Htrace HP Hexit]" as "Hpayload".
  { unfold withdrawalLoopPayload. iFrame. done. }
  iPoseProof (withdrawal_tail_loop_correct sp pointer base rows prefix row rest source tail P
    with "H95 IH") as "Htail".
  iPoseProof (instr_pre_wand 0x156dc 0x156dc false false with "Htail []") as "Hlast".
  1: done. 1: reflexivity.
  { iIntros "Hpost". iApply (withdrawal_fields_to_tail with "Hpost"). }
  iPoseProof (withdrawal_fields_correct sp (BV 64 0x156a8) old5 pointer row
    (writeSuccessExactWithdrawalEvents sp rest tail)
    (withdrawalBodyFrame sp pointer base rows prefix row rest source tail P) Hrow
    with "H91 H92 H93 H94 Hint Houtput Hlast") as "Hbody".
  iPoseProof (instr_pre_wand 0x156a8 0x156a8 false true with "Hbody []") as "Hnext".
  1: done. 1: reflexivity.
  { iIntros "Hpost". iApply (withdrawal_copy_to_fields with "Hpost"). }
  iPoseProof (withdrawal_loop_to_copy sp pointer oldra old5 base rows prefix row rest source tail P
    with "[Hsys H1 H5 H8 H9 Hpayload Hnext]") as "Hcopyentry".
  { iFrame "Hsys H1 H5 H8 H9 Hpayload Hnext". }
  iPoseProof (withdrawal_copy_correct sp pointer oldra base (48 * length prefix) source
    (withdrawalCopyCallerFrame sp pointer old5 base rows prefix row rest source tail P)
    with "H90 Hcopy") as "Hbodycopy".
  iEval (rewrite instr_pre'_eq) in "Hbodycopy". iApply ("Hbodycopy" with "Hcopyentry").
Qed.
Print Assumptions withdrawal_loop_body.


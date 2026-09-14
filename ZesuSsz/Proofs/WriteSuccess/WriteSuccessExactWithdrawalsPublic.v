Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsInitial WriteSuccessExactWithdrawalsLoopSpec
  WriteSuccessExactWithdrawalsLoopClosed.

Definition withdrawalLoopCode `{!islaG Sigma} : iProp Sigma :=
  ([∗ list] block ∈
    [IslaTraces.write_success_90.instrs.instr_map;
     IslaTraces.write_success_91.instrs.instr_map;
     IslaTraces.write_success_92.instrs.instr_map;
     IslaTraces.write_success_93.instrs.instr_map;
     IslaTraces.write_success_94.instrs.instr_map;
     IslaTraces.write_success_95.instrs.instr_map;
     IslaTraces.write_success_02.instrs.instr_map;
     IslaTraces.write_success_07.instrs.instr_map;
     IslaTraces.write_success_01.instrs.instr_map],
    [∗ list] instruction ∈ block, instr instruction.1 (Some instruction.2))%I.
Global Instance : LithiumUnfold (@withdrawalLoopCode) := I.

Lemma withdrawal_initial_closed `{!islaG Sigma} `{!threadG}
    sp oldra old5 base row rest source tail (P : iProp Sigma) :
  withdrawalLoopFacts sp (Z_to_bv 64 base) base (row :: rest) [] row rest source ->
  ([∗ list] instruction ∈ IslaTraces.write_success_89.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  withdrawalLoopCode -∗
  instr_body 0x1568c (withdrawalInitialEntry sp oldra old5 base row rest source tail P).
Proof.
  intros Hfacts. iStartProof. iIntros "#H89 #Hloop".
  iApply (withdrawal_initial_nonempty sp oldra old5 base row rest source tail P Hfacts with "H89").
  iEval (unfold withdrawalLoopCode; rewrite !big_sepL_cons big_sepL_nil) in "Hloop".
  iDestruct "Hloop" as "#(H90 & H91 & H92 & H93 & H94 & H95 & Hcopy & Hint & Houtput & _)".
  iApply (withdrawal_loop_closed with "H90 H91 H92 H93 H94 H95 Hcopy Hint Houtput").
Qed.
Print Assumptions withdrawal_initial_closed.


Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsInitial WriteSuccessExactAuthorizationsLoopSpec
  WriteSuccessExactAuthorizationsLoopClosed.

Definition authorizationLoopCode `{!islaG Sigma} : iProp Sigma :=
  ([∗ list] block ∈
    [IslaTraces.write_success_75.instrs.instr_map;
     IslaTraces.write_success_76.instrs.instr_map;
     IslaTraces.write_success_77.instrs.instr_map;
     IslaTraces.write_success_78.instrs.instr_map;
     IslaTraces.write_success_79.instrs.instr_map;
     IslaTraces.write_success_80.instrs.instr_map;
     IslaTraces.write_success_81.instrs.instr_map;
     IslaTraces.write_success_82.instrs.instr_map;
     IslaTraces.write_success_02.instrs.instr_map;
     IslaTraces.write_success_07.instrs.instr_map;
     IslaTraces.write_success_08.instrs.instr_map;
     IslaTraces.write_success_01.instrs.instr_map],
    [∗ list] instruction ∈ block, instr instruction.1 (Some instruction.2))%I.
Global Instance : LithiumUnfold (@authorizationLoopCode) := I.

Lemma authorization_initial_closed `{!islaG Sigma} `{!threadG}
    sp oldra old5 base row rest source tail (P : iProp Sigma) :
  authorizationLoopFacts sp (Z_to_bv 64 base) base (row :: rest) [] row rest source ->
  ([∗ list] instruction ∈ IslaTraces.write_success_74.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  authorizationLoopCode -∗
  instr_body 0x15584 (authorizationInitialEntry sp oldra old5 base row rest source tail P).
Proof.
  intros Hfacts. iStartProof. iIntros "#H74 #Hloop".
  iApply (authorization_initial_nonempty sp oldra old5 base row rest source tail P Hfacts with "H74").
  iEval (unfold authorizationLoopCode; rewrite !big_sepL_cons big_sepL_nil) in "Hloop".
  iDestruct "Hloop" as "#(H75 & H76 & H77 & H78 & H79 & H80 & H81 & H82 & Hcopy & Hint & Hu256 & Houtput & _)".
  iApply (authorization_loop_closed with "H75 H76 H77 H78 H79 H80 H81 H82 Hcopy Hint Hu256 Houtput").
Qed.
Print Assumptions authorization_initial_closed.

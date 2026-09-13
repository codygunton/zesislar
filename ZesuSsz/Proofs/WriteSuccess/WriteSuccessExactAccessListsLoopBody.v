Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Continuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsLoopSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsEmptyBranch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsBody.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsTailNative.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsControlExit.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Lemma access_exact_loop_body `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (entries : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (tail : spec) (x19 savedX22 : bv 64) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_53.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_54.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_55.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_56.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_57.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_58.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_59.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_60.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_61.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_62.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_63.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ accessExactExitBodies sp base entries bytes tail x19 savedX22 P -∗
  □ instr_pre 0x151d4 (writeSuccessExactAccessListsLoopSpec sp base entries bytes tail x19 savedX22 P) -∗
  instr_body 0x151d4 (writeSuccessExactAccessListsLoopSpec sp base entries bytes tail x19 savedX22 P).
Proof.
  iStartProof. iIntros "#H53 #H54 #H55 #H56 #H57 #H58 #H59 #H60 #H61 #H62 #H63 #Hcopy #Hencoder #Houtput #Hexit #IH".
  unfold writeSuccessExactAccessListsLoopSpec.
  iApply (instr_body_exists 0x151d4). iIntros (processed).
  iApply (instr_body_exists 0x151d4). iIntros (remaining).
  iApply (instr_body_exists 0x151d4). iIntros (storedIndex).
  iApply (instr_body_exists 0x151d4). iIntros (data).
  iApply (instr_body_exists 0x151d4). iIntros (x22).
  iApply (instr_body_exists 0x151d4). iIntros (x27).
  iApply (access_control_exact_with_exit with "H53 [] Hexit").
  destruct remaining as [|entry rest].
  - iPoseProof (instr_body_false 0x151dc) as "Hfalse".
    iApply (instr_pre_wand 0x151dc 0x151dc false false with "Hfalse");
      [done | reflexivity |].
    iApply access_empty_branch_impossible.
  - iPoseProof (access_tail_exact_loop_native sp base entries processed entry rest bytes
      x19 savedX22 tail P with "H63 IH") as "#Hnext".
    iPoseProof (access_exact_iteration_correct sp base entries processed entry rest bytes
      storedIndex x19 savedX22 x22 x27 tail
      (accessExactLoopFrame sp base entries bytes tail x19 savedX22 P)
      with "H54 H55 H56 H57 H58 H59 H60 H61 H62 Hcopy Hencoder Houtput Hnext") as "Hbody".
    iApply (instr_pre_wand 0x151dc 0x151dc false false with "Hbody");
      [done | reflexivity |].
    iIntros "(Hstate & _ & _)". iExact "Hstate".
Qed.
Print Assumptions access_exact_loop_body.

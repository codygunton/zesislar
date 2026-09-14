Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAccessListsSpec WriteSuccessExactAccessListsControl
  WriteSuccessExactAccessListsControlEntry WriteSuccessExactAccessListsControlReturn.
From IslaTraces.write_success_52 Require Import instrs.

Lemma access_initial_to_loop_correct `{!islaG Sigma} `{!threadG}
    sp base entries bytes storedIndex x19 savedX22 data old11 x22 x27 tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_52.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x151d4 (writeSuccessExactAccessListsState sp base entries [] entries bytes
    storedIndex x19 savedX22 data x22 x27 tail P) -∗
  instr_body 0x151d0 (accessListsControlState sp (Z_to_bv 64 (Z.of_nat (length entries))) old11 data
    (accessControlFrame sp base entries [] entries bytes storedIndex x19 savedX22 data x22 x27 tail P)).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iAssert (instr_pre 0x151d4 (accessListsControlState sp
    (Z_to_bv 64 (Z.of_nat (length entries))) (BV 64 0) data
    (accessControlFrame sp base entries [] entries bytes storedIndex x19 savedX22 data x22 x27 tail P)))%I
    as "HcontrolNext".
  { iApply (instr_pre_wand 0x151d4 0x151d4 true true with "Hnext"); [done | done |].
    have Hzero : Z_to_bv 64 0 = BV 64 0 by bv_solve.
    rewrite -Hzero.
    iApply (access_control_return_resources sp base entries [] entries bytes storedIndex
      x19 savedX22 data data x22 x27 tail P). }
  iEval (rewrite /IslaTraces.write_success_52.instrs.instr_map /=) in "Hcode".
  iDestruct "Hcode" as "#(H0 & _)".
  zesu_run.
Qed.
Print Assumptions access_initial_to_loop_correct.

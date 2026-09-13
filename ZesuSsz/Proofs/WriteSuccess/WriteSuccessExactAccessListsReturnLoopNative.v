Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Continuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsReturnLoopEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsReturnCount.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Export.Snapshots.
Require Import isla.riscv64.riscv64.

Lemma access_return_loop_native_correct `{!islaG Sigma} `{!threadG}
    sp base entries bytes x19 savedX22 tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_64.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x153d0 (accessReturnCountPost sp savedX22 tail (accessReturnLoopFrame sp base entries bytes x19 P)) -∗
  instr_body 0x153c0 (writeSuccessAccessListsLoopExit sp base entries bytes
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail)
    x19 savedX22 (accessReturnRuntimeBounds sp P)).
Proof.
  iStartProof. iIntros "#Hcode #Hencoder #Houtput Hnext".
  iAssert (∀ values : (bv 64 * (bv 64 * bv 64))%type, instr_body 0x153c0
    (accessReturnCountEntry sp savedX22 values.1 values.2.1 values.2.2
      (Z_to_bv 64 (Z.of_nat (length entries))) (Z_to_bv 64 (Z.of_nat (length entries))) tail (accessReturnLoopFrame sp base entries bytes x19 P)))%I as "Hall".
  { iIntros (values). iApply (access_return_count_correct with "Hcode Hencoder Houtput"). }
  iPoseProof (instr_body_exists 0x153c0 _ with "Hall") as "Hbody".
  iApply (instr_pre_wand 0x153c0 0x153c0 false false with "Hbody");
    [done | reflexivity |].
  iIntros "Hpost".
  iDestruct (access_return_loop_entry_resources sp base entries bytes x19 savedX22 tail P
    with "[Hpost Hnext]") as (old22 old_ra old5) "Hentry".
  { iFrame "Hpost". iSplitL "Hnext"; last done.
    iApply (instr_pre_wand 0x153d0 0x153d0 false true with "Hnext");
      [done | reflexivity |]. iIntros "$". }
  iExists (old22, (old_ra, old5)). iExact "Hentry".
Qed.
Print Assumptions access_return_loop_native_correct.

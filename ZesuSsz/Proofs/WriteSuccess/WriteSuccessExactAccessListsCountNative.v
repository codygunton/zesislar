Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.Continuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsOutputEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsOutputWhole.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCountEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCountWhole.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Lemma access_count_exact_loop_native `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes storedIndex x19 savedX22 x22 x27 tail
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_56.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x1521c (accessCountWholePost sp (writeSuccessAccessEntryBytes entry)
    (accessEntryAfterCountEvents sp entry rest tail)
    (accessCountLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P)) -∗
  instr_body 0x15210 (accessListsWholeOutputPost sp (writeSuccessAccessEntryBytes entry)
    (accessEntryAfterAddressEvents sp entry rest tail)
    (accessOutputLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P)).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput Hnext".
  iPoseProof (access_count_whole_correct sp (BV 64 0x15210) (BV 64 (mapIoContextAddress defaultMap))
    (sp + BV 64 1760)%bv (BV 64 20) (writeSuccessAccessEntryBytes entry)
    (accessEntryAfterCountEvents sp entry rest tail)
    (accessCountLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P)
    with "Hcaller Hencoder Houtput") as "Hbody".
  iApply (instr_pre_wand 0x15210 0x15210 false false with "Hbody");
    [done | reflexivity |].
  iIntros "Hpost". iApply access_count_loop_entry_resources.
  iFrame "Hpost".
  iSplitL "Hnext"; last done.
  iApply (instr_pre_wand 0x1521c 0x1521c false true with "Hnext");
    [done | reflexivity |].
  iIntros "$".
Qed.
Print Assumptions access_count_exact_loop_native.

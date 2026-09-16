Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.Continuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCopyEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCopyWhole.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsOutputEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsOutputWhole.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Lemma access_output_exact_loop_native `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes storedIndex x19 savedX22 x22 x27 tail
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_55.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15210 (accessListsWholeOutputPost sp (writeSuccessAccessEntryBytes entry)
    (accessEntryAfterAddressEvents sp entry rest tail) (accessOutputLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P)) -∗
  instr_body 0x15200 (accessCopyWholePost sp (Z_to_bv 64 base)
    (Z_to_bv 64 (Z.of_nat (length processed))) bytes
    (accessCopyLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P)).
Proof.
  iStartProof. iIntros "#Hcaller #Houtput Hnext".
  iAssert (∀ old5 : bv 64, instr_body 0x15200 (accessListsWholeOutputEntry sp
    (BV 64 0x15200) old5 (sp + BV 64 1744)%bv
    (Z_to_bv 64 (base + 40 * Z.of_nat (length processed))) (writeSuccessAccessEntryBytes entry)
    (accessEntryAfterAddressEvents sp entry rest tail) (accessOutputLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P)))%I
    with "[Hnext]" as "Hall".
  { iIntros (old5).
    iApply (access_lists_whole_output_correct with "Hcaller Houtput Hnext"). }
  iPoseProof (instr_body_exists 0x15200 _ with "Hall") as "Hbody".
  iApply (instr_pre_wand 0x15200 0x15200 false false with "Hbody");
    [done | reflexivity |].
  iApply access_output_loop_entry_resources.
Qed.
Print Assumptions access_output_exact_loop_native.

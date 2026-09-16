Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.Continuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCopyWhole.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCopyEntry.
Require Import isla.riscv64.riscv64.

Lemma access_copy_exact_loop_native `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes storedIndex x19 savedX22 x22 x27 tail
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_54.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15200 (accessCopyWholePost sp (Z_to_bv 64 base)
    (Z_to_bv 64 (Z.of_nat (length processed))) bytes (accessCopyLoopFrame sp base entries processed (entry :: rest) bytes storedIndex
      x19 savedX22 (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P)) -∗
  instr_body 0x151dc (writeSuccessExactAccessListsState sp base entries processed (entry :: rest) bytes
    storedIndex x19 savedX22 (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hmemcpy Hnext".
  iAssert (instr_pre 0x15200 (accessCopyWholePost sp (Z_to_bv 64 base)
    (Z_to_bv 64 (Z.of_nat (length processed))) bytes (accessCopyLoopFrame sp base entries processed (entry :: rest) bytes storedIndex
      x19 savedX22 (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P)))%I with "[Hnext]" as "Hret".
  { iApply (instr_pre_wand 0x15200 0x15200 false true with "Hnext");
      [done | reflexivity |]. auto. }
  iAssert (∀ old_ra : bv 64, instr_body 0x151dc (accessCopyWholeEntry sp (Z_to_bv 64 base)
    (Z_to_bv 64 (Z.of_nat (length processed))) storedIndex old_ra bytes (accessCopyLoopFrame sp base entries processed (entry :: rest) bytes storedIndex
      x19 savedX22 (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P)))%I as "Hall".
  { iIntros (old_ra). iApply (access_copy_whole_correct with "Hcaller Hmemcpy"). }
  iPoseProof (instr_body_exists 0x151dc _ with "Hall") as "Hbody".
  iApply (instr_pre_wand 0x151dc 0x151dc false false with "Hbody");
    [done | reflexivity |].
  iIntros "Hstate". iApply access_copy_loop_entry_resources. iFrame.
Qed.
Print Assumptions access_copy_exact_loop_native.

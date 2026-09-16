Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.Continuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsTail.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsTailGuarded.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsTailEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsTailReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsLoopSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsStorageEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import isla.riscv64.riscv64.

Lemma access_tail_exact_loop_native `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes x19 savedX22 tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_63.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x151d4 (writeSuccessExactAccessListsLoopSpec sp base entries bytes tail x19 savedX22 P) -∗
  □ instr_body 0x153b4 (writeSuccessStorageKeysLoopExit x19 sp
    (bv_unsigned (writeSuccessAccessEntryStoragePointer entry))
    (writeSuccessAccessEntryStorageCount entry) (writeSuccessAccessEntryStorageBytes entry)
    (writeSuccessExactAccessListsEvents sp rest tail)
    (accessStorageLoopFrame sp base entries processed entry rest bytes savedX22 (accessExactLoopFrame sp base entries bytes tail x19 savedX22 P))).
Proof.
  iStartProof. iIntros "#Hcode #IH". iModIntro.
  iAssert (∀ values : (bv 64 * (bv 64 * bv 64))%type,
    instr_body 0x153b4 (accessListsTailEntry sp
      (Z_to_bv 64 (Z.of_nat (length processed))) values.2.1 (accessTailLoopFrame sp base entries (processed ++ [entry]) rest bytes x19 savedX22
      values.1 values.2.2 tail (accessExactLoopFrame sp base entries bytes tail x19 savedX22 P))))%I as "Hall".
  { iIntros (values). iApply (access_lists_tail_guarded_correct with "Hcode").
    iApply (instr_pre_wand 0x151d4 0x151d4 true true with "IH");
      [done | reflexivity |].
    iIntros "Hpost".
    iPoseProof (access_tail_loop_return_resources with "Hpost") as "Hstate".
    iApply (access_loop_state_resources with "Hstate"). }
  iPoseProof (instr_body_exists 0x153b4 _ with "Hall") as "Hbody".
  iApply (instr_pre_wand 0x153b4 0x153b4 false false with "Hbody");
    [done | reflexivity |].
  iIntros "Hpost". iDestruct (access_tail_loop_entry_resources with "Hpost")
    as (data old11 pointer) "Hentry".
  iExists (data, (old11, pointer)). iExact "Hentry".
Qed.
Print Assumptions access_tail_exact_loop_native.

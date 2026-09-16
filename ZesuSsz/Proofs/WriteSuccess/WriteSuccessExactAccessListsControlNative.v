Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsControl.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsControlEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsControlReturn.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_53 Require Import instrs.

Lemma access_control_exact_native_correct `{!islaG Sigma} `{!threadG}
    sp base entries processed remaining bytes storedIndex x19 savedX22 data x22 x27 tail
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_53.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x151dc (writeSuccessExactAccessListsState sp base entries processed remaining bytes
      storedIndex x19 savedX22 (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P ∗
    ⌜Z_to_bv 64 (Z.of_nat (length processed)) <> Z_to_bv 64 (Z.of_nat (length entries))⌝ ∗ True) -∗
  instr_body 0x153c0 (writeSuccessExactAccessListsState sp base entries processed remaining bytes
      storedIndex x19 savedX22 (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P ∗
    ⌜Z_to_bv 64 (Z.of_nat (length processed)) = Z_to_bv 64 (Z.of_nat (length entries))⌝ ∗ True) -∗
  instr_body 0x151d4 (writeSuccessExactAccessListsState sp base entries processed remaining bytes
    storedIndex x19 savedX22 data x22 x27 tail P).
Proof.
  iStartProof. iIntros "#Hcode Hpositive Hzero".
  iAssert (instr_body 0x151dc (accessListsControlState sp
    (Z_to_bv 64 (Z.of_nat (length entries))) (Z_to_bv 64 (Z.of_nat (length processed)))
    (Z_to_bv 64 (Z.of_nat (length entries)))
    (accessControlFrame sp base entries processed remaining bytes
      storedIndex x19 savedX22 data x22 x27 tail P) ∗
    ⌜Z_to_bv 64 (Z.of_nat (length processed)) <> Z_to_bv 64 (Z.of_nat (length entries))⌝ ∗ True))%I
    with "[Hpositive]" as "Hpos".
  { iApply (instr_pre_wand 0x151dc 0x151dc false false with "Hpositive");
      [done | reflexivity |].
    iIntros "(Hcontrol & Hbranch & _)".
    iSplitL "Hcontrol"; last (iFrame).
    iApply (access_control_return_resources with "Hcontrol"). }
  iAssert (instr_body 0x153c0 (accessListsControlState sp
    (Z_to_bv 64 (Z.of_nat (length entries))) (Z_to_bv 64 (Z.of_nat (length processed)))
    (Z_to_bv 64 (Z.of_nat (length entries)))
    (accessControlFrame sp base entries processed remaining bytes
      storedIndex x19 savedX22 data x22 x27 tail P) ∗
    ⌜Z_to_bv 64 (Z.of_nat (length processed)) = Z_to_bv 64 (Z.of_nat (length entries))⌝ ∗ True))%I
    with "[Hzero]" as "HzeroControl".
  { iApply (instr_pre_wand 0x153c0 0x153c0 false false with "Hzero");
      [done | reflexivity |].
    iIntros "(Hcontrol & Hbranch & _)".
    iSplitL "Hcontrol"; last (iFrame).
    iApply (access_control_return_resources with "Hcontrol"). }
  iPoseProof (access_lists_control_correct false with "Hcode Hpos HzeroControl") as "Hbody".
  iApply (instr_pre_wand 0x151d4 0x151d4 false false with "Hbody");
    [done | reflexivity |].
  iApply access_control_entry_resources.
Qed.
Print Assumptions access_control_exact_native_correct.

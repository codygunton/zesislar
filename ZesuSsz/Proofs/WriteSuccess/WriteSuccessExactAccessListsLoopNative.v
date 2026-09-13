Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsLoopSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsLoopBody.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsLoopClosed.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsLoopOpen.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsExitProvider.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Lemma access_exact_loop_native_correct `{!islaG Sigma} `{!threadG}
    sp base entries processed remaining bytes storedIndex x19 savedX22 data pointer count tail
    (P : iProp Sigma) :
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
  □ (∀ (sp' : bv 64) (base' : Z) (entries' : list writeSuccessAccessEntry)
     (bytes' : list (bv 8)) (tail' : spec) (savedX22' : bv 64),
   instr_body 0x153c0 (writeSuccessAccessListsLoopExit sp' base' entries' bytes' tail' x19 savedX22' P)) -∗
  instr_body 0x151d4 (writeSuccessExactAccessListsState sp base entries processed remaining bytes storedIndex
    x19 savedX22 data pointer count tail P).
Proof.
  iStartProof. iIntros "#H53 #H54 #H55 #H56 #H57 #H58 #H59 #H60 #H61 #H62 #H63 #Hcopy #Hencoder #Houtput #Hexit".
  iPoseProof (access_exact_exit_provider x19 P with "Hexit") as "#HexitFrame".
  iPoseProof (access_exact_loop_closed x19 P with
    "H53 H54 H55 H56 H57 H58 H59 H60 H61 H62 H63 Hcopy Hencoder Houtput HexitFrame") as "#Hloop".
  iPoseProof (access_exact_loop_body x19 P with
    "H53 H54 H55 H56 H57 H58 H59 H60 H61 H62 H63 Hcopy Hencoder Houtput HexitFrame Hloop") as "Hbody".
  iPoseProof ("Hexit" $! sp base entries bytes tail savedX22) as "#HnextBody".
  iApply (instr_pre_wand 0x151d4 0x151d4 false false with "Hbody");
    [done | reflexivity |].
  iIntros "Hstate".
  iApply (access_loop_state_resources sp base entries processed remaining bytes storedIndex
    x19 savedX22 data pointer count tail P).
  iApply (access_loop_open_resources with "[] Hstate").
  iApply (instr_pre_wand 0x153c0 0x153c0 false true with "HnextBody");
    [done | reflexivity |].
  iIntros "$".
Qed.
Print Assumptions access_exact_loop_native_correct.

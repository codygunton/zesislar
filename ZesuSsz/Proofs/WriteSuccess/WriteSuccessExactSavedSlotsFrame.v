Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEpilogueBlock.
Lemma exact_saved_slots_frame `{!islaG Sigma} `{!threadG}
    (entry frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (Hframe : bv_unsigned entry = (bv_unsigned frame + 2000)%Z) :
  writeSuccessSavedSlots entry ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ⊣⊢
  writeSuccessEpilogueSavedSlots frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ∗ True.
Proof.
  rewrite /writeSuccessSavedSlots /writeSuccessEpilogueSavedSlots Hframe.
  rewrite -!Z.add_sub_assoc /=.
  iSplit; iIntros "Hslots";
    repeat iDestruct select (_ ∗ _)%I as "[? ?]"; iFrame.
Qed.
Print Assumptions exact_saved_slots_frame.

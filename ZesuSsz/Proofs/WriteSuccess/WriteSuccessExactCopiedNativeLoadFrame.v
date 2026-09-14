Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import Interfaces WriteSuccessExactNativeLoadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactCopiedNativeLoadSpec.
Lemma exact_native_copied_load_frame_mono `{!islaG Sigma} `{!threadG}
    stage sp decoded object (P Q : iProp Sigma) :
  (P -∗ Q) -∗ exactNativeCopiedLoadState stage sp decoded object P -∗
    exactNativeCopiedLoadState stage sp decoded object Q.
Proof.
  rewrite /exactNativeCopiedLoadState.
  iIntros "Hwand (Hsys & Hregs & H2 & H8 & Hobject & Hstack & Hwords & Hlength & Halign & Hlower & Hupper & Hspalign & Hsplower & Hspupper & HP & _)".
  iPoseProof ("Hwand" with "HP") as "HQ". iFrame.
Qed.
Print Assumptions exact_native_copied_load_frame_mono.

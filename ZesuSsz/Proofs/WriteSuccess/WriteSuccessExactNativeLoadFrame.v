Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactNativeLoadSpec.
Lemma exact_native_load_frame_mono `{!islaG Sigma} `{!threadG}
    sp decoded object (P Q : iProp Sigma) :
  (P -∗ Q) -∗ exactNativeLoadState sp decoded object P -∗
    exactNativeLoadState sp decoded object Q.
Proof.
  rewrite /exactNativeLoadState.
  iIntros "Hwand (Hsys & Hregs & H2 & H8 & Hobject & Hstack & Hlength & Halign & Hlower & Hupper & Hspalign & Hsplower & Hspupper & HP & _)".
  iPoseProof ("Hwand" with "HP") as "HQ". iFrame.
Qed.
Print Assumptions exact_native_load_frame_mono.

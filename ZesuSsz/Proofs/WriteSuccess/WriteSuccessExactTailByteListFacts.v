Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Lemma exact_tail_byte_list_sizes `{!islaG Sigma} address items :
  byteListItemResources address items -∗
  ⌜Forall (fun item => bv_unsigned (byteListSize item) = Z.of_nat (length (byteListBytes item))) items⌝ ∗
  byteListItemResources address items.
Proof.
  iInduction items as [|item rest] "IH" forall (address).
  - iIntros "_". iSplit; [iPureIntro; constructor | done].
  - cbn [byteListItemResources].
    iIntros "(Hdata & Hsize & Hbytes & %Hlength & Hrest)".
    iDestruct ("IH" $! (address + 16)%Z with "Hrest") as "[%Hsizes Hrest]".
    iSplit; [iPureIntro; constructor; assumption |].
    iFrame. done.
Qed.
Print Assumptions exact_tail_byte_list_sizes.

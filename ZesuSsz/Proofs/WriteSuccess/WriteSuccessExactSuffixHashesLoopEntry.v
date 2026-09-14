Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactSuffixHashesLoopSpec WriteSuccessExactSuffixHashesWord3
  WriteSuccessExactSuffixHashesWordHandoffs WriteSuccessExactSuffixHashesEmitHandoff
  WriteSuccessExactSuffixHashesReturn WriteSuccessExactSuffixHashesModel.

Lemma suffix_loop_to_words `{!islaG Sigma} `{!threadG}
    (sp pointer old_ra old5 : bv 64) base total processed remaining source tail (P : iProp Sigma) :
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗ "x9" ↦ᵣ RVal_Bits pointer ∗
   suffixLoopPayload sp pointer base total processed remaining source tail P ∗ True)%I -∗
  suffixWord3Entry sp pointer base source (32 * processed)
    (suffixWordFrame3 sp source (32 * processed)
      (suffixOutputResources sp old_ra old5 (take 32 (drop (32 * processed) source))
        (writeSuccessExactSuffixHashesEvents sp (S processed) remaining source tail)
        (suffixLoopCaller sp pointer base total processed remaining source tail P))).
Proof.
  iIntros "(Hsys & Hra & H5 & H8 & Hptr & Hpayload & _)".
  unfold suffixLoopPayload, suffixLoopScratch.
  iDestruct "Hpayload" as "(Hsp & Hregs & Hsource & Hscratch & Hmmio & Htrace & HP & %Hfacts & Hexit & _)".
  iDestruct "Hscratch" as "(H0 & H1 & H2 & H3 & _)".
  pose proof Hfacts as Hcopy.
  destruct Hcopy as (Hlength & Htotal & Hcursor & Hcount & Halign & Hlow & Hhigh & Hbase & Hend).
  have Hposition : bv_unsigned pointer = (base + Z.of_nat (32 * processed))%Z.
  { rewrite Nat2Z.inj_mul. exact Hcursor. }
  have Hbound : (32 * processed + 32 <= length source)%nat by lia.
  unfold suffixWord3Entry, suffixWordFrame3, suffixOutputResources, suffixLoopCaller.
  cbn [writeSuccessExactSuffixHashesEvents].
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions suffix_loop_to_words.

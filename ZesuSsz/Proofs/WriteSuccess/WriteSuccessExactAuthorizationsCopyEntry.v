Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsLoopSpec WriteSuccessExactAuthorizationsCopy
  WriteSuccessExactAuthorizationsArray.

Lemma authorization_loop_to_copy `{!islaG Sigma} `{!threadG}
    (sp pointer oldra old5 : bv 64) base rows prefix row rest source tail (P : iProp Sigma) :
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗ "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
   authorizationLoopPayload sp pointer base rows prefix row rest source tail P ∗
   instr_pre 0x155a4 (authorizationCopyPost sp pointer base (144 * length prefix) source
     (authorizationCopyCallerFrame sp pointer old5 base rows prefix row rest source tail P)) ∗ True)%I -∗
  authorizationCopyEntry sp pointer oldra base (144 * length prefix) source
    (authorizationCopyCallerFrame sp pointer old5 base rows prefix row rest source tail P).
Proof.
  iIntros "(Hsys & H1 & H5 & H9 & H18 & Hpayload & Hnext & _)".
  iDestruct "Hpayload" as "(Hsp & H8 & Hwords & Hsource & Hcopy & Hscratch & Hmmio & Htrace & HP & %Hfacts & Hexit & _)".
  destruct Hfacts as (Hrows & Hall & Hbytes & Hposition & Hcount & Halign & Hlow & Hhigh & Hbase & Hend).
  have HwholeLength : length source = (144 * length rows)%nat.
  { rewrite Hbytes. clear -Hall. induction Hall as [|bytes rows Hlen Hall IH]; cbn; [reflexivity|].
    rewrite app_length IH Hlen. lia. }
  unfold authorizationCopyEntry. iFrame "Hsys Hsp H9 H1 Hwords Hsource Hcopy Hnext".
  iSplit; first (iPureIntro; rewrite Nat2Z.inj_mul; cbn; exact Hposition).
  iSplit; first (iPureIntro; rewrite HwholeLength Hrows app_length /=; lia).
  iSplit; first done. iSplit; first done. iSplit; first (iPureIntro; lia). iSplit; first done.
  unfold authorizationCopyCallerFrame. iFrame. iPureIntro.
  unfold authorizationLoopFacts. repeat split; assumption.
Qed.
Print Assumptions authorization_loop_to_copy.

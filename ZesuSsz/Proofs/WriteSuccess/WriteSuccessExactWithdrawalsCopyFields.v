Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.RegPacking.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsLoopSpec WriteSuccessExactWithdrawalsCopy
  WriteSuccessExactWithdrawalsFields WriteSuccessExactWithdrawalsModel.

Lemma withdrawal_copy_to_fields `{!islaG Sigma} `{!threadG}
    sp pointer old5 base rows prefix row rest source tail (P : iProp Sigma) :
  withdrawalCopyPost sp pointer base (48 * length prefix) source
    (withdrawalCopyCallerFrame sp pointer old5 base rows prefix row rest source tail P) -∗
  withdrawalFieldsEntry sp (BV 64 0x156a8) old5 pointer row
    (writeSuccessExactWithdrawalEvents sp rest tail)
    (withdrawalBodyFrame sp pointer base rows prefix row rest source tail P).
Proof.
  iIntros "Hpost". iDestruct "Hpost" as (final13 final14)
    "(Hsys & H1 & H10 & H11 & H12 & H13 & H14 & H15 & Hsource & Hcopied & Hframe & _)".
  iDestruct "Hframe" as "(Hsp & H8 & Hcaller & _)".
  iDestruct "Hcaller" as "(H5 & H18 & H9 & Hscratch & Hmmio & Htrace & HP & %Hfacts & Hexit & _)".
  pose proof (withdrawal_facts_layout sp pointer base rows prefix row rest source Hfacts)
    as (Hprefix & Hrow & Hslice & HsourceLength).
  pose proof Hfacts as HfactsCopy.
  destruct Hfacts as (Hrows & Hall & Hbytes & Hposition & Hcount & Halign & Hlow & Hhigh & Hbase & Hend).
  have HcopyBase : bv_unsigned (sp + BV 64 1744)%bv = (bv_unsigned sp + 1744)%Z.
  { clear -Hlow Hhigh. bv_solve. }
  iEval (rewrite Hslice HcopyBase) in "Hcopied".
  iAssert (reg_col [(KindReg "x10", BitsShape 64)]) with "[H10]" as "Hdata".
  { iApply (reg_col_bv_list_shape [("x10", (sp + BV 64 1744)%bv)]). cbn. iFrame. }
  iAssert (reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
    (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)])
    with "[H12 H13 H14 H15]" as "Hother".
  { iApply (reg_col_bv_list_shape [("x12", BV 64 48); ("x13", final13);
      ("x14", final14); ("x15", BV 64 48)]). cbn. iFrame. }
  unfold withdrawalFieldsEntry, withdrawalBodyFrame. iFrame.
  repeat iSplit; try done; iPureIntro; exact HfactsCopy.
Qed.
Print Assumptions withdrawal_copy_to_fields.

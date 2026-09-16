Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsAddressEntry WriteSuccessExactAuthorizationsOutputWhole
  WriteSuccessExactAuthorizationsInt WriteSuccessExactAuthorizationsU256
  WriteSuccessExactEncoderIntFramedCall WriteSuccessExactTransactionsGasLoads
  WriteSuccessObservation WriteSuccessOutputSemantic.

Definition authorizationIntCallerFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
   reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
   (bv_unsigned sp - 48) ↦ₘ? 32 ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationIntCallerFrame) := I.

Lemma authorization_address_to_int `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  length bytes = 144%nat ->
  authorizationWholeOutputPost sp bytes
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64
        (bv_unsigned (transactionRowWord bytes 0 96)))) tail)
    (authorizationAddressCallerFrame sp P) -∗
  instr_pre 0x155d8 (authorizationIntPost sp bytes (BV 64 0x155d8) tail
    (authorizationIntCallerFrame sp P)) -∗
  authorizationIntEntry sp (BV 64 0x155cc) (BV 64 (mapIoContextAddress defaultMap))
    (BV 64 20) bytes 96 (BV 64 0x155d8) tail (authorizationIntCallerFrame sp P).
Proof.
  intros Hlen. iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & H5 & H10 & H11 & Hbytes & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hsp & H8 & Hcaller & _)".
  iDestruct "Hcaller" as "(Hpair & Hscratch & %Halign & %Hlow & %Hhigh & HP & _)".
  iDestruct (mem_mapsto_uninit_split 32 with "Hscratch") as "[Hprefix Hsuffix]"; first lia.
  replace ((bv_unsigned sp - 48) + 32)%Z with (bv_unsigned sp - 16)%Z by lia.
  iAssert (reg_col [(KindReg "x10", BitsShape 64)]) with "[H10]" as "H10col".
  { rewrite reg_col_cons reg_col_nil. iSplit; last done. iExists _. iFrame. done. }
  have Hsource : bv_unsigned (sp + BV 64 1744)%bv = (bv_unsigned sp + 1744)%Z by bv_solve.
  iEval (rewrite Hsource) in "Hbytes".
  unfold authorizationIntEntry. iFrame "Hsys Hsp H1 H5 H11 H10col Hbytes Hsuffix Hmmio Htrace Hnext".
  unfold authorizationIntCallerFrame. iFrame. repeat iSplit; done.
Qed.
Print Assumptions authorization_address_to_int.

Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsAddressInt WriteSuccessExactAuthorizationsInt
  WriteSuccessExactAuthorizationsU256 WriteSuccessExactEncoderIntFramedCall
  WriteSuccessExactTransactionsGasLoads WriteSuccessObservation WriteSuccessOutputSemantic
  WriteSuccessExactEncoderU256Spec.

Lemma authorization_int_to_u256 `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  authorizationIntPost sp bytes (BV 64 0x155e4)
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload (transactionRowWord bytes 32 0)
        (transactionRowWord bytes 32 8) (transactionRowWord bytes 32 16)
        (transactionRowWord bytes 32 24)) tail)
    (authorizationIntCallerFrame sp P) -∗
  instr_pre 0x155fc (authorizationU256Post sp bytes 32 (BV 64 0x155fc) tail
    ("x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗ P ∗ True)%I) -∗
  authorizationU256Entry sp (BV 64 0x155e4) (BV 64 (mapIoContextAddress defaultMap))
    bytes 32 (BV 64 0x155fc) tail
    ("x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗ P ∗ True)%I.
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hsuffix & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hbytes & %Hlen & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(H8 & Hpair & Hprefix & HP & _)".
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I with "[Hprefix Hsuffix]" as "Hscratch".
  { iApply (mem_mapsto_uninit_combine 32 with "Hprefix"); first lia.
    replace ((bv_unsigned sp - 48) + 32)%Z with (bv_unsigned sp - 16)%Z by lia. done. }
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
    (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)])
    with "[H10 H11 Hpair]" as "Hwords".
  { rewrite !reg_col_cons. iSplitL "H10".
    - iExists _. iFrame. done.
    - iSplitL "H11"; last done. iExists _. iFrame. done. }
  unfold authorizationU256Entry. iFrame. repeat iSplit; done.
Qed.
Print Assumptions authorization_int_to_u256.

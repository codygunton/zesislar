Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.RegPacking.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsInt WriteSuccessExactEncoderIntFramedCall
  WriteSuccessExactTransactionsGasLoads WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma withdrawal_int_next_entry `{!islaG Sigma} `{!threadG}
    sp bytes oldret ret offset tail (P : iProp Sigma) :
  withdrawalIntPost sp bytes oldret
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64
        (bv_unsigned (transactionRowWord bytes 0 offset)))) tail) P -∗
  instr_pre (bv_unsigned ret) (withdrawalIntPost sp bytes ret tail P) -∗
  withdrawalIntEntry sp oldret (BV 64 (mapIoContextAddress defaultMap))
    (BV 64 8) bytes offset ret tail P.
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hscratch & Hmmio & Htrace & Hframe & _)".
  iDestruct "Hframe" as "(Hbytes & %Hlen & %Halign & %Hlow & %Hhigh & HP & _)".
  iAssert (reg_col [(KindReg "x10", BitsShape 64)]) with "[H10]" as "H10col".
  { iApply (reg_col_bv_list_shape [("x10", (sp - BV 64 16)%bv)]). cbn. iFrame. }
  unfold withdrawalIntEntry. iFrame. repeat iSplit; done.
Qed.
Print Assumptions withdrawal_int_next_entry.

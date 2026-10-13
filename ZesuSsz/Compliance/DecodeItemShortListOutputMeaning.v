Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Open Scope Z_scope.

(* This image is the exact retained five-store output. *)
Definition decodeItemShortListUpdatedImage (locals : DecodeItemReturnLocals) : list byte :=
  (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (@bv_unsigned (Npos
  (xO (xO (xO (xO (xO (xO xH))))))) (@bv_add (Npos (xO (xO (xO (xO (xO (xO xH))))))) (returnA1 locals)
  (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) (Zpos xH) I))) (Z.ones (Zpos (xO (xO (xO xH)))))))
  (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) (@bv_add (Npos (xO (xO (xO (xO (xO (xO
  xH))))))) (returnA1 locals) (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) (Zpos xH) I))) (Zpos (xO
  (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv
  (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO
  xH))))))) (@bv_add (Npos (xO (xO (xO (xO (xO (xO xH))))))) (returnA1 locals) (@BV (Npos (xO (xO (xO
  (xO (xO (xO xH))))))) (Zpos xH) I))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Z.ones
  (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO (xO (xO xH))))
  (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) (@bv_add
  (Npos (xO (xO (xO (xO (xO (xO xH))))))) (returnA1 locals) (@BV (Npos (xO (xO (xO (xO (xO (xO
  xH))))))) (Zpos xH) I))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO
  xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO
  (xO (xO xH)))) (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO
  (xO (xO xH))))))) (@bv_add (Npos (xO (xO (xO (xO (xO (xO xH))))))) (returnA1 locals) (@BV (Npos (xO
  (xO (xO (xO (xO (xO xH))))))) (Zpos xH) I))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH)))))
  (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv
  (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr (Z.shiftr (Z.shiftr
  (Z.shiftr (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) (@bv_add (Npos (xO (xO (xO
  (xO (xO (xO xH))))))) (returnA1 locals) (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) (Zpos xH) I)))
  (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO
  xH))))) (Zpos (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO
  xH))))) (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr
  (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) (@bv_add (Npos (xO (xO (xO (xO (xO
  (xO xH))))))) (returnA1 locals) (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) (Zpos xH) I))) (Zpos
  (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH)))))
  (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv
  (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr (Z.shiftr (Z.shiftr
  (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
  (@bv_add (Npos (xO (xO (xO (xO (xO (xO xH))))))) (returnA1 locals) (@BV (Npos (xO (xO (xO (xO (xO
  (xO xH))))))) (Zpos xH) I))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO
  xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO
  (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos
  (xO (xO (xO xH)))) (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) (returnA3 locals))
  (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO (xO (xO
  xH)))) (Z.land (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) (returnA3 locals))
  (Zpos (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO xH)))))
  (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO
  (xO (xO xH))))))) (returnA3 locals)) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Z.ones
  (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO (xO (xO xH))))
  (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
  (returnA3 locals)) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH)))))
  (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO (xO (xO
  xH)))) (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO
  xH))))))) (returnA3 locals)) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO
  xH))))) (Zpos (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO
  xH))))) (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) (returnA3 locals)) (Zpos (xO (xO (xO xH)))))
  (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO
  xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO
  (xO (xO xH)))) (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (@bv_unsigned
  (Npos (xO (xO (xO (xO (xO (xO xH))))))) (returnA3 locals)) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO
  (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO
  (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv
  (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr
  (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) (returnA3 locals)) (Zpos (xO (xO (xO
  xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO
  (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH)))))))
  (@app (bv (Npos (xO (xO (xO xH))))) (@firstn (bv (Npos (xO (xO (xO xH))))) (S (S (S (S (S (S (S (S
  O)))))))) (@insert nat (bv (Npos (xO (xO (xO xH))))) (list (bv (Npos (xO (xO (xO xH))))))
  (@list_insert (bv (Npos (xO (xO (xO xH)))))) O (@bv_extract (Npos (xO (xO (xO (xO (xO (xO xH)))))))
  N0 (Npos (xO (xO (xO xH)))) (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) (Zpos xH) I)) (@skipn (bv
  (Npos (xO (xO (xO xH))))) (N.to_nat (Npos (xO (xO (xO xH))))) (@skipn (bv (Npos (xO (xO (xO xH)))))
  (N.to_nat (Npos (xO (xO (xO xH))))) (@app (bv (Npos (xO (xO (xO xH))))) (@firstn (bv (Npos (xO (xO
  (xO xH))))) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
  (S (S (S O)))))))))))))))))))))))))))))))) (returnStorage locals)) (@cons (bv (Npos (xO (xO (xO
  xH))))) (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO xH))))) (@BV
  (Npos (xO (xO (xO (xO xH))))) Z0 I)) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO
  (xO xH))))) (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO
  xH))))) (@BV (Npos (xO (xO (xO (xO xH))))) Z0 I)) (Zpos (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO
  (xO xH))))))) (@skipn (bv (Npos (xO (xO (xO xH))))) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (N.to_nat (Npos (xO
  xH))))))))))))))))))))))))))))))))))) (returnStorage locals))))))))) (@cons (bv (Npos (xO (xO (xO
  xH))))) (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO
  xH))))))) (@bv_add (Npos (xO (xO (xO (xO (xO (xO xH))))))) (returnA3 locals) (@BV (Npos (xO (xO (xO
  (xO (xO (xO xH))))))) (Zpos xH) I))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO
  (xO xH))))) (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO
  (xO (xO xH))))))) (@bv_add (Npos (xO (xO (xO (xO (xO (xO xH))))))) (returnA3 locals) (@BV (Npos (xO
  (xO (xO (xO (xO (xO xH))))))) (Zpos xH) I))) (Zpos (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO
  xH))))))) (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr
  (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) (@bv_add (Npos (xO (xO (xO (xO (xO
  (xO xH))))))) (returnA3 locals) (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) (Zpos xH) I))) (Zpos
  (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos
  (xO (xO (xO xH))))) (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr (Z.shiftr (Z.shiftr
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) (@bv_add (Npos (xO (xO (xO (xO (xO (xO
  xH))))))) (returnA3 locals) (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) (Zpos xH) I))) (Zpos (xO
  (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO
  xH))))))) (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr
  (Z.shiftr (Z.shiftr (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) (@bv_add (Npos
  (xO (xO (xO (xO (xO (xO xH))))))) (returnA3 locals) (@BV (Npos (xO (xO (xO (xO (xO (xO xH)))))))
  (Zpos xH) I))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos
  (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO xH)))))
  (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr
  (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) (@bv_add (Npos (xO (xO (xO (xO (xO (xO
  xH))))))) (returnA3 locals) (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) (Zpos xH) I))) (Zpos (xO
  (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos
  (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO xH)))))
  (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr
  (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH))))))) (@bv_add (Npos (xO (xO (xO (xO (xO
  (xO xH))))))) (returnA3 locals) (@BV (Npos (xO (xO (xO (xO (xO (xO xH))))))) (Zpos xH) I))) (Zpos
  (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH)))))
  (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv
  (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO (xO (xO xH)))) (Z.land (Z.shiftr (Z.shiftr (Z.shiftr
  (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO (xO (xO xH)))))))
  (@bv_add (Npos (xO (xO (xO (xO (xO (xO xH))))))) (returnA3 locals) (@BV (Npos (xO (xO (xO (xO (xO
  (xO xH))))))) (Zpos xH) I))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO
  xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO (xO xH))))) (Zpos (xO (xO
  (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@skipn (bv (Npos (xO (xO (xO xH))))) (S (S (S (S (S
  (S (S (S (N.to_nat (Npos (xO (xO (xO xH))))))))))))) (@insert nat (bv (Npos (xO (xO (xO xH)))))
  (list (bv (Npos (xO (xO (xO xH)))))) (@list_insert (bv (Npos (xO (xO (xO xH)))))) O (@bv_extract
  (Npos (xO (xO (xO (xO (xO (xO xH))))))) N0 (Npos (xO (xO (xO xH)))) (@BV (Npos (xO (xO (xO (xO (xO
  (xO xH))))))) (Zpos xH) I)) (@skipn (bv (Npos (xO (xO (xO xH))))) (N.to_nat (Npos (xO (xO (xO
  xH))))) (@skipn (bv (Npos (xO (xO (xO xH))))) (N.to_nat (Npos (xO (xO (xO xH))))) (@app (bv (Npos
  (xO (xO (xO xH))))) (@firstn (bv (Npos (xO (xO (xO xH))))) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
  (returnStorage locals)) (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO (xO (xO xH))))
  (Z.land (@bv_unsigned (Npos (xO (xO (xO (xO xH))))) (@BV (Npos (xO (xO (xO (xO xH))))) Z0 I))
  (Z.ones (Zpos (xO (xO (xO xH))))))) (@cons (bv (Npos (xO (xO (xO xH))))) (Z_to_bv (Npos (xO (xO (xO
  xH)))) (Z.land (Z.shiftr (@bv_unsigned (Npos (xO (xO (xO (xO xH))))) (@BV (Npos (xO (xO (xO (xO
  xH))))) Z0 I)) (Zpos (xO (xO (xO xH))))) (Z.ones (Zpos (xO (xO (xO xH))))))) (@skipn (bv (Npos (xO
  (xO (xO xH))))) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
  (S (S (S (S (N.to_nat (Npos (xO xH))))))))))))))))))))))))))))))))))) (returnStorage
  locals)))))))))))))))))))))))))))))))))).

Definition decodeItemShortListOutputFacts
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals)
    (inputPrefix : byte) (rest : list byte) : Prop :=
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
  length (returnStorage locals) = 40%nat /\
  decodeItemInputHead args inputPrefix rest /\
  192 <= bv_unsigned inputPrefix /\ bv_unsigned inputPrefix <= 247 /\
  bv_unsigned (returnA1 locals) = decodeItemInputPointer args /\
  bv_unsigned (returnA3 locals) = bv_unsigned inputPrefix - 192 /\
  decodeItemAcceptedFacts args true 1 (bv_unsigned inputPrefix - 192) /\
  returnStorage locals = decodeItemBeforeStorage args /\
  decodeItemInputLength args = Z.of_nat (length (decodeItemInputBytes args)) /\
  0 <= decodeItemInputPointer args /\
  decodeItemInputPointer args + decodeItemInputLength args < RlpDecodeItem.word64Modulus.

Lemma decodeItemShortListUpdatedMeaning args locals inputPrefix rest :
  decodeItemShortListOutputFacts args locals inputPrefix rest ->
  DecodeMeaningModuloKnownBugs args (decodeItemShortListUpdatedImage locals).
Proof.
  intros (H0 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & HarrayFact9 & HarrayFact11 & HarrayFact13).
  unfold decodeItemShortListUpdatedImage.
  1: rename select (length (returnStorage locals) = _) into HstorageLength.
  1: lazymatch goal with |- DecodeMeaningModuloKnownBugs args ?after => assert (HcanonicalImage : after = decodeItemOkBytes (returnStorage locals) (bv_to_little_endian 8 8 (bv_unsigned ((returnA1 locals + 1)%bv))) (bv_to_little_endian 8 8 (bv_unsigned (returnA3 locals))) (bv_to_little_endian 8 8 (bv_unsigned ((returnA3 locals + 1)%bv))) true) by (generalize HstorageLength; generalize (returnStorage locals); intros before Hlength; clear -before Hlength locals; do 40 (destruct before as [|? before]; [discriminate |]); destruct before; [unfold decodeItemOkBytes, bv_to_little_endian, Z_to_little_endian; cbn [Z.iter Pos.iter Z.of_N N.to_nat take drop firstn skipn list_fmap fmap insert]; repeat (rewrite Z.land_ones; last lia); repeat (rewrite Z.shiftr_div_pow2; last lia); reflexivity | cbn in Hlength; lia]) end.
  rewrite HcanonicalImage.
  eapply (decodeItemShortListPostMeaning args _ (bv_unsigned inputPrefix - 192)).
  1: exact (proj2 H0).
  1: exact H8.
  1: rewrite <- H9; apply decodeItemOkBytes_encodeSuccess.
  1: exact HstorageLength.
  1-3: apply length_bv_to_little_endian; compute; discriminate.
  1: rewrite decodeItemByteDecoderBridge little_endian_to_bv_to_little_endian; last lia.
  1: rewrite Z.mod_small; last (change (0 <= bv_unsigned (returnA1 locals + 1) < bv_modulus 64)%Z; apply bv_unsigned_in_range).
  1: unfold RlpDecodeItemSchema.itemPayloadPointer; rewrite H3; cbn; assert (Hpneq : (bv_unsigned inputPrefix =? 128)%Z = false) by (apply Z.eqb_neq; lia); rewrite Hpneq.
  1: bv_simplify_arith.
  1: rename select (bv_unsigned (returnA1 locals) = decodeItemInputPointer args) into HinputBaseValue.
  1: rewrite HinputBaseValue.
  1: assert (HinputNonempty : (1 <= decodeItemInputLength args)%Z) by (rewrite HarrayFact9 H3; cbn; lia).
  1: rewrite bv_wrap_small; [reflexivity | unfold bv_modulus, RlpDecodeItem.word64Modulus in *; lia].
  1: rename select (bv_unsigned (returnA3 locals) = (bv_unsigned inputPrefix - 192)%Z) into HpayloadValue.
  1: rewrite decodeItemByteDecoderBridge little_endian_to_bv_to_little_endian; last lia.
  1: rewrite Z.mod_small; [exact HpayloadValue | change (0 <= bv_unsigned (returnA3 locals) < bv_modulus 64)%Z; apply bv_unsigned_in_range].
  1: rewrite decodeItemByteDecoderBridge little_endian_to_bv_to_little_endian; last lia.
  1: rewrite Z.mod_small; last (change (0 <= bv_unsigned (returnA3 locals + 1) < bv_modulus 64)%Z; apply bv_unsigned_in_range).
  1: rename select (bv_unsigned (returnA3 locals) = (bv_unsigned inputPrefix - 192)%Z) into HconsumedPayloadValue.
  1: bv_simplify_arith; rewrite HconsumedPayloadValue; unfold bv_wrap, bv_modulus, RlpDecodeItem.word64Modulus; f_equal; lia.
  all: unfold RlpDecodeItem.word64Modulus; lia.
Qed.

#[export] Instance decodeItemShortListOutputDerivedFacts args locals inputPrefix rest :
  ZesuDerivedFacts (decodeItemShortListOutputFacts args locals inputPrefix rest)
    (DecodeMeaningModuloKnownBugs args (decodeItemShortListUpdatedImage locals)).
Proof. exact (decodeItemShortListUpdatedMeaning args locals inputPrefix rest). Qed.

Print Assumptions decodeItemShortListUpdatedMeaning.
Print Assumptions decodeItemShortListOutputDerivedFacts.

Lemma decodeItemShortListOutputRegistration args locals inputPrefix rest :
  ZesuDerivedFacts (decodeItemShortListOutputFacts args locals inputPrefix rest)
    (DecodeMeaningModuloKnownBugs args (decodeItemShortListUpdatedImage locals)).
Proof. exact (decodeItemShortListOutputDerivedFacts args locals inputPrefix rest). Qed.
Print Assumptions decodeItemShortListOutputRegistration.

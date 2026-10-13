Require Import ZesuSsz.Automation.All.
Require Import isla.isla isla.riscv64.riscv64.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemReturnExitResources.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImageDef.
Require Import ZesuSsz.Contracts.RlpDecodeItemReturnImages.
Open Scope Z_scope.

Definition decodeItemLongStringMachineMeaningFacts
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals)
    (prefix : byte) (rest : list byte) (after : DecodeItemOutcome) : Prop :=
  decodeItemC1BDomain args /\
  decodeItemLongAcceptedFacts args false (1 + (bv_unsigned prefix - 183))
    (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned prefix - 183)) rest)) /\
  length (returnStorage locals) = 40%nat /\
  returnStorage locals = decodeItemBeforeStorage args /\
  decodeItemInputHead args prefix rest /\
  184 <= bv_unsigned prefix <= 191 /\
  0 <= RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned prefix - 183)) rest) /\
  bv_unsigned (returnA1 locals) = decodeItemInputPointer args + (1 + (bv_unsigned prefix - 183)) /\
  bv_unsigned (returnA3 locals) = RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned prefix - 183)) rest) /\
  bv_unsigned (returnA4 locals) = ((1 + (bv_unsigned prefix - 183) +
    RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned prefix - 183)) rest)) mod RlpDecodeItem.word64Modulus) /\
  after = decodeItemOkBytes (returnStorage locals)
    (bv_to_little_endian 8 8 (bv_unsigned (returnA1 locals)))
    (bv_to_little_endian 8 8 (bv_unsigned (returnA3 locals)))
    (bv_to_little_endian 8 8 (bv_unsigned (returnA4 locals))) false.

Lemma decodeItemLongStringMachineOutputMeaning args locals prefix rest after :
  decodeItemLongStringMachineMeaningFacts args locals prefix rest after ->
  DecodeMeaningModuloKnownBugs args after.
Proof.
  intros (Hdomain & Haccepted & Hlength & Hbefore & Hhead & Hprefix &
    Hnonnegative & Hpointer & Hpayload & Hconsumed & Himage).
  rewrite Himage.
  eapply (decodeItemLongStringPostMeaning args _ (1 + (bv_unsigned prefix - 183))
    (RlpDecodeItem.bigEndian (take (Z.to_nat (bv_unsigned prefix - 183)) rest))).
  - exact Hdomain.
  - exact Haccepted.
  - rewrite <- Hbefore. apply decodeItemOkBytes_encodeSuccess.
    + exact Hlength.
    + apply length_bv_to_little_endian; compute; discriminate.
    + apply length_bv_to_little_endian; compute; discriminate.
    + apply length_bv_to_little_endian; compute; discriminate.
    + rewrite (littleEndian_machine_bytes 8); last (change (0 <= bv_unsigned (returnA1 locals) < bv_modulus 64); apply bv_unsigned_in_range).
      rewrite Hpointer. unfold RlpDecodeItemSchema.itemPayloadPointer.
      rewrite Hhead. cbn. assert (Hempty : (bv_unsigned prefix =? 128) = false) by (apply Z.eqb_neq; lia).
      rewrite Hempty. reflexivity.
    + rewrite (littleEndian_machine_bytes 8); [exact Hpayload | change (0 <= bv_unsigned (returnA3 locals) < bv_modulus 64); apply bv_unsigned_in_range].
    + rewrite (littleEndian_machine_bytes 8); [exact Hconsumed | change (0 <= bv_unsigned (returnA4 locals) < bv_modulus 64); apply bv_unsigned_in_range].
  - lia.
  - exact Hnonnegative.
Qed.

Global Instance decodeItemLongStringOutputMeaningDerived args locals prefix rest after :
  ZesuDerivedFacts (decodeItemLongStringMachineMeaningFacts args locals prefix rest after)
    (DecodeMeaningModuloKnownBugs args after) :=
  decodeItemLongStringMachineOutputMeaning args locals prefix rest after.

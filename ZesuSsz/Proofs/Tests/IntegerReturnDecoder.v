Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Automation.ReturnRoute.
Require Import ZesuSsz.Compliance.DecodeItemReturnRestorationFacts.
Require Import ZesuSsz.Contracts.DecodeItemFrameImage.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
Open Scope Z_scope.

Lemma return_decoder_expression (Sigma : gFunctors)
    (args : DecodeItemArgs) (frameBytes : list byte)
    (Hframe : decodeItemSavedFrameFacts args frameBytes)
    (Haligned : (decodeItemReturnAddress args mod 4 = 0)%Z) :
  LiTactic (normalize_instr_addr (Σ:=Sigma)
    (bv_unsigned (bv_or (bv_and (bv_add
      (Z_to_bv 64 (little_endian_to_bv 8
        (take (N.to_nat 8) (drop
          (Z.to_nat (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 -
            (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))) frameBytes))))
      (BV 64 0)) (BV 64 18446744073709551614)) (BV 64 0)))).
Proof.
  autorewrite with isla_coq_rewrite.
  typeclasses eauto.
Qed.

Lemma return_decoder_target
    (args : DecodeItemArgs) (frameBytes : list byte)
    (Hframe : decodeItemSavedFrameFacts args frameBytes)
    (Haligned : (decodeItemReturnAddress args mod 4 = 0)%Z) :
  bv_wrap 64 (bv_unsigned (bv_or (bv_and (bv_add
    (Z_to_bv 64 (little_endian_to_bv 8
      (take (N.to_nat 8) (drop
        (Z.to_nat (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 -
          (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))) frameBytes))))
    (BV 64 0)) (BV 64 18446744073709551614)) (BV 64 0))) =
  bv_wrap 64 (decodeItemReturnAddress args).
Proof.
  autorewrite with isla_coq_rewrite.
  apply zesu_ret_target. lia.
Qed.

Lemma return_decoder_fault_expression
    (args : DecodeItemArgs) (frameBytes : list byte)
    (Hframe : decodeItemSavedFrameFacts args frameBytes)
    (Hrange : (0 <= decodeItemReturnAddress args < 2 ^ 64)%Z)
    (Haligned : (decodeItemReturnAddress args mod 4 = 0)%Z) :
  SimplImpl (bv_extract 0 1 (bv_shiftr
    (bv_or (bv_and (bv_add
      (Z_to_bv 64 (little_endian_to_bv 8
        (take (N.to_nat 8) (drop
          (Z.to_nat (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes + 8 -
            (decodeItemStackPointer args - RlpDecodeItem.decodeItemStackBytes))) frameBytes))))
      (BV 64 0)) (BV 64 18446744073709551614)) (BV 64 0)) (BV 64 1)) = BV 1 1) False.
Proof.
  autorewrite with lithium_rewrite.
  typeclasses eauto.
Qed.

Print Assumptions return_decoder_expression.
Print Assumptions return_decoder_target.
Print Assumptions return_decoder_fault_expression.

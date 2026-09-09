From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockOutputSupport.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsBlockEncoderIntSupport.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d10.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d1c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d20.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24.

Import ListNotations.
Open Scope Z_scope.

Lemma writeSuccessEncoderIntStackUnsigned sp :
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  bv_unsigned (sp - BV 64 16)%bv = bv_unsigned sp - 16.
Proof.
  intros Hrange. unfold islaMemoryRange in Hrange.
  bv_solve.
Qed.

Lemma writeSuccessEncoderIntPrefixFacts regs sp :
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntRegs1 regs sp) /\
  writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntRegs2 regs sp) /\
  writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntRegs3 regs sp) /\
  writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntRegs4 regs sp) /\
  writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntRegs5 regs sp) /\
  writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntRegs6 regs sp) /\
  writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntRegs7 regs sp).
Proof.
  intros Hfacts.
  have H1 : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntRegs1 regs sp).
  { unfold writeSuccessEncoderIntRegs1, writeSuccess15d10Regs.
    repeat (apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|]). exact Hfacts. }
  have H2 : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntRegs2 regs sp).
  { unfold writeSuccessEncoderIntRegs2, writeSuccess15d14Regs.
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|exact H1]. }
  have H3 : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntRegs3 regs sp).
  { unfold writeSuccessEncoderIntRegs3, writeSuccess15d18Regs.
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|exact H2]. }
  have H4 : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntRegs4 regs sp).
  { change (writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccess15d1cRegs (writeSuccessEncoderIntRegs3 regs sp)
        (sp - BV 64 16)%bv)).
    unfold writeSuccess15d1cRegs.
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|].
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|exact H3]. }
  have H5 : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntRegs5 regs sp).
  { change (writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccess15d20Regs (writeSuccessEncoderIntRegs4 regs sp))).
    unfold writeSuccess15d20Regs.
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|].
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|exact H4]. }
  have H6 : writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccessEncoderIntRegs6 regs sp).
  { change (writeSuccessWithdrawalsOperationalRegisterFacts
      (writeSuccess15d24Regs (writeSuccessEncoderIntRegs5 regs sp))).
    unfold writeSuccess15d24Regs.
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|].
    apply writeSuccessEncoderIntFactsInsert; [cbn; tauto|exact H5]. }
  have H7 := writeSuccessEncoderIntRegs7Facts regs sp Hfacts.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [exact H4|]. split; [exact H5|]. split; assumption.
Qed.

Lemma writeSuccessEncoderIntStoreAssumes regs (stack : bv 64) :
  regs !! "x2" = Some (RVal_Bits stack) ->
  regs !! "rv_ram_base" = Some (RVal_Bits (BV 64 0x20000000)) ->
  regs !! "rv_ram_size" = Some (RVal_Bits (BV 64 0x20000000)) ->
  islaMemoryRange (bv_unsigned stack) 16 ->
  bv_unsigned stack `mod` 8 = 0 ->
  0x20000000 <= bv_unsigned stack ->
  bv_unsigned stack + 16 <= 0x40000000 ->
  eval_a_exp regs writeSuccess15d14Aligned = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess15d14Lower = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess15d14Upper = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess15d18Aligned = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess15d18Lower = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess15d18Upper = Some (Val_Bool true).
Proof.
  intros Hx2 Hrambase Hramsize Hrange Haligned HramLower HramUpper.
  unfold islaMemoryRange in Hrange.
  have Ha14 : eval_a_exp regs writeSuccess15d14Aligned = Some (Val_Bool true).
  { unfold writeSuccess15d14Aligned. cbn. rewrite Hx2. cbn.
    change (Some (Val_Bool (bool_decide
      (bv_extract 0 3 (stack + BV 64 8)%bv = BV 3 0))) =
      Some (Val_Bool true)).
    repeat apply f_equal. apply bool_decide_eq_true_2. bv_solve. }
  have Hl14 : eval_a_exp regs writeSuccess15d14Lower = Some (Val_Bool true).
  { unfold writeSuccess15d14Lower. cbn. rewrite Hx2 Hrambase. cbn.
    lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
      option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
      decide_rel foldl].
    repeat apply f_equal. apply bool_decide_eq_true_2.
    rewrite bv_add_unsigned. rewrite bv_wrap_small.
    - change (bv_unsigned stack + 8 >= 0x20000000). lia.
    - change (0 <= bv_unsigned stack + 8 < 2 ^ 64). lia. }
  have Hu14 : eval_a_exp regs writeSuccess15d14Upper = Some (Val_Bool true).
  { unfold writeSuccess15d14Upper. cbn. rewrite Hx2 Hrambase Hramsize. cbn.
    lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
      option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
      decide_rel foldl].
    repeat apply f_equal. apply bool_decide_eq_true_2.
    change (bv_unsigned (stack + BV 64 8)%bv <= 0x3ffffff8).
    bv_solve. }
  have Ha18 : eval_a_exp regs writeSuccess15d18Aligned = Some (Val_Bool true).
  { unfold writeSuccess15d18Aligned. cbn. rewrite Hx2. cbn.
    lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
      option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
      decide_rel foldl].
    repeat apply f_equal. apply bool_decide_eq_true_2.
    change (bv_extract 0 3 (stack + BV 64 0)%bv = BV 3 0). bv_solve. }
  have Hl18 : eval_a_exp regs writeSuccess15d18Lower = Some (Val_Bool true).
  { unfold writeSuccess15d18Lower. cbn. rewrite Hx2 Hrambase. cbn.
    lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
      option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
      decide_rel foldl].
    repeat apply f_equal. apply bool_decide_eq_true_2.
    change (bv_unsigned (stack + BV 64 0)%bv >= 0x20000000). bv_solve. }
  have Hu18 : eval_a_exp regs writeSuccess15d18Upper = Some (Val_Bool true).
  { unfold writeSuccess15d18Upper. cbn. rewrite Hx2 Hrambase Hramsize. cbn.
    lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
      option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
      decide_rel foldl].
    repeat apply f_equal. apply bool_decide_eq_true_2.
    change (bv_unsigned (stack + BV 64 0)%bv <= 0x3ffffff8). bv_solve. }
  repeat split; assumption.
Qed.

Lemma writeSuccessEncoderIntStoreFacts regs (stack : bv 64) :
  regs !! "x2" = Some (RVal_Bits stack) ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  islaMemoryRange (bv_unsigned stack) 16 ->
  bv_unsigned stack `mod` 8 = 0 ->
  0x20000000 <= bv_unsigned stack ->
  bv_unsigned stack + 16 <= 0x40000000 ->
  exists mstatusBits satp,
    regs !! "mstatus" = Some
      (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) /\
    regs !! "satp" = Some (RVal_Bits satp) /\
    writeSuccess15d14SysRegs regs /\
    writeSuccess15d18SysRegs regs /\
    eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) /\
    eval_a_exp regs writeSuccess15d14Aligned = Some (Val_Bool true) /\
    eval_a_exp regs writeSuccess15d14Lower = Some (Val_Bool true) /\
    eval_a_exp regs writeSuccess15d14Upper = Some (Val_Bool true) /\
    eval_a_exp regs writeSuccess15d18Aligned = Some (Val_Bool true) /\
    eval_a_exp regs writeSuccess15d18Lower = Some (Val_Bool true) /\
    eval_a_exp regs writeSuccess15d18Upper = Some (Val_Bool true).
Proof.
  intros Hx2 Hfacts Hrange Haligned HramLower HramUpper.
  destruct (writeSuccessOutputRegisterFacts regs Hfacts) as
    (mstatusBits & satp & oldX5 & Hx5 & Hmstatus & Hsatp & Hsys & HmstatusEval).
  have Hrambase := proj1 (proj2 (proj2 Hsys)).
  have Hramsize := proj1 (proj2 (proj2 (proj2 Hsys))).
  destruct (writeSuccessEncoderIntStoreAssumes regs stack Hx2 Hrambase Hramsize
    Hrange Haligned HramLower HramUpper) as
    (Ha14 & Hl14 & Hu14 & Ha18 & Hl18 & Hu18).
  exists mstatusBits, satp. split; [exact Hmstatus|]. split; [exact Hsatp|].
  split. { unfold writeSuccess15d14SysRegs, writeSuccess10198SysRegs in Hsys |- *.
    tauto. }
  split. { unfold writeSuccess15d18SysRegs, writeSuccess10198SysRegs in Hsys |- *.
    tauto. }
  split; [exact HmstatusEval|].
  repeat split; assumption.
Qed.

Lemma writeSuccessEncoderIntInitialReads memory (sp : bv 64) scratch :
  read_mem_list memory (bv_unsigned sp - 16) 16%N = Some scratch ->
  exists low high oldLow oldHigh,
    scratch = low ++ high /\ length low = 8%nat /\ length high = 8%nat /\
    read_mem memory (bv_unsigned sp - 16) 8%N = Some oldLow /\
    read_mem memory (bv_unsigned sp - 8) 8%N = Some oldHigh.
Proof.
  intros Hread.
  change (read_mem_list memory (bv_unsigned sp - 16)
    (N.of_nat (8 + 8)) = Some scratch) in Hread.
  destruct (read_mem_list_split memory (bv_unsigned sp - 16) 8 8 scratch Hread)
    as (low & high & Hscratch & HlowLength & HhighLength & Hlow & Hhigh).
  exists low, high,
    (bv_to_bvn (Z_to_bv (8 * 8) (little_endian_to_bv 8 low))),
    (bv_to_bvn (Z_to_bv (8 * 8) (little_endian_to_bv 8 high))).
  repeat split; try assumption.
  - unfold read_mem. rewrite Hlow. reflexivity.
  - replace (bv_unsigned sp - 8) with (bv_unsigned sp - 16 + 8) by lia.
    unfold read_mem. rewrite Hhigh. reflexivity.
Qed.

Lemma writeSuccessEncoderIntAfterStoresRead global
    (sp returnAddress value : bv 64) :
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  read_mem
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_mem)
    (bv_unsigned sp - 8) 8%N = Some (bv_to_bvn returnAddress).
Proof.
  intros Hrange. unfold read_mem. rewrite writeSuccessEncoderIntGlobal2Memory.
  have HbytesLength :
      length (bv_to_little_endian 8 8 (bv_unsigned value)) = 8%nat.
  { rewrite length_bv_to_little_endian; lia. }
  have HwriteRange : islaMemoryRange (bv_unsigned sp - 16)
      (length (bv_to_little_endian 8 8 (bv_unsigned value))).
  { rewrite HbytesLength. unfold islaMemoryRange in Hrange.
    unfold islaMemoryRange. lia. }
  have Hdisjoint : islaMemoryRangesDisjoint (bv_unsigned sp - 16)
      (length (bv_to_little_endian 8 8 (bv_unsigned value)))
      (bv_unsigned sp - 8) 8.
  { rewrite HbytesLength. unfold islaMemoryRangesDisjoint. lia. }
  pose proof (read_mem_list_write_mem_list_disjoint_eq
    (write_mem_list global.(seq_mem) (Z_to_bv 64 (bv_unsigned sp - 8))
      (bv_to_little_endian 8 8 (bv_unsigned returnAddress)))
    (bv_unsigned sp - 16)
    (bv_to_little_endian 8 8 (bv_unsigned value))
    (bv_unsigned sp - 8) 8 HwriteRange Hdisjoint) as Hskip.
  change (read_mem_list
    (write_mem_list
      (write_mem_list global.(seq_mem) (Z_to_bv 64 (bv_unsigned sp - 8))
        (bv_to_little_endian 8 8 (bv_unsigned returnAddress)))
      (Z_to_bv 64 (bv_unsigned sp - 16))
      (bv_to_little_endian 8 8 (bv_unsigned value)))
    (bv_unsigned sp - 8) 8%N =
    read_mem_list
      (write_mem_list global.(seq_mem) (Z_to_bv 64 (bv_unsigned sp - 8))
        (bv_to_little_endian 8 8 (bv_unsigned returnAddress)))
      (bv_unsigned sp - 8) 8%N) in Hskip.
  rewrite Hskip. rewrite read_mem_list_written.
  - cbn. rewrite Z_to_bv_little_endian_to_bv_to_little_endian;
      [reflexivity | lia | native_compute; reflexivity].
  - rewrite length_bv_to_little_endian; [|lia].
    unfold islaMemoryRange in Hrange. unfold islaMemoryRange. lia.
Qed.

Lemma writeSuccessEncoderIntAfterStoresValue global
    (sp returnAddress value : bv 64) :
  islaMemoryRange (bv_unsigned sp - 16) 16 ->
  read_mem_list
    (writeSuccessEncoderIntGlobal2 global sp returnAddress value).(seq_mem)
    (bv_unsigned sp - 16) 8%N =
    Some (bv_to_little_endian 8 8 (bv_unsigned value)).
Proof.
  intros Hrange. rewrite writeSuccessEncoderIntGlobal2Memory.
  apply read_mem_list_written. unfold islaMemoryRange in Hrange.
  rewrite length_bv_to_little_endian; [|lia].
  unfold islaMemoryRange. lia.
Qed.

Print Assumptions writeSuccessEncoderIntPrefixFacts.
Print Assumptions writeSuccessEncoderIntStoreFacts.
Print Assumptions writeSuccessEncoderIntAfterStoresRead.
Print Assumptions writeSuccessEncoderIntAfterStoresValue.

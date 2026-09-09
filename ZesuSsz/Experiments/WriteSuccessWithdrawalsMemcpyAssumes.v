From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0.

Open Scope Z_scope.

Lemma writeSuccessMemcpyLoadAssumes regs (address : bv 64) :
  regs !! "x13" = Some (RVal_Bits address) ->
  regs !! "rv_ram_base" = Some (RVal_Bits (BV 64 0x20000000)) ->
  regs !! "rv_ram_size" = Some (RVal_Bits (BV 64 0x20000000)) ->
  0x20000000 <= bv_unsigned address ->
  bv_unsigned address + 1 <= 0x40000000 ->
  eval_a_exp regs writeSuccess101e4Lower = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess101e4Upper = Some (Val_Bool true).
Proof.
  intros Haddress Hrambase Hramsize Hlower Hupper.
  destruct address as [address HaddressRange]. cbn in *.
  split.
  - unfold writeSuccess101e4Lower. cbn. rewrite Haddress Hrambase. cbn.
    lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
      option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
      decide_rel foldl].
    repeat apply f_equal. apply bool_decide_eq_true_2.
    change (bv_unsigned ((BV 64 address) + BV 64 0)%bv >=
      bv_unsigned (BV 64 0x20000000)).
    have Hadd : ((BV 64 address) + BV 64 0)%bv = BV 64 address by bv_solve.
    rewrite Hadd. bv_solve.
  - unfold writeSuccess101e4Upper. cbn.
    rewrite Haddress Hrambase Hramsize. cbn.
    lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
      option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
      decide_rel foldl].
    repeat apply f_equal. apply bool_decide_eq_true_2.
    change (bv_unsigned ((BV 64 address) + BV 64 0)%bv <=
      bv_unsigned (((BV 64 0x20000000) + BV 64 0x20000000) - BV 64 1)%bv).
    have Hleft : ((BV 64 address) + BV 64 0)%bv = BV 64 address by bv_solve.
    have Hright : (((BV 64 0x20000000) + BV 64 0x20000000) - BV 64 1)%bv =
        BV 64 0x3fffffff by bv_solve.
    rewrite Hleft Hright. bv_solve.
Qed.

Lemma writeSuccessMemcpyStoreAssumes regs (address : bv 64) :
  regs !! "x14" = Some (RVal_Bits address) ->
  regs !! "rv_ram_base" = Some (RVal_Bits (BV 64 0x20000000)) ->
  regs !! "rv_ram_size" = Some (RVal_Bits (BV 64 0x20000000)) ->
  0x20000000 <= bv_unsigned address ->
  bv_unsigned address + 1 <= 0x40000000 ->
  eval_a_exp regs writeSuccess101f0Lower = Some (Val_Bool true) /\
  eval_a_exp regs writeSuccess101f0Upper = Some (Val_Bool true).
Proof.
  intros Haddress Hrambase Hramsize Hlower Hupper.
  destruct address as [address HaddressRange]. cbn in *.
  split.
  - unfold writeSuccess101f0Lower. cbn. rewrite Haddress Hrambase. cbn.
    lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
      option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
      decide_rel foldl].
    repeat apply f_equal. apply bool_decide_eq_true_2.
    change (bv_unsigned ((BV 64 address) + BV 64 0)%bv >=
      bv_unsigned (BV 64 0x20000000)).
    have Hadd : ((BV 64 address) + BV 64 0)%bv = BV 64 address by bv_solve.
    rewrite Hadd. bv_solve.
  - unfold writeSuccess101f0Upper. cbn.
    rewrite Haddress Hrambase Hramsize. cbn.
    lazy [read_accessor mapM mbind option_bind eval_manyop eval_binop
      option_fmap option_map fmap mret option_ret guard bvn_to_bv decide
      decide_rel foldl].
    repeat apply f_equal. apply bool_decide_eq_true_2.
    change (bv_unsigned ((BV 64 address) + BV 64 0)%bv <=
      bv_unsigned (((BV 64 0x20000000) + BV 64 0x20000000) - BV 64 1)%bv).
    have Hleft : ((BV 64 address) + BV 64 0)%bv = BV 64 address by bv_solve.
    have Hright : (((BV 64 0x20000000) + BV 64 0x20000000) - BV 64 1)%bv =
        BV 64 0x3fffffff by bv_solve.
    rewrite Hleft Hright. bv_solve.
Qed.

Print Assumptions writeSuccessMemcpyLoadAssumes.
Print Assumptions writeSuccessMemcpyStoreAssumes.

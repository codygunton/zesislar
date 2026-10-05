Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Open Scope Z_scope.

Require Import ZesuSsz.Automation.Hooks.


Lemma region_fault_disabled : True.
Proof. Fail zesu_region_fault_if_enabled. exact I. Qed.

Require Import ZesuSsz.Automation.Switches.RegionFault.
Lemma region_input_cursor_lower (args : DecodeItemArgs) (n i start : Z)
    (bytes : list byte)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)
    (Hfold : decodeItemByteFoldFacts args n i start bytes)
    (Hi : i < n)
    (Hnotram : ~ bv_signed (bv_zero_extend 128 (Z_to_bv 64 (start + i))) >=
      bv_signed (BV 128 (mapRamBase defaultMap))) :
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (start + i))) >=
      bv_signed (BV 128 (mapInputBufferAddress defaultMap)).
Proof. zesu_region_fault_bound_if_enabled. Qed.

Lemma region_input_cursor_capacity (args : DecodeItemArgs) (n i start : Z)
    (bytes : list byte)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)
    (Hfold : decodeItemByteFoldFacts args n i start bytes)
    (Hi : i < n)
    (Hnotram : ~ bv_signed (bv_zero_extend 128 (Z_to_bv 64 (start + i))) >=
      bv_signed (BV 128 (mapRamBase defaultMap))) :
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (start + i)) + BV 128 1) <= bv_signed (BV 128 (mapInputBufferAddress defaultMap + mapInputCapacity defaultMap)).
Proof. zesu_region_fault_bound_if_enabled. Qed.

Lemma region_input_cursor_dynamic_end (args : DecodeItemArgs) (n i start : Z)
    (bytes : list byte)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)
    (Hfold : decodeItemByteFoldFacts args n i start bytes)
    (Hi : i < n) :
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (start + i)) + BV 128 1) <= bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputEnd args))).
Proof. zesu_region_fault_bound_if_enabled. Qed.

Lemma region_input_cursor_ram_end (args : DecodeItemArgs) (n i start : Z)
    (bytes : list byte)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)
    (Hfold : decodeItemByteFoldFacts args n i start bytes)
    (Hi : i < n)
    (Hram : bv_signed (bv_zero_extend 128 (Z_to_bv 64 (start + i))) >=
      bv_signed (BV 128 (mapRamBase defaultMap))) :
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (start + i)) + BV 128 1) <= bv_signed (BV 128 (machineRamEnd defaultMap)).
Proof. zesu_region_fault_bound_if_enabled. Qed.

Lemma region_output_lower_0 (args : DecodeItemArgs)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) :
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemOutputPointer args) + BV 64 0)) >= bv_signed (BV 128 (mapRamBase defaultMap)).
Proof. zesu_region_fault_bound_if_enabled. Qed.

Lemma region_output_upper_0 (args : DecodeItemArgs)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) :
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemOutputPointer args) + BV 64 0) + BV 128 8) <= bv_signed (BV 128 (machineRamEnd defaultMap)).
Proof. zesu_region_fault_bound_if_enabled. Qed.

Lemma region_output_lower_8 (args : DecodeItemArgs)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) :
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemOutputPointer args) + BV 64 8)) >= bv_signed (BV 128 (mapRamBase defaultMap)).
Proof. zesu_region_fault_bound_if_enabled. Qed.

Lemma region_output_upper_8 (args : DecodeItemArgs)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) :
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemOutputPointer args) + BV 64 8) + BV 128 8) <= bv_signed (BV 128 (machineRamEnd defaultMap)).
Proof. zesu_region_fault_bound_if_enabled. Qed.

Section assertion_tests.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma region_fault_assert_lower es ann (address : bv 64) (minimum : Z)
      (Hbound : minimum <= bv_unsigned address) :
    ⊢ WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128 address) >= minimum)))
      Mk_annot) Mk_annot)) ann :t: es).
  Proof. iStartProof. zesu_region_fault_if_enabled. Qed.

  Lemma region_fault_assert_impossible_equal es ann (address : bv 64) (minimum : Z)
      (Hbound : minimum < bv_unsigned address) :
    ⊢ WPasm (Smt (Assert (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128 address) = minimum)))
      Mk_annot)) ann :t: es).
  Proof. iStartProof. zesu_region_fault_if_enabled. Qed.

  Lemma region_fault_assert_missing_bound (address : bv 64) :
    ⊢ WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128 address) >= 1)))
      Mk_annot) Mk_annot)) Mk_annot :t: tnil) -∗
    WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128 address) >= 1)))
      Mk_annot) Mk_annot)) Mk_annot :t: tnil).
  Proof.
    iStartProof. iIntros "Hfault". Fail zesu_region_fault_if_enabled.
    iExact "Hfault".
  Qed.

  Lemma region_fault_assert_reject_boolean (condition : bool) :
    ⊢ WPasm (Smt (Assert (Val (Val_Bool condition) Mk_annot)) Mk_annot :t: tnil) -∗
    WPasm (Smt (Assert (Val (Val_Bool condition) Mk_annot)) Mk_annot :t: tnil).
  Proof.
    iStartProof. iIntros "Hfault". Fail zesu_region_fault_if_enabled.
    iExact "Hfault".
  Qed.
End assertion_tests.

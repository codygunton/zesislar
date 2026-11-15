From Coq Require Import ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Automation2.All.
Open Scope Z_scope.

(* The cursor facts are the pure conjuncts of the generated 6a24 loop entry
   (fp_machineAt00c4_LoopClass0): x15 is the input cursor below the limit x11.
   The entry fixes x11 only as a bitvector sum under the length guard; the
   upper-bound lemmas state its consequence, x11 <= input pointer + length,
   in the arithmetic form that the region rule reads. *)
Lemma region_input_cursor_lower (args : DecodeItemArgs) (machine_x15 machine_x11 : bv 64) (i : Z)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)
    (Hcursor : bv_unsigned machine_x15 = decodeItemInputPointer args + 1 + i)
    (Hindex : 0 <= i)
    (Hlimit : bv_unsigned machine_x15 < bv_unsigned machine_x11)
    (Hnotram : ~ bv_signed (bv_zero_extend 128 machine_x15) >=
      bv_signed (BV 128 (mapRamBase defaultMap))) :
    bv_signed (bv_zero_extend 128 machine_x15) >=
      bv_signed (BV 128 (mapInputBufferAddress defaultMap)).
Proof. ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_bound_if_enabled. Qed.

Lemma region_input_cursor_capacity (args : DecodeItemArgs) (machine_x15 machine_x11 : bv 64) (i : Z)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)
    (Hcursor : bv_unsigned machine_x15 = decodeItemInputPointer args + 1 + i)
    (Hindex : 0 <= i)
    (Hlimit : bv_unsigned machine_x15 < bv_unsigned machine_x11)
    (Hend : bv_unsigned machine_x11 <= decodeItemInputPointer args + decodeItemInputLength args)
    (Hnotram : ~ bv_signed (bv_zero_extend 128 machine_x15) >=
      bv_signed (BV 128 (mapRamBase defaultMap))) :
    bv_signed (bv_zero_extend 128 machine_x15 + BV 128 1) <= bv_signed (BV 128 (mapInputBufferAddress defaultMap + mapInputCapacity defaultMap)).
Proof. ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_bound_if_enabled. Qed.

Lemma region_input_cursor_dynamic_end (args : DecodeItemArgs) (machine_x15 machine_x11 : bv 64) (i : Z)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)
    (Hcursor : bv_unsigned machine_x15 = decodeItemInputPointer args + 1 + i)
    (Hindex : 0 <= i)
    (Hlimit : bv_unsigned machine_x15 < bv_unsigned machine_x11)
    (Hend : bv_unsigned machine_x11 <= decodeItemInputPointer args + decodeItemInputLength args) :
    bv_signed (bv_zero_extend 128 machine_x15 + BV 128 1) <= bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputEnd args))).
Proof. ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_bound_if_enabled. Qed.

Lemma region_input_cursor_ram_end (args : DecodeItemArgs) (machine_x15 machine_x11 : bv 64) (i : Z)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)
    (Hcursor : bv_unsigned machine_x15 = decodeItemInputPointer args + 1 + i)
    (Hindex : 0 <= i)
    (Hlimit : bv_unsigned machine_x15 < bv_unsigned machine_x11)
    (Hend : bv_unsigned machine_x11 <= decodeItemInputPointer args + decodeItemInputLength args)
    (Hram : bv_signed (bv_zero_extend 128 machine_x15) >=
      bv_signed (BV 128 (mapRamBase defaultMap))) :
    bv_signed (bv_zero_extend 128 machine_x15 + BV 128 1) <= bv_signed (BV 128 (machineRamEnd defaultMap)).
Proof. ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_bound_if_enabled. Qed.

Lemma region_output_lower_0 (args : DecodeItemArgs)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) :
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemOutputPointer args) + BV 64 0)) >= bv_signed (BV 128 (mapRamBase defaultMap)).
Proof. ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_bound_if_enabled. Qed.

Lemma region_output_upper_0 (args : DecodeItemArgs)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) :
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemOutputPointer args) + BV 64 0) + BV 128 8) <= bv_signed (BV 128 (machineRamEnd defaultMap)).
Proof. ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_bound_if_enabled. Qed.

Lemma region_output_lower_8 (args : DecodeItemArgs)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) :
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemOutputPointer args) + BV 64 8)) >= bv_signed (BV 128 (mapRamBase defaultMap)).
Proof. ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_bound_if_enabled. Qed.

Lemma region_output_upper_8 (args : DecodeItemArgs)
    (Hdomain : decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args) :
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemOutputPointer args) + BV 64 8) + BV 128 8) <= bv_signed (BV 128 (machineRamEnd defaultMap)).
Proof. ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_bound_if_enabled. Qed.

Set Default Proof Using "Type".

Section assertion_tests.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma region_fault_assert_lower es ann (address : bv 64) (minimum : Z)
      (Hbound : minimum <= bv_unsigned address) :
    ⊢ WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128 address) >= minimum)))
      Mk_annot) Mk_annot)) ann :t: es).
  Proof. iStartProof. ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_if_enabled. Qed.

  Lemma region_fault_assert_impossible_equal es ann (address : bv 64) (minimum : Z)
      (Hbound : minimum < bv_unsigned address) :
    ⊢ WPasm (Smt (Assert (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128 address) = minimum)))
      Mk_annot)) ann :t: es).
  Proof.
    iStartProof.
    Fail ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_if_enabled.
    ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_assert.
  Qed.

  Lemma region_fault_assert_missing_bound (address : bv 64) :
    ⊢ WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128 address) >= 1)))
      Mk_annot) Mk_annot)) Mk_annot :t: tnil) -∗
    WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128 address) >= 1)))
      Mk_annot) Mk_annot)) Mk_annot :t: tnil).
  Proof.
    iStartProof. iIntros "Hfault".
    Fail ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_if_enabled.
    iExact "Hfault".
  Qed.

  Lemma region_fault_assert_reject_boolean (condition : bool) :
    ⊢ WPasm (Smt (Assert (Val (Val_Bool condition) Mk_annot)) Mk_annot :t: tnil) -∗
    WPasm (Smt (Assert (Val (Val_Bool condition) Mk_annot)) Mk_annot :t: tnil).
  Proof.
    iStartProof. iIntros "Hfault".
    Fail ZesuSsz.Automation2.UnionRuleComponents.zesu_region_fault_if_enabled.
    iExact "Hfault".
  Qed.
End assertion_tests.

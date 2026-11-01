Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Definition ram_fault_test_layout (base stop sp size offset width : Z) : Prop :=
  0 <= base /\ stop < 2 ^ 64 /\ 0 <= size <= sp /\
  base + size <= sp <= stop /\ 0 <= offset /\
  offset + width <= size /\ 0 <= width.

Lemma ram_fault_disabled : True.
Proof. Fail zesu_ram_fault_if_enabled. exact I. Qed.

Set Default Proof Using "Type".

Section enabled.
  Local Instance ram_fault_enabled : ZesuStepRamFault := I.

  Lemma ram_fault_upper (base stop sp size offset width : Z)
      (Hlayout : ram_fault_test_layout base stop sp size offset width)
      (Hfault : ~ bv_signed (bv_zero_extend 128
        (Z_to_bv 64 sp + Z_to_bv 64 (-size) + Z_to_bv 64 offset) +
        Z_to_bv 128 width) <= bv_signed (Z_to_bv 128 stop)) : False.
  Proof. zesu_ram_fault_if_enabled. Qed.

  Lemma ram_fault_lower (base stop sp size offset width : Z)
      (Hlayout : ram_fault_test_layout base stop sp size offset width)
      (Hfault : ~ bv_signed (bv_zero_extend 128
        (Z_to_bv 64 sp + Z_to_bv 64 (-size) + Z_to_bv 64 offset)) >=
        bv_signed (Z_to_bv 128 base)) : False.
  Proof. zesu_ram_fault_if_enabled. Qed.

  Lemma ram_fault_missing_layout (sp size offset : Z)
      (Hfault : ~ bv_signed (bv_zero_extend 128
        (Z_to_bv 64 sp + Z_to_bv 64 (-size) + Z_to_bv 64 offset)) >=
        bv_signed (BV 128 1)) : True.
  Proof. Fail zesu_ram_fault_if_enabled. exact I. Qed.

  Lemma ram_fault_normal_branch (sp size offset : Z)
      (Hnormal : bv_signed (bv_zero_extend 128
        (Z_to_bv 64 sp + Z_to_bv 64 (-size) + Z_to_bv 64 offset)) >=
        bv_signed (BV 128 1)) : True.
  Proof. Fail zesu_ram_fault_if_enabled. exact I. Qed.
End enabled.

Section assertion_tests.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma ram_fault_assert_disabled es ann (address : bv 64) :
    ⊢ WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128 address) >= 0)))
      Mk_annot) Mk_annot)) ann :t: es).
  Proof.
    iStartProof. Fail zesu_ram_fault_if_enabled.
    assert (Hswitch : ZesuStepRamFault) by exact I.
    zesu_ram_fault_if_enabled.
  Qed.

  Local Instance ram_fault_assert_enabled : ZesuStepRamFault := I.

  Lemma ram_fault_assert_upper es ann
      (base stop sp size offset width : Z)
      (Hlayout : ram_fault_test_layout base stop sp size offset width) :
    ⊢ WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128
        (Z_to_bv 64 sp + Z_to_bv 64 (-size) + Z_to_bv 64 offset) +
        Z_to_bv 128 width) <= bv_signed (Z_to_bv 128 stop))))
      Mk_annot) Mk_annot)) ann :t: es).
  Proof. iStartProof. zesu_ram_fault_if_enabled. Qed.

  Lemma ram_fault_assert_lower es ann
      (base stop sp size offset width : Z)
      (Hlayout : ram_fault_test_layout base stop sp size offset width) :
    ⊢ WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128
        (Z_to_bv 64 sp + Z_to_bv 64 (-size) + Z_to_bv 64 offset)) >=
        bv_signed (Z_to_bv 128 base)))) Mk_annot) Mk_annot)) ann :t: es).
  Proof. iStartProof. zesu_ram_fault_if_enabled. Qed.

  Lemma ram_fault_assert_let_and_environment es ann
      (base stop sp size offset width : Z)
      (Hlayout : ram_fault_test_layout base stop sp size offset width)
      (resources : iProp Sigma) :
    resources -∗
    (WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128
        (Z_to_bv 64 sp + Z_to_bv 64 (-size) + Z_to_bv 64 offset)) >=
        bv_signed (Z_to_bv 128 base)))) Mk_annot) Mk_annot)) ann :t: es) ∧ True).
  Proof.
    iStartProof. iIntros "Hresources".
    lazymatch goal with |- environments.envs_entails ?context ?target =>
      pose (faultContext := context); change (environments.envs_entails faultContext target)
    end.
    lazymatch goal with |- context[bool_decide ?bound] =>
      set (faultDecision := bool_decide bound)
    end.
    zesu_ram_fault_if_enabled.
  Qed.

  Lemma ram_fault_assert_missing_layout (address : bv 64) :
    ⊢ WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128 address) >= 1)))
      Mk_annot) Mk_annot)) Mk_annot :t: tnil) -∗
    WPasm (Smt (Assert (Unop Not (Val (Val_Bool
      (bool_decide (bv_signed (bv_zero_extend 128 address) >= 1)))
      Mk_annot) Mk_annot)) Mk_annot :t: tnil).
  Proof.
    iStartProof. iIntros "Hfault". Fail zesu_ram_fault_if_enabled. iExact "Hfault".
  Qed.

  Lemma ram_fault_assert_reject_boolean (condition : bool) :
    ⊢ WPasm (Smt (Assert (Unop Not (Val (Val_Bool condition)
      Mk_annot) Mk_annot)) Mk_annot :t: tnil) -∗
    WPasm (Smt (Assert (Unop Not (Val (Val_Bool condition)
      Mk_annot) Mk_annot)) Mk_annot :t: tnil).
  Proof.
    iStartProof. iIntros "Hfault". Fail zesu_ram_fault_if_enabled. iExact "Hfault".
  Qed.
End assertion_tests.

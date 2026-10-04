Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Definition ram_fault_test_layout (base stop sp size offset width : Z) : Prop :=
  0 <= base /\ stop < 2 ^ 64 /\ 0 <= size <= sp /\
  base + size <= sp <= stop /\ 0 <= offset /\
  offset + width <= size /\ 0 <= width.

Lemma ram_fault_disabled : True.
Proof. Fail zesu_ram_fault_if_enabled. exact I. Qed.

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

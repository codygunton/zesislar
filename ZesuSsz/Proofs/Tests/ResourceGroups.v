Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Resources.

Lemma resource_groups_array_frame `{!islaG Sigma}
    (address : Z) (bytes : list (bv 8)) (word : bv 64) (P : iProp Sigma) :
  (address ↦ₘ word ∗ (address + 8)%Z ↦ₘ∗ bytes ∗ P) -∗
  address ↦ₘ word ∗ (address + 8)%Z ↦ₘ∗ bytes ∗ P ∗ True.
Proof.
  iStartProof. iIntros "Hgroup". zesu_open_resource_groups. zesu_run.
Qed.
Print Assumptions resource_groups_array_frame.

Lemma resource_groups_nested `{!islaG Sigma}
    (address : Z) (word : bv 64) (P Q : iProp Sigma) :
  ((address ↦ₘ word ∗ P) ∗ Q) -∗ address ↦ₘ word ∗ P ∗ Q ∗ True.
Proof.
  iStartProof. iIntros "Hgroup". zesu_open_resource_groups. zesu_run.
Qed.
Print Assumptions resource_groups_nested.

Lemma resource_array_ram_offset `{!islaG Sigma}
    (pointer : bv 64) (bytes : list (bv 8)) :
  0x20000000 <= bv_unsigned pointer ->
  bv_unsigned pointer + 32 < 0x40000000 ->
  (bv_unsigned pointer + 16)%Z ↦ₘ∗ bytes -∗
  bv_unsigned (pointer + BV 64 16)%bv ↦ₘ∗ bytes ∗ True.
Proof.
  intros Hlower Hupper. iStartProof. iIntros "Hbytes".
  zesu_normalize_resource_addresses. zesu_run.
Qed.
Print Assumptions resource_array_ram_offset.

Lemma resource_groups_pure `{!islaG Sigma}
    (address : Z) (word : bv 64) (n : nat) :
  (address ↦ₘ word ∗ ⌜n = 0%nat⌝) -∗
  address ↦ₘ word ∗ ⌜n <= 1⌝ ∗ True.
Proof.
  iStartProof. iIntros "Hgroup". zesu_open_resource_groups. zesu_run.
Qed.
Print Assumptions resource_groups_pure.

Lemma resource_bits_collection `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  reg_col [(KindReg "x6", BitsShape 64); (KindReg "x7", BitsShape 64)] -∗
  P -∗ reg_col [(KindReg "x7", BitsShape 64)] ∗
  "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗ P ∗ True.
Proof.
  iStartProof. iIntros "Hregisters HP".
  zesu_open_bits_registers. zesu_run.
Qed.
Print Assumptions resource_bits_collection.

Lemma resource_bits_bundled `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  reg_col [(KindReg "x6", BitsShape 64); (KindReg "x7", BitsShape 64);
    (KindReg "x28", BitsShape 64); (KindReg "x29", BitsShape 64);
    (KindReg "x30", BitsShape 64); (KindReg "x31", BitsShape 64)] -∗
  P -∗ ∃ x : valu *ₗ (), ⌜valu_has_shape x.1ₗ (BitsShape 64)⌝ ∗
    "x7" ↦ᵣ x.1ₗ ∗
    reg_col [(KindReg "x28", BitsShape 64); (KindReg "x29", BitsShape 64);
      (KindReg "x30", BitsShape 64); (KindReg "x31", BitsShape 64)] ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗ P ∗ True.
Proof.
  iStartProof. iIntros "Hregisters HP". zesu_open_bits_registers.
  zesu_pack_register "x7". zesu_run.
Qed.
Print Assumptions resource_bits_bundled.

Lemma resource_branch_frame `{!islaG Sigma} `{!threadG}
    (sp total cursor : bv 64) (P : iProp Sigma) :
  reg_col zesu_ram_sys_regs ∗ reg_col [(KindReg "x7", BitsShape 64)] ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits total ∗
    "x11" ↦ᵣ RVal_Bits cursor ∗ P ∗ True ⊣⊢
  reg_col zesu_ram_sys_regs ∗ "x10" ↦ᵣ RVal_Bits total ∗
    "x11" ↦ᵣ RVal_Bits cursor ∗
    (reg_col [(KindReg "x7", BitsShape 64)] ∗ "x2" ↦ᵣ RVal_Bits sp ∗
      P ∗ True) ∗ True.
Proof. apply zesu_branch_resource_equiv. Qed.
Print Assumptions resource_branch_frame.
Print Assumptions zesu_branch_resource_equiv.

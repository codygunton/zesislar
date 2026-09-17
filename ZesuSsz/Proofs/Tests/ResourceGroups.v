Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Resources.

Definition resource_groups_closed_package `{!islaG Sigma}
    (address : Z) (word : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (address ↦ₘ word ∗ P ∗ True)%I.

Lemma resource_groups_open_matching_package `{!islaG Sigma}
    (address : Z) (word : bv 64) (P Q : iProp Sigma) :
  resource_groups_closed_package address word P -∗ Q -∗
  address ↦ₘ word ∗ Q ∗ P ∗ True.
Proof.
  iStartProof. iIntros "Hpackage HQ". zesu_run.
Qed.
Print Assumptions resource_groups_open_matching_package.

Definition resource_groups_array_leaf `{!islaG Sigma}
    (address : Z) (bytes : list (bv 8)) : iProp Sigma :=
  (address ↦ₘ∗ bytes ∗ ⌜length bytes = length bytes⌝)%I.
Global Instance : LithiumUnfold (@resource_groups_array_leaf) := I.

Definition resource_groups_array_middle `{!islaG Sigma}
    (address : Z) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (P ∗ resource_groups_array_leaf address bytes ∗ True)%I.
Global Instance : LithiumUnfold (@resource_groups_array_middle) := I.

Definition resource_groups_array_outer `{!islaG Sigma}
    (address : Z) (bytes : list (bv 8)) (P Q : iProp Sigma) : iProp Sigma :=
  (Q ∗ resource_groups_array_middle address bytes P ∗ True)%I.
Global Instance : LithiumUnfold (@resource_groups_array_outer) := I.

Lemma resource_groups_open_requested_array_path `{!islaG Sigma}
    (address : Z) (bytes : list (bv 8)) (P Q : iProp Sigma) :
  resource_groups_array_outer address bytes P Q -∗
  address ↦ₘ∗ bytes ∗ ⌜length bytes = length bytes⌝ ∗ P ∗ Q ∗ True.
Proof.
  iStartProof. iIntros "Houter".
  zesu_rotate_descriptor_resources.
Qed.
Print Assumptions resource_groups_open_requested_array_path.

Lemma resource_groups_assumption_first_pure `{!islaG Sigma} `{!threadG}
    (fact : Prop) (P : iProp Sigma) :
  fact -> P -∗ (P ∗ ⌜fact⌝ ∗ ⌜fact⌝ ∗ True)%I.
Proof.
  intros Hfact. iStartProof. iIntros "HP". iFrame.
  zesu_finish_pure_resources.
Qed.
Print Assumptions resource_groups_assumption_first_pure.

Lemma resource_groups_environment_alias `{!islaG Sigma}
    (P : iProp Sigma) :
  P -∗ P ∗ True.
Proof.
  iStartProof. iIntros "HP".
  lazymatch goal with
  | |- environments.envs_entails ?current ?requested =>
      pose (IPM_JANNO := current);
      change (environments.envs_entails IPM_JANNO requested)
  end.
  zesu_expose_environment_alias. iFrame.
Qed.
Print Assumptions resource_groups_environment_alias.

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
  (mapRamBase defaultMap) <= bv_unsigned pointer ->
  bv_unsigned pointer + 32 < (machineRamEnd defaultMap) ->
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

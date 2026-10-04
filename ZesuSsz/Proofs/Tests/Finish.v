Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.Hooks.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Generated.TestTraces.LdX16X10Off80.

Import ZesuSsz.Automation.Hooks.

Lemma finish_extract_alias (value : bv 64) (bits : bv 1) :
  bv_extract 0 1 value = bits ->
  let alias := value in bv_extract 0 1 alias = bits.
Proof.
  intros Hbits. zesu_finish_extract_alias.
Qed.
Print Assumptions finish_extract_alias.

Lemma finish_list_slice_length (xs : list nat) (count : nat) :
  length (take count xs) <= length xs.
Proof. zesu_finish_list_slice_length. Qed.
Print Assumptions finish_list_slice_length.

Lemma finish_little_endian_constant :
  Z_to_little_endian 8 1 0 = [0%Z; 0%Z; 0%Z; 0%Z;
    0%Z; 0%Z; 0%Z; 0%Z].
Proof. zesu_finish_little_endian. Qed.
Print Assumptions finish_little_endian_constant.

Lemma finish_introduced_code_list `{!islaG Sigma} (P : iProp Sigma) :
  ([∗ list] x ∈ [1%nat; 2%nat], P)%I -∗ P ∗ P.
Proof.
  iStartProof. iIntros "Hlist".
  zesu_reduce_introduced_code_lists.
  iDestruct "Hlist" as "[HP1 [HP2 _]]". iFrame.
Qed.
Print Assumptions finish_introduced_code_list.

#[local] Hint Rewrite zesu_bv_sign_extend_same : isla_coq_rewrite.
#[local] Hint Rewrite zesu_bv_unsigned_add_Z_64 using bv_solve
  : isla_coq_rewrite lithium_rewrite.
#[local] Hint Rewrite zesu_bv_unsigned_add_no_wrap_64 using bv_solve
  : isla_coq_rewrite lithium_rewrite.

Lemma test_zesu_block `{!islaG Sigma} `{!threadG}
    (base : bv 64) (bytes : list (bv 8)) :
  length bytes = 288%nat ->
  instr 0x15048 (Some trace_ld_x16_x10_80) -∗
  instr_body 0x15048 (
    reg_col zesu_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits base ∗
    "x16" ↦ᵣ: (fun _ => True) ∗
    ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned base ∧
      bv_unsigned base + 288 <= (machineRamEnd defaultMap)⌝ ∗
    bv_unsigned base ↦ₘ∗ bytes ∗
    instr_pre 0x1504c (
      reg_col zesu_sys_regs ∗
      "x10" ↦ᵣ RVal_Bits base ∗
      "x16" ↦ᵣ RVal_Bits
        (Z_to_bv 64
          (little_endian_to_bv 8 (take 8 (drop 80 bytes)))) ∗
      bv_unsigned base ↦ₘ∗ bytes ∗ True) ∗ True).
Proof.
  move => Hlength.
  zesu_block.
Qed.

Print Assumptions test_zesu_block.

Lemma test_zesu_pack `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  P -∗ ∃ n : nat, ⌜n = 7%nat⌝ ∗ P.
Proof.
  iStartProof. iIntros "HP". zesu_pack 7%nat.
Qed.

Print Assumptions test_zesu_pack.

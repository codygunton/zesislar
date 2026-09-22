(* The other half of `RuleSetV1.v`: a module that imports rule set v2.

   Without this module nothing under `ZesuSsz/Proofs/` imports
   `Automation/Sets/v2.v`, so the gate would compile `zesu_run_pass_v2`
   and never run it. Rule set v2 would be correct by construction and
   untested.

   Two things are checked here: that the switch resolves, which is what
   selects the v2 pass, and that a real block proof still closes under
   it. The block is the one in `Tests/Finish.v`, deliberately unchanged,
   so the two modules prove the same lemma under the two rule sets. *)

Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.v2.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
From IslaTraces.write_success_32 Require Import a15048.

Lemma test_rule_set_v2_selected : True.
Proof.
  tryif zesu_rule_set_v2_on then exact I
  else fail "rule set v2 is imported and its switch does not resolve".
Qed.
Print Assumptions test_rule_set_v2_selected.

#[local] Hint Rewrite zesu_bv_sign_extend_same : isla_coq_rewrite.
#[local] Hint Rewrite zesu_bv_unsigned_add_Z_64 using bv_solve
  : isla_coq_rewrite lithium_rewrite.
#[local] Hint Rewrite zesu_bv_unsigned_add_no_wrap_64 using bv_solve
  : isla_coq_rewrite lithium_rewrite.

(* The block `Tests/Finish.v` proves under rule set v1, proved here
   under v2. A v2 step that broke a block would break it here.

   The length premise sits inside `instr_body` rather than in front of
   the lemma, so the proof is `zesu_block` and nothing else: a lemma
   that states `instr_body` and carries a hand line owes a residual
   record, and this one has no debt to record. *)
Lemma test_rule_set_v2_block `{!islaG Sigma} `{!threadG}
    (base : bv 64) (bytes : list (bv 8)) :
  instr 0x15048 (Some a15048) -∗
  instr_body 0x15048 (
    reg_col zesu_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits base ∗
    "x16" ↦ᵣ: (fun _ => True) ∗
    ⌜length bytes = 288%nat⌝ ∗
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
Proof. zesu_block. Qed.
Print Assumptions test_rule_set_v2_block.

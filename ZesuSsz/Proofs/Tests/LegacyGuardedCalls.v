Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma test_legacy_guarded_resource_matching `{!islaG Sigma} `{!threadG}
    (address : Z) (sp ret : bv 64) :
  ⊢ subsume (instr_body address ("x2" ↦ᵣ RVal_Bits sp ∗ True))
    (fun _ : unit => instr_pre address
       ("x2" ↦ᵣ RVal_Bits sp ∗ "x1" ↦ᵣ RVal_Bits ret ∗ True))
    (fun _ => True%I).
Proof.
  zesu_block.
  Unshelve. all: repeat iIntros "?"; zesu_run.
  Unshelve. all: prepare_sidecond; try reflexivity.
  Unshelve. all: try exact tt.
  all: iSplit; [iIntros "(H2 & _)"; iFrame | done].
Qed.

Print Assumptions test_legacy_guarded_resource_matching.

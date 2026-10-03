Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.GuardedMemorySelection.
Lemma disabled_rejects `{!islaG Sigma} `{!threadG} (base : Z) :
 base ↦ₘ? 1896 -∗
 find_in_context (FindMemMapsTo (base+312))
   (fun mk => (⌜mk = MKUninit base 1896⌝)%I).
Proof using All.
 iIntros "Hregion". Fail zesu_guarded_uninit_key. zesu_block.
Qed.

Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.GuardedMemorySelection.
Require Import ZesuSsz.Automation.Switches.BoundedArithmetic.
Require Import ZesuSsz.Automation.Switches.SealedOpen.
Section Tests.
Context `{!islaG Sigma} `{!threadG}.
Lemma complete_region (base : Z) :
 base ↦ₘ? 1896 -∗
 find_in_context (FindMemMapsTo (base + 312))
   (fun mk => (⌜mk = MKUninit base 1896⌝)%I).
Proof using All.
 iIntros "Hregion". zesu_guarded_uninit_key. done.
Qed.
Lemma preserves_prefix_suffix (base source : Z) (bytes : list (bv 8)) :
 (0 <= base)%Z -> (base+1896 < 1073741824)%Z ->
 base ↦ₘ? 1896 -∗ source ↦ₘ∗ bytes -∗
 find_in_context (FindMemMapsTo (base + 312))
   (fun mk => subsume (mem_mapsto_kind_prop (base+312) mk)
     (fun _ : unit => ((base+312) ↦ₘ? 720)%I)
     (fun _ => (base ↦ₘ? 312 ∗ (base+1032) ↦ₘ? 864 ∗ source ↦ₘ∗ bytes)%I)).
Proof using All.
 intros Hmin Hmax. iIntros "Hregion Hsource". zesu_guarded_uninit_key. zesu_block.
Qed.
Lemma noncovering_rejects (base : Z) (bytes : list (bv 8)) :
 base ↦ₘ? 1896 -∗ (base+2000) ↦ₘ∗ bytes -∗
 find_in_context (FindMemMapsTo (base + 2000))
   (fun mk => (⌜mk = MKArray 8 (base+2000) bytes⌝ ∗ base ↦ₘ? 1896)%I).
Proof using All.
 iIntros "Hregion Harray". Fail zesu_guarded_uninit_key. zesu_block.
Qed.
Lemma missing_bound_rejects (base address : Z) (bytes : list (bv 8)) :
 base ↦ₘ? 1896 -∗ address ↦ₘ∗ bytes -∗
 find_in_context (FindMemMapsTo address)
   (fun mk => (⌜mk = MKArray 8 address bytes⌝ ∗ base ↦ₘ? 1896)%I).
Proof using All.
 iIntros "Hregion Harray". Fail zesu_guarded_uninit_key. zesu_block.
Qed.
Lemma unresolved_address_rejects (base : Z) :
 base ↦ₘ? 1896 -∗ ∃ address : Z,
 find_in_context (FindMemMapsTo address)
   (fun mk => (⌜mk = MKUninit base 1896⌝)%I).
Proof using All.
 iIntros "Hregion". iExists (_ : Z). Fail zesu_guarded_uninit_key.
 instantiate (1 := (base+312)%Z). zesu_guarded_uninit_key. done.
Qed.
Lemma near_end_keeps_width_check (base : Z) :
 base ↦ₘ? 1896 -∗
 find_in_context (FindMemMapsTo (base+1895))
   (fun mk => (⌜mk = MKUninit base 1896⌝ ∗ ⌜~ (base+1895+8 <= base+1896)%Z⌝)%I).
Proof using All.
 iIntros "Hregion". zesu_guarded_uninit_key.
 Fail let bogus := constr:(_ : ZesuRegionBounds ((base+1895)+8 <= base+1896)%Z) in idtac.
 iSplit; first done. iPureIntro. lia.
Qed.
End Tests.

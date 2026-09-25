Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.

Lemma transactions_source_authorization_restore_scratch `{!islaG Sigma} (sp : bv 64) :
  (bv_unsigned sp + 1744) ↦ₘ? 144 -∗
  (bv_unsigned sp + 1888) ↦ₘ? 8 -∗
  (bv_unsigned sp + 1744) ↦ₘ? 40 ∗
  (bv_unsigned sp + 1784) ↦ₘ? 112.
Proof.
  iIntros "Hscratch Hlast".
  iDestruct (mem_mapsto_uninit_split 40 with "Hscratch") as
    "[Hfirst Hrest]"; first lia.
  iSplitL "Hfirst"; first iExact "Hfirst".
  iEval (replace (bv_unsigned sp + 1744 + 40) with (bv_unsigned sp + 1784) by lia) in "Hrest".
  iEval (replace (bv_unsigned sp + 1888) with (bv_unsigned sp + 1784 + 104) by lia) in "Hlast".
  iEval (replace (144 - 40) with 104 by lia) in "Hrest".
  iApply (mem_mapsto_uninit_combine 104 (bv_unsigned sp + 1784) (DfracOwn 1) 112 with
    "Hrest Hlast"); lia.
Qed.
Print Assumptions transactions_source_authorization_restore_scratch.

Lemma transactions_source_authorization_restore_registers `{!islaG Sigma} `{!threadG} :
  reg_col [(KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64)] -∗
  reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
    (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] -∗
  reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
    ["x3"; "x4"; "x6"; "x7"; "x16"; "x17"; "x20"; "x21";
     "x23"; "x24"; "x25"; "x26"; "x27"; "x28"; "x29"; "x30"; "x31"]) -∗
  reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
    ["x3"; "x4"; "x6"; "x7"; "x8"; "x9"; "x12"; "x13";
     "x14"; "x15"; "x16"; "x17"; "x20"; "x21";
     "x23"; "x24"; "x25"; "x26"; "x27"; "x28"; "x29"; "x30"; "x31"]).
Proof.
  iIntros "Hfirst Hsecond Hrest".
  iCombine "Hfirst Hsecond Hrest" as "Hall".
  iEval (unfold reg_col; rewrite -!big_sepL_app) in "Hall".
  unfold reg_col.
  iApply (big_sepL_submseteq with "Hall").
  cbn [fmap]. solve_submseteq.
Qed.
Print Assumptions transactions_source_authorization_restore_registers.

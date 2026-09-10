From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_126 Require Import a15a10.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.

Import ListNotations.

Definition writeSuccessEpilogueSavedSlots `{!islaG Sigma}
    (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64) : iProp Sigma :=
  ((bv_unsigned sp + 1992) ↦ₘ ra ∗
   (bv_unsigned sp + 1984) ↦ₘ s0 ∗
   (bv_unsigned sp + 1976) ↦ₘ s1 ∗
   (bv_unsigned sp + 1968) ↦ₘ s2 ∗
   (bv_unsigned sp + 1960) ↦ₘ s3 ∗
   (bv_unsigned sp + 1952) ↦ₘ s4 ∗
   (bv_unsigned sp + 1944) ↦ₘ s5 ∗
   (bv_unsigned sp + 1936) ↦ₘ s6 ∗
   (bv_unsigned sp + 1928) ↦ₘ s7 ∗
   (bv_unsigned sp + 1920) ↦ₘ s8 ∗
   (bv_unsigned sp + 1912) ↦ₘ s9 ∗
   (bv_unsigned sp + 1904) ↦ₘ s10 ∗
   (bv_unsigned sp + 1896) ↦ₘ s11)%I.

Global Instance : LithiumUnfold (@writeSuccessEpilogueSavedSlots) := I.

Definition writeSuccessEpilogueFrame `{!islaG Sigma} `{!threadG}
    (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col writeSuccessOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits (sp + 2000)%bv ∗
   "x8" ↦ᵣ RVal_Bits s0 ∗ "x9" ↦ᵣ RVal_Bits s1 ∗
   "x18" ↦ᵣ RVal_Bits s2 ∗ "x19" ↦ᵣ RVal_Bits s3 ∗
   "x20" ↦ᵣ RVal_Bits s4 ∗ "x21" ↦ᵣ RVal_Bits s5 ∗
   "x22" ↦ᵣ RVal_Bits s6 ∗ "x23" ↦ᵣ RVal_Bits s7 ∗
   "x24" ↦ᵣ RVal_Bits s8 ∗ "x25" ↦ᵣ RVal_Bits s9 ∗
   "x26" ↦ᵣ RVal_Bits s10 ∗ "x27" ↦ᵣ RVal_Bits s11 ∗
   writeSuccessEpilogueSavedSlots sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ∗
   P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessEpilogueFrame) := I.

Definition writeSuccessEpiloguePost `{!islaG Sigma} `{!threadG}
    (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ra ∗
   writeSuccessEpilogueFrame sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P)%I.

Global Instance : LithiumUnfold (@writeSuccessEpiloguePost) := I.

Definition writeSuccessEpilogueSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64),
    reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessOtherRegShapes ∗
    "x1" ↦ᵣ: (fun _ => "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ: (fun _ => "x9" ↦ᵣ: (fun _ =>
    "x18" ↦ᵣ: (fun _ => "x19" ↦ᵣ: (fun _ =>
    "x20" ↦ᵣ: (fun _ => "x21" ↦ᵣ: (fun _ =>
    "x22" ↦ᵣ: (fun _ => "x23" ↦ᵣ: (fun _ =>
    "x24" ↦ᵣ: (fun _ => "x25" ↦ᵣ: (fun _ =>
    "x26" ↦ᵣ: (fun _ => "x27" ↦ᵣ: (fun _ =>
    writeSuccessEpilogueSavedSlots sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp + 1896⌝ ∗
    ⌜bv_unsigned sp + 2000 < 0x40000000⌝ ∗
    ⌜bv_extract 0 1 ra = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ra = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ra = BV 2 0⌝ ∗
    P ∗ instr_pre
      (bv_unsigned (bv_or (bv_and (ra + 0)%bv (BV 64 18446744073709551614)) (BV 64 0)))
      (writeSuccessEpiloguePost sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P) ∗
    True))))))))))))))%I.

Global Instance : LithiumUnfold (@writeSuccessEpilogueSpec) := I.

Lemma write_success_return_instruction :
  is_Some (IslaTraces.write_success_blocks.Index.lookup 0x15a10).
Proof. vm_compute. eauto. Qed.

Definition writeSuccessReturnSpec `{!islaG Sigma} `{!threadG}
    (ra : bv 64) (Q : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ra ∗ Q ∗
   ⌜bv_extract 0 2 ra = BV 2 0⌝ ∗
   instr_pre
     (bv_unsigned (bv_or (bv_and (ra + 0)%bv (BV 64 18446744073709551614)) (BV 64 0)))
     (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ra ∗ Q ∗ True) ∗
   True)%I.

Global Instance : LithiumUnfold (@writeSuccessReturnSpec) := I.

Lemma instr_pre_weaken `{!islaG Sigma} `{!threadG} (address : Z)
    (P Q : iProp Sigma) :
  (Q -∗ P) -∗ instr_pre address P -∗ instr_pre address Q.
Proof.
  iIntros "Hwand Hpre".
  iApply (instr_pre_wand with "Hpre Hwand"); [done|reflexivity].
Qed.

Definition writeSuccessReturnAnySpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (ra : bv 64) (Q : iProp Sigma), writeSuccessReturnSpec ra Q)%I.

Global Instance : LithiumUnfold (@writeSuccessReturnAnySpec) := I.

Lemma write_success_return_any_block `{!islaG Sigma} `{!threadG} :
  instr 0x15a10 (Some IslaTraces.write_success_126.a15a10.a15a10) -∗
  instr_body 0x15a10 writeSuccessReturnAnySpec.
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite bv_sign_extend_64_idemp.
  all: bv_solve.
Qed.

Lemma write_success_epilogue_block `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x159d8 (writeSuccessEpilogueSpec P).
Proof.
  move => *.
  iStartProof. iIntros "_ #Hcode".
  iPoseProof "Hcode" as "#HrawLookup".
  iEval (rewrite /instr_lookup_resources) in "HrawLookup".
  iPoseProof ("HrawLookup" $! 0x15a10 with "[]") as "#HreturnCode".
  { iPureIntro. exact write_success_return_instruction. }
  iAssert (instr_body 0x15a10 writeSuccessReturnAnySpec)%I
    with "[HreturnCode]" as "#Hreturn".
  { iApply write_success_return_any_block. iExact "HreturnCode". }
  liARun.
  Unshelve.
  all: try iExists
    (writeSuccessEpilogueFrame sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P,
     ra, tt)ₗ.
  all: try cbn.
  all: try unLET.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite bv_sign_extend_64_idemp.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  have HspAdd (offset : Z) (Hoffset : (0 <= offset <= 2000)%Z) :
      bv_unsigned (sp + Z_to_bv 64 offset)%bv =
        (bv_unsigned sp + offset)%Z.
  { pose proof (bv_unsigned_in_range 64 sp).
    rewrite bv_add_unsigned bv_unsigned_BV.
    rewrite (bv_wrap_small 64 offset);
      [|change (0 <= offset < 18446744073709551616)%Z; lia].
    rewrite (bv_wrap_small 64 (bv_unsigned sp + offset)); [reflexivity|].
    change (0 <= bv_unsigned sp + offset < 18446744073709551616)%Z.
    lia. }
  rewrite !bv_sign_extend_64_idemp.
  rewrite (HspAdd 1992 ltac:(lia)) (HspAdd 1984 ltac:(lia))
    (HspAdd 1976 ltac:(lia)) (HspAdd 1968 ltac:(lia))
    (HspAdd 1960 ltac:(lia)) (HspAdd 1952 ltac:(lia))
    (HspAdd 1944 ltac:(lia)) (HspAdd 1936 ltac:(lia))
    (HspAdd 1928 ltac:(lia)) (HspAdd 1920 ltac:(lia))
    (HspAdd 1912 ltac:(lia)) (HspAdd 1904 ltac:(lia))
    (HspAdd 1896 ltac:(lia)).
  iEval (unfold writeSuccessReturnSpec, writeSuccessEpilogueFrame,
    writeSuccessEpilogueSavedSlots, reg_col).
  iEval (rewrite /zesu_ram_sys_regs /writeSuccessOtherRegShapes
    /writeSuccessOtherRegisters /=).
  iFrame.
  iSplit; [iPureIntro; exact H5|].
  iRename select
    (instr_pre
      (bv_unsigned (bv_or (bv_and (ra + 0)%bv (BV 64 18446744073709551614))
        (BV 64 0)))
      (writeSuccessEpiloguePost sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P))%I
    into "Hterminal".
  iSplit; [|done].
  iApply (instr_pre_weaken
    (bv_unsigned (bv_or (bv_and (ra + 0)%bv (BV 64 18446744073709551614))
      (BV 64 0)))
    (writeSuccessEpiloguePost sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P)
    (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ra ∗
      writeSuccessEpilogueFrame sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P ∗
      True)
    with "[] Hterminal").
  iIntros "(Hsys & Hx1 & Hframe & _)".
  iEval (unfold writeSuccessEpiloguePost). iFrame.
Qed.

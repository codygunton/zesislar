Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.

Lemma write_success_hashes_loop_pre_frame
    `{!islaG Sigma} `{!threadG} (F P : iProp Sigma) :
  □ instr_pre 0x15754 (writeSuccessHashesLoopSpec P) -∗
  □ instr_pre 0x15754 (writeSuccessHashesLoopSpec (F ∗ P)).
Proof.
  iIntros "#Hloop". iModIntro.
  iApply (instr_pre_wand 0x15754 0x15754 true true with "Hloop");
    [done | reflexivity |].
  iIntros "Hstate".
  iEval (rewrite /writeSuccessHashesLoopSpec) in "Hstate".
  iDestruct "Hstate" as
    (sp pointer base total processed remaining bytes tail)
    "(Hsys & Hregs & H2 & H8 & H9 & Hbytes & Hscratch & Hmmio & Htrace &
      HFP & Hinvariant & Hexit & _)".
  iDestruct "HFP" as "(HF & HP)".
  iAssert (instr_pre 0x158e0
      (writeSuccessHashesLoopExit sp base total bytes tail P))%I
    with "[Hexit HF]" as "HexitP".
  { iApply (instr_pre_wand 0x158e0 0x158e0 true true with "Hexit");
      [done | reflexivity |].
    iIntros "HexitP".
    rewrite /writeSuccessHashesLoopExit.
    iDestruct "HexitP" as (exitPointer)
      "(HsysExit & HregsExit & H2Exit & H8Exit & H9Exit & HbytesExit &
        HscratchExit & HmmioExit & HtraceExit & HP & %Hpointer & _)".
    iExists exitPointer.
    iFrame "HsysExit HregsExit H2Exit H8Exit H9Exit HbytesExit HscratchExit
      HmmioExit HtraceExit HF HP".
    iPureIntro. split; [exact Hpointer | done]. }
  rewrite /writeSuccessHashesLoopSpec.
  iExists sp, pointer, base, total, processed, remaining, bytes, tail.
  iFrame "Hsys Hregs H2 H8 H9 Hbytes Hscratch Hmmio Htrace HP Hinvariant
    HexitP".
Qed.

Lemma write_success_hashes_loop_exit_frame
    `{!islaG Sigma} `{!threadG} (F P : iProp Sigma)
    (sp : bv 64) (base : Z) (total : nat) (bytes : list (bv 8))
    (tail : spec) :
  instr_pre 0x158e0
    (writeSuccessHashesLoopExit sp base total bytes tail P) -∗
  instr_pre 0x158e0
    (writeSuccessHashesLoopExit sp base total bytes tail (F ∗ P)).
Proof.
  iIntros "Hexit".
  iApply (instr_pre_wand 0x158e0 0x158e0 true true with "Hexit");
    [done | reflexivity |].
  iIntros "HexitFP".
  rewrite /writeSuccessHashesLoopExit.
  iDestruct "HexitFP" as (pointer)
    "(Hsys & Hregs & H2 & H8 & H9 & Hbytes & Hscratch & Hmmio & Htrace &
      HFP & %Hpointer & _)".
  iDestruct "HFP" as "(_ & HP)".
  iExists pointer.
  iFrame "Hsys Hregs H2 H8 H9 Hbytes Hscratch Hmmio Htrace HP".
  iPureIntro. split; [exact Hpointer | done].
Qed.

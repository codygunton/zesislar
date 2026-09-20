Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawLoadSpec.
Open Scope Z_scope.

Lemma exact_tail_raw_load `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (transactionCount : nat)
    (tail : spec) (P : iProp Sigma)
    (Hvalues : length values = 74%nat)
    (Halign : bv_unsigned sp `mod` 16 = 0)
    (Hlower : mapRamBase defaultMap <= bv_unsigned sp)
    (Hupper : bv_unsigned sp + 1896 < machineRamEnd defaultMap) :
  WriteSuccessNativeCode.writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15674 (exactTailRawLoadExit sp values tail P) -∗
  instr_body 0x15668 (exactTailRawLoadEntry sp values transactionCount tail P).
Proof.
  have HprefixLength : length (take 69 values) = 69%nat.
  { rewrite length_take Hvalues. reflexivity. }
  iIntros "#Hnative #Hnext".
  iEval (unfold WriteSuccessNativeCode.writeSuccessCompleteNativeCode) in "Hnative".
  iDestruct "Hnative" as "#(H00 & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & Hlists & Hbytes & Hint & Hu256 & Hu128)".
  iClear "H00 Houtput Hmemcpy Hboolean Hoptional Hlists Hbytes Hint Hu256 Hu128".
  iStartProof; simpl.
  repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"].
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_run_until ltac:(fun _ => lazymatch goal with
    | |- iris.proofmode.environments.envs_entails _
        (find_in_context (FindMemMapsTo _) _) => idtac
    end).
  zesu_finish. zesu_finish. liAStep.
  zesu_run_until ltac:(fun _ => lazymatch goal with
    | |- iris.proofmode.environments.envs_entails _
        (find_in_context (FindMemMapsTo _) _) => idtac
    end).
  zesu_finish. zesu_finish. liAStep.
  zesu_run_until ltac:(fun _ => lazymatch goal with
    | |- iris.proofmode.environments.envs_entails _
        (instr_pre 0x15674 _) => idtac
    end).
  Unshelve. all: try zesu_finish.
  - have Hindex9 : Z.to_nat
      ((bv_unsigned sp + 1104 - (bv_unsigned sp + 1032)) `div` 8) = 9%nat by lia.
    match goal with H : (take 69 values !! Z.to_nat
        ((bv_unsigned sp + 1104 - (bv_unsigned sp + 1032)) `div` 8) = Some _) |- _ =>
      rename H into HvalueWord9 end.
    rewrite Hindex9 in HvalueWord9. rewrite lookup_take in HvalueWord9; last lia.
    unfold WriteSuccessValueSpec.writeSuccessValueWord. rewrite HvalueWord9. reflexivity.
  - have Hindex10 : Z.to_nat
      ((bv_unsigned sp + 1112 - (bv_unsigned sp + 1032)) `div` 8) = 10%nat by lia.
    match goal with H : (take 69 values !! Z.to_nat
        ((bv_unsigned sp + 1112 - (bv_unsigned sp + 1032)) `div` 8) = Some _) |- _ =>
      rename H into HvalueWord10 end.
    rewrite Hindex10 in HvalueWord10. rewrite lookup_take in HvalueWord10; last lia.
    unfold WriteSuccessValueSpec.writeSuccessValueWord. rewrite HvalueWord10. reflexivity.
Qed.
Print Assumptions exact_tail_raw_load.

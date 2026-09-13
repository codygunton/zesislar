Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.

Fixpoint writeSuccessExactBlobHashesEvents (sp : bv 64)
    (processed count : nat) (bytes : list (bv 8)) (tail : spec) : spec :=
  match count with
  | O => tail
  | S remaining =>
      writeOutputEvents (sp + BV 64 1680)%bv (BV 64 32)
        (take 32 (drop (32 * processed) bytes))
        (writeSuccessExactBlobHashesEvents sp (S processed) remaining bytes tail)
  end.

Lemma writeSuccessExactBlobHashesEvents_zero sp processed bytes tail :
  writeSuccessExactBlobHashesEvents sp processed 0 bytes tail = tail.
Proof. reflexivity. Qed.
Print Assumptions writeSuccessExactBlobHashesEvents_zero.

Lemma writeSuccessExactBlobHashesEvents_cons sp processed count bytes tail :
  writeSuccessExactBlobHashesEvents sp processed (S count) bytes tail =
  writeOutputEvents (sp + BV 64 1680)%bv (BV 64 32)
    (take 32 (drop (32 * processed) bytes))
    (writeSuccessExactBlobHashesEvents sp (S processed) count bytes tail).
Proof. reflexivity. Qed.
Print Assumptions writeSuccessExactBlobHashesEvents_cons.

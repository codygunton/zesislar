Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Definition accessExactLoopFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (entries : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (tail : spec) (x19 savedX22 : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (instr_pre 0x153c0 (writeSuccessAccessListsLoopExit sp base entries bytes tail x19 savedX22 P) ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@accessExactLoopFrame) := I.

Definition writeSuccessExactAccessListsLoopSpec `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (entries processed remaining : list writeSuccessAccessEntry)
     (bytes : list (bv 8)) (storedIndex savedX22 data pointer count : bv 64) (tail : spec),
   writeSuccessExactAccessListsState sp base entries processed remaining bytes storedIndex
     x19 savedX22 data pointer count tail
     (accessExactLoopFrame sp base entries bytes tail x19 savedX22 P))%I.
Global Instance : LithiumUnfold (@writeSuccessExactAccessListsLoopSpec) := I.

Lemma access_loop_state_resources `{!islaG Sigma} `{!threadG}
    sp base entries processed remaining bytes storedIndex x19 savedX22 data pointer count tail
    (P : iProp Sigma) :
  writeSuccessExactAccessListsState sp base entries processed remaining bytes storedIndex
    x19 savedX22 data pointer count tail
    (accessExactLoopFrame sp base entries bytes tail x19 savedX22 P) -∗
  writeSuccessExactAccessListsLoopSpec x19 P.
Proof.
  iIntros "Hstate".
  iExists sp, base, entries, processed, remaining, bytes, storedIndex, savedX22, data, pointer, count, tail.
  iExact "Hstate".
Qed.
Print Assumptions access_loop_state_resources.

Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsLoopSpec WriteSuccessExactAuthorizationsArray.

Lemma authorization_facts_layout sp pointer base rows prefix row rest source :
  authorizationLoopFacts sp pointer base rows prefix row rest source ->
  Forall (fun bytes => length bytes = 144%nat) prefix /\ length row = 144%nat /\
  take 144 (drop (144 * length prefix) source) = row /\
  length source = (144 * (length prefix + S (length rest)))%nat.
Proof.
  intros (Hrows & Hall & Hsource & Hposition & Hcount & Halign & Hlow & Hhigh & Hbase & Hend).
  rewrite Hrows Forall_app in Hall. destruct Hall as [Hprefix Hremaining].
  inversion Hremaining as [|? ? Hrow Hrest].
  have HprefixLength : length (concat prefix) = (144 * length prefix)%nat.
  { clear -Hprefix. induction Hprefix as [|bytes prefix Hbytes Hprefix IH]; cbn; [reflexivity|].
    rewrite app_length IH Hbytes. lia. }
  have HrestLength : length (concat rest) = (144 * length rest)%nat.
  { clear -Hrest. induction Hrest as [|bytes rest Hbytes Hrest IH]; cbn; [reflexivity|].
    rewrite app_length IH Hbytes. lia. }
  repeat split; try assumption.
  - rewrite Hsource Hrows. apply authorization_row_slice; assumption.
  - rewrite Hsource Hrows concat_app app_length /= app_length HprefixLength HrestLength Hrow. lia.
Qed.
Print Assumptions authorization_facts_layout.

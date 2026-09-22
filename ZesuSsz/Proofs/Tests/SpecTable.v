Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SpecTable.
Require Import InstrSpecs.Lookup.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.

(* The table resolves by computation, and only for an address it holds.
   0x15668 is the post-transactions entry, which the table specifies. *)
Lemma test_spec_table_resolves `{!islaG Sigma} `{!threadG} :
  exists body : iProp Sigma, ZesuSpecAt 0x15668 body.
Proof. eexists. unfold ZesuSpecAt. reflexivity. Qed.
Print Assumptions test_spec_table_resolves.

(* An address the table does not hold resolves to nothing, so the search
   falls through to the raw instruction as it did before. *)
Lemma test_spec_table_absent `{!islaG Sigma} `{!threadG} :
  Index.body_lookup 0x10190 = None.
Proof. reflexivity. Qed.
Print Assumptions test_spec_table_absent.

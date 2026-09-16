Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesLoopSpec.

Lemma suffix_facts_advance sp pointer base total processed remaining source :
  suffixLoopFacts sp pointer base total processed (S remaining) source ->
  suffixLoopFacts sp (pointer + BV 64 32)%bv base total (S processed) remaining source.
Proof.
  intros (Hlength & Htotal & Hcursor & Hcount & Halign & Hlow & Hhigh & Hbase & Hend).
  have HcursorNext : bv_unsigned (pointer + BV 64 32)%bv = (base + 32 * Z.of_nat (S processed))%Z.
  { have HlenZ : Z.of_nat (length source) = 32 * Z.of_nat total by rewrite Hlength Nat2Z.inj_mul; reflexivity.
    have HtotalZ : Z.of_nat total = Z.of_nat processed + (1 + (1 + Z.of_nat remaining)).
    { rewrite -Htotal Nat2Z.inj_add !Nat2Z.inj_succ. lia. }
    rewrite Nat2Z.inj_succ. clear -Hcursor Hbase Hend HlenZ HtotalZ. bv_solve. }
  unfold suffixLoopFacts. repeat split; try assumption; lia.
Qed.
Print Assumptions suffix_facts_advance.

Lemma suffix_facts_end_pointer sp pointer base total processed source :
  suffixLoopFacts sp pointer base total processed 0 source ->
  (pointer + BV 64 32)%bv = Z_to_bv 64 (base + Z.of_nat (length source)).
Proof.
  intros (Hlength & Htotal & Hcursor & Hcount & Halign & Hlow & Hhigh & Hbase & Hend).
  have HlenZ : Z.of_nat (length source) = (32 * (Z.of_nat processed + 1))%Z.
  { rewrite Hlength -Htotal Nat2Z.inj_mul Nat2Z.inj_add. cbn. lia. }
  clear -Hcursor HlenZ. bv_solve.
Qed.
Print Assumptions suffix_facts_end_pointer.

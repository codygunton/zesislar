Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
Open Scope Z_scope.
Lemma decodeItemShortListMaskFacts (register : bv 64) (prefix : byte) :
  192 <= bv_unsigned prefix <= 247 ->
  bv_unsigned register = bv_unsigned prefix ->
  bv_unsigned (bv_and (register + 64) 255) = bv_unsigned prefix - 192.
Proof.
  intros Hclass Hregister.
  pose proof (zesu_unsigned_low_mask_add_integer 64 8 register 255 64
    ltac:(done) ltac:(reflexivity)) as Hlow.
  rewrite Hlow Hregister Z_to_bv_unsigned.
  change ((bv_unsigned prefix + 64) mod 256 = bv_unsigned prefix - 192).
  replace (bv_unsigned prefix + 64) with
    ((bv_unsigned prefix - 192) + 1 * 256) by ring.
  rewrite Z.mod_add; [apply Z.mod_small; lia | lia].
Qed.

#[export] Hint Extern 1
  (SimplAnd (bv_unsigned (bv_and (?register + 64) 255) =
    bv_unsigned ?prefix - 192) True) =>
  unfold SimplAnd; split;
  [ intros _; eapply decodeItemShortListMaskFacts;
    solve [eassumption | split; assumption]
  | intros _; exact I ] : typeclass_instances.


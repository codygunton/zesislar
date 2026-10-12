Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.

Lemma maskedReturnUmbrella (ret : bv 64)
    (Haligned : bv_extract 0 1 ret = BV 1 0) :
  bv_unsigned (bv_or (bv_and ret (BV 64 18446744073709551614)) (BV 64 0)) =
    bv_unsigned ret.
Proof. zesu_saturate_derived_facts. assumption. Qed.

Lemma maskedReturnWitnessConsumer (ret : bv 64)
    (Haligned : bv_extract 0 1 ret = BV 1 0) :
  bv_unsigned (bv_or (bv_and ret (BV 64 18446744073709551614)) (BV 64 0)) =
    bv_unsigned ret.
Proof. zesu_witness_facts. assumption. Qed.

Lemma maskedReturnMissingAlignment (ret : bv 64) : True.
Proof.
  assert_fails (assert (Hwrong : ZesuDerivedFacts
    (bv_extract 0 1 ret = BV 1 1)
    (bv_unsigned (bv_or (bv_and ret (BV 64 18446744073709551614)) (BV 64 0)) =
      bv_unsigned ret)) by solve [typeclasses eauto]).
  exact I.
Qed.

Lemma maskedReturnOddControl :
  bv_unsigned (bv_or (bv_and (BV 64 1) (BV 64 18446744073709551614)) (BV 64 0)) <> 1.
Proof. vm_compute. discriminate. Qed.

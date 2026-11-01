Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.HypothesisCast.
From Coq Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions.
Open Scope Z_scope.
Lemma hypothesis_cast_symbolic_source388 (source : N) (word : bv source) : True.
Proof.
  Fail assert (Hrange : 0 <= bv_unsigned word < bv_modulus 64) by
    (HypothesisCast.zesu_hypothesis_cast_range 64 (bv_unsigned word)).
  exact I.
Qed.
Print Assumptions hypothesis_cast_symbolic_source388.
Lemma hypothesis_cast_control388_guarded (value limit : Z)
  (Hrange : 0 <= value < 2^32)
  (Hcast : bv_unsigned (Z_to_bv 32 value) < limit) : value < limit.
Proof.
  assert (Hen : HypothesisCast.ZesuStepHypothesisCast) by constructor.
  HypothesisCast.zesu_hypothesis_cast_finish.
Qed.
Print Assumptions hypothesis_cast_control388_guarded.

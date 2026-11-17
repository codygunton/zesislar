Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Automation2.Hooks.
From stdpp Require Import bitvector.definitions bitvector.tactics.
From Coq Require Import ZArith.ZArith Lia.
Local Open Scope Z_scope.

(* Pure evidence transport only. No search, address, or contract is encoded. *)
Ltac zesu_unsigned_branch_evidence :=
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation2.BitvectorFacts.ZesuStepBranchGuards);
  lazymatch goal with
  | |- ?target =>
      assert_fails (has_evar target);
      ZesuSsz.Automation2.Hooks.zesu_region_arithmetic_statement target;
      match goal with
      | Hbranch : context [bv_signed (bv_zero_extend 128 _)] |- _ =>
          let view := fresh "HunsignedBranch" in
          pose proof Hbranch as view;
          progress (rewrite !ZesuSsz.Automation2.BitvectorFacts.zesu_signed_zero_extend_64_128 in view);
          first [exact view | solve [lia] | solve [bv_solve]]
      end
  end.

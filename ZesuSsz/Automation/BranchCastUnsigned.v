Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.Hooks.
From stdpp Require Import bitvector.definitions bitvector.tactics.
From Coq Require Import ZArith.ZArith Lia.
Local Open Scope Z_scope.

(* Pure evidence transport only. No search, address, or contract is encoded. *)
Ltac zesu_unsigned_branch_cast_evidence :=
  ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled constr:(ZesuSsz.Automation.BitvectorFacts.ZesuStepBranchGuards);
  lazymatch goal with
  | |- ?target =>
      assert_fails (has_evar target);
      ZesuSsz.Automation.Hooks.zesu_region_arithmetic_statement target;
      match goal with
      | Hbranch : context [bv_signed (bv_zero_extend 128 _)] |- _ =>
          let view := fresh "HunsignedBranch" in
          pose proof Hbranch as view;
          progress (rewrite !ZesuSsz.Automation.BitvectorFacts.zesu_signed_zero_extend_64_128 in view);
          repeat match type of view with
          | context [bv_unsigned (Z_to_bv ?width ?value)] =>
              let range := fresh "HcastRange" in
              assert (range : 0 <= value < bv_modulus width) by
                (unfold bv_modulus; cbn; lia);
              rewrite (Z_to_bv_small width value range) in view
          end;
          first [exact view | solve [lia] | solve [bv_solve]]
      end
  end.

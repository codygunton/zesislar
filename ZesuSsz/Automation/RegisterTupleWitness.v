Require Import ZesuSsz.Automation.CallSet.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.

(* Resolve tuple components from their exact resource or captured shape. *)
Ltac zesu_resolve_tuple_register opened :=
  multimatch opened with
  | context[(@reg_mapsto _ _ _ ?register ?fraction (RVal_Bits ?bits))] =>
      has_evar bits;
      iMatchHyp ltac:(fun H resource =>
        lazymatch resource with
        | @reg_mapsto _ _ _ ?owned_register ?owned_fraction (RVal_Bits ?owned_bits) =>
          constr_eq register owned_register;
          assert_fails (has_evar owned_bits);
          unify bits owned_bits
        end)
  | context[?value = RVal_Bits ?bits] =>
      has_evar bits;
      assert_fails (has_evar value);
      match goal with
      | Heq : value = RVal_Bits ?owned_bits |- _ =>
          assert_fails (has_evar owned_bits); unify bits owned_bits
      end
  end.

(* Derive fresh bitvectors before the tuple evars fix their context. *)
Ltac zesu_prepare_tuple_shape body :=
  multimatch body with
  | context[?value = RVal_Bits ?bits] =>
      assert_fails (has_evar value);
      first [is_var value | fail 1];
      let width := lazymatch bits with @bv_to_bvn ?n _ => n end in
      tryif (match goal with Heq : value = RVal_Bits _ |- _ => idtac end) then fail else idtac;
      let Hshape := fresh "HtupleShape" in
      first [assert (Hshape : valu_has_shape value (BitsShape width)) by assumption |
        repeat iDestruct select (⌜_⌝)%I as %?;
        assert (Hshape : valu_has_shape value (BitsShape width)) by assumption];
      let owned_bits := fresh "tupleBits" in
      let Heq := fresh "HtupleBits" in
      destruct (valu_has_bits_shape value width Hshape) as [owned_bits Heq]
  end.

Ltac zesu_resolve_register_tuple witness opened :=
  tryif has_evar witness then
    (zesu_resolve_tuple_register opened; zesu_resolve_register_tuple witness opened)
  else idtac.

(* A closed probe exposes projections without creating orphan goals. *)
Ltac zesu_register_tuple_probe T :=
 lazymatch T with
 | li_prod (bv ?width) ?rest =>
   let tail := zesu_register_tuple_probe rest in
   constr:(li_pair (BV width 0) tail)
 | unit => constr:(tt)
 end.

Ltac zesu_register_tuple_witness :=
  zesu_call_set_on;
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T ?body) =>
      let probe := zesu_register_tuple_probe T in
      let probed := eval cbv beta iota delta [li_fst li_snd] in (body probe) in
      repeat zesu_prepare_tuple_shape probed;
      let witness := zesu_tuple_witness T in
      let opened := eval cbv beta iota delta [li_fst li_snd] in (body witness) in
      zesu_resolve_register_tuple witness opened;
      assert_fails (has_evar witness);
      iExists witness
  end.

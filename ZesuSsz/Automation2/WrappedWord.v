Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.PureFacts.
Require Import ZesuSsz.Automation2.VmClosed.
Local Open Scope Z_scope.

(* Wrapped-word helpers. The versioned proof profile controls their activation. *)
Ltac zesu_wrapped_word_range arithmetic :=
  rewrite !bv_add_unsigned !Z_to_bv_unsigned ;
  repeat rewrite bv_unsigned_BV;
  repeat rewrite bv_wrap_add_idemp_l;
  repeat (rewrite <- Z.add_assoc; rewrite bv_wrap_add_idemp_l);
  lazymatch goal with
  | |- context [bv_wrap ?width (?base + ?offset)] =>
    let adjusted := constr:(offset - bv_modulus width) in
    let Hrange := fresh "HwrappedRange" in
    assert (Hrange : 0 <= base + adjusted < bv_modulus width) by arithmetic;
    let Hword := fresh "HwrappedWord" in
    assert (Hword : bv_wrap width (base + offset) = base + adjusted) by
      (replace (base + offset) with (base + adjusted + bv_modulus width) by ring;
       rewrite bv_wrap_add_modulus_1; apply bv_wrap_small; exact Hrange);
    rewrite Hword
  end;
  cbv [bv_unsigned Z_to_bv bv_wrap bv_modulus];
  arithmetic.

Ltac zesu_reduce_closed_Z_aliases :=
  repeat match goal with
  | Hconstant : context [?scalar] |- _ =>
    let scalar_type := type of scalar in
    constr_eq scalar_type Z;
    is_closed_term scalar;
    let head := get_head scalar in
    constr_eq head scalar;
    assert_fails (is_var scalar);
    let reduced := eval cbv delta [scalar] in scalar in
    progress change scalar with reduced in *
  end.


Lemma zesu_wrapped_add_unsigned_small (width : N) (base : Z) (left right : bv width) :
  0 <= base + (bv_unsigned left + bv_unsigned right - bv_modulus width) < bv_modulus width ->
  bv_unsigned (Z_to_bv width base + left + right) =
    base + (bv_unsigned left + bv_unsigned right - bv_modulus width).
Proof.
  intros Hrange.
  rewrite !bv_add_unsigned Z_to_bv_unsigned.
  rewrite bv_wrap_add_idemp_l.
  rewrite <- Z.add_assoc, bv_wrap_add_idemp_l, Z.add_assoc.
  replace (base + bv_unsigned left + bv_unsigned right) with
    (base + (bv_unsigned left + bv_unsigned right - bv_modulus width) + bv_modulus width) by ring.
  rewrite bv_wrap_add_modulus_1.
  apply bv_wrap_small. exact Hrange.
Qed.

Lemma zesu_wrapped_offset_base (width : N) (base : Z) :
  bv_unsigned (Z_to_bv width base) = bv_wrap width (base + 0).
Proof. rewrite Z_to_bv_unsigned Z.add_0_r. reflexivity. Qed.

Lemma zesu_wrapped_offset_step (width : N) (base sum : Z) (word step : bv width) :
  bv_unsigned word = bv_wrap width (base + sum) ->
  bv_unsigned (bv_add word step) = bv_wrap width (base + (sum + bv_unsigned step)).
Proof.
  intros Hword. rewrite bv_add_unsigned Hword bv_wrap_add_idemp_l Z.add_assoc.
  reflexivity.
Qed.

Lemma zesu_wrapped_offset_small (width : N) (base sum offset address : Z) (word : bv width) :
  bv_unsigned word = bv_wrap width (base + sum) ->
  bv_swrap width sum = offset ->
  address = base + offset ->
  0 <= address < bv_modulus width ->
  bv_unsigned word = address.
Proof.
  intros Hword Hoffset Haddress Hrange. rewrite Hword. subst offset address.
  pose proof (bv_modulus_pos width) as Hpos.
  unfold bv_swrap, bv_wrap in *.
  set (shifted := sum + bv_half_modulus width).
  replace (base + sum) with
    (base + (shifted mod bv_modulus width - bv_half_modulus width) +
      (shifted / bv_modulus width) * bv_modulus width)
    by (pose proof (Z.div_mod shifted (bv_modulus width)); subst shifted; lia).
  rewrite Z_mod_plus_full. apply Z.mod_small. exact Hrange.
Qed.

(* A proof of [bv_unsigned word = bv_wrap width (base + sum)] for additions
   on one integer cast. *)
Ltac zesu_wrapped_offset_chain word :=
  lazymatch word with
  | Z_to_bv ?width ?base => constr:(zesu_wrapped_offset_base width base)
  | bv_add ?inner ?step =>
      let proof := zesu_wrapped_offset_chain inner in
      constr:(zesu_wrapped_offset_step _ _ _ inner step proof)
  end.

(* Two or more additions on one integer cast, every offset closed. *)
Ltac zesu_wrapped_closed_chain word :=
  lazymatch word with
  | bv_add (bv_add _ _) _ =>
      let chain := zesu_wrapped_offset_chain word in
      lazymatch type of chain with
      | bv_unsigned _ = bv_wrap ?width (_ + ?sum) =>
          zesu_vm_closed width; zesu_vm_closed sum
      end
  end.

(* Reduce the closed offsets to one signed literal: the address becomes
   [base - k], [base] or [base + k]. The caller checks the chain with
   [zesu_wrapped_closed_chain] before this VM evaluation. *)
Ltac zesu_wrapped_closed_offset word arithmetic :=
  let chain := zesu_wrapped_offset_chain word in
  lazymatch type of chain with
  | bv_unsigned _ = bv_wrap ?width (?base + ?sum) =>
      let offset := zesu_vm_eval_closed (bv_swrap width sum) in
      let address := lazymatch eval vm_compute in (Z.compare offset 0) with
        | Lt => let magnitude := eval vm_compute in (Z.opp offset) in constr:(base - magnitude)
        | Eq => constr:(base)
        | Gt => constr:(base + offset)
        end in
      let Heq := fresh "HwrappedAddress" in
      assert (Heq : bv_unsigned word = address) by
        (refine (zesu_wrapped_offset_small width base sum offset address word chain _ _ _);
         [vm_compute; reflexivity | ring | arithmetic]);
      rewrite Heq; clear Heq
  end.

Ltac zesu_normalize_wrapped_findmem arithmetic :=
  lazymatch goal with
  | |- iris.proofmode.environments.envs_entails _ (find_in_context (FindMemMapsTo (bv_unsigned ?word)) _) =>
    lazymatch word with
    | bv_add (bv_add (Z_to_bv ?width ?base) ?left) ?right =>
      let Heq := fresh "HwrappedAddress" in
      assert (Heq : bv_unsigned word =
        base + (bv_unsigned left + bv_unsigned right - bv_modulus width)) by
        (apply zesu_wrapped_add_unsigned_small; arithmetic);
      rewrite Heq; clear Heq
    end
  end.

(* Rewrite a lookup address with two or more closed offsets on one integer
   cast to its reduced form. The run loops try this only after every other
   route refused the lookup, then retry the lookup once (s0-relative stores
   with three offsets, and two-offset forms no other rule takes). The range
   side condition uses the facts of [zesu_wrapped_memory_lookup]. *)
Ltac zesu_wrapped_closed_address_step :=
  lazymatch goal with
  | |- iris.proofmode.environments.envs_entails _
      (find_in_context (FindMemMapsTo (bv_unsigned ?word)) _) =>
      first [zesu_wrapped_closed_chain word |
        (* A local definition whose body is a closed chain: unfold that
           binder in the goal only. *)
        is_var word;
        let body := eval cbv delta [word] in word in
        zesu_wrapped_closed_chain body; change word with body]
  end;
  ZesuSsz.Automation2.PureFacts.zesu_saturate_derived_facts;
  repeat first [progress ZesuSsz.Automation2.PureFacts.zesu_split_folded_pure |
    match goal with Hpair : _ /\ _ |- _ => destruct Hpair end];
  zesu_reduce_closed_Z_aliases;
  lazymatch goal with
  | |- iris.proofmode.environments.envs_entails _
      (find_in_context (FindMemMapsTo (bv_unsigned ?word)) _) =>
      zesu_wrapped_closed_offset word ltac:(
        zesu_reduce_closed_Z_aliases; cbv [bv_unsigned bv_modulus] in *; lia)
  end.

(* Reduce every closed-chain `bv_unsigned` in a pure goal, such as the array
   bound `Z.to_nat (addr - base) + k <= length L` of a load or store whose
   address was not reduced at its lookup. *)
Ltac zesu_wrapped_closed_terms :=
  repeat match goal with
  | |- context [bv_unsigned ?word] =>
      zesu_wrapped_closed_chain word;
      zesu_wrapped_closed_offset word ltac:(
        ZesuSsz.Automation2.PureFacts.zesu_saturate_derived_facts;
        repeat first [progress ZesuSsz.Automation2.PureFacts.zesu_split_folded_pure |
          match goal with Hpair : _ /\ _ |- _ => destruct Hpair end];
        zesu_reduce_closed_Z_aliases; cbv [bv_unsigned bv_modulus] in *; lia)
  end.

Ltac zesu_wrapped_memory_lookup :=
  lazymatch goal with
  | |- iris.proofmode.environments.envs_entails _
      (find_in_context (FindMemMapsTo (bv_unsigned ?word)) _) =>
    lazymatch word with
    | bv_add (bv_add (Z_to_bv _ _) _) _ => idtac
    end
  end;
  ZesuSsz.Automation2.PureFacts.zesu_saturate_derived_facts;
  repeat first [progress ZesuSsz.Automation2.PureFacts.zesu_split_folded_pure |
    match goal with Hpair : _ /\ _ |- _ => destruct Hpair end];
  zesu_reduce_closed_Z_aliases;
  zesu_normalize_wrapped_findmem ltac:(
    zesu_reduce_closed_Z_aliases; cbv [bv_unsigned bv_modulus] in *; lia);
  liStep.



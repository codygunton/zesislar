Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.PureFacts.
Require ZesuSsz.Automation2.VmClosed.
Require ZesuSsz.Automation2.RangeFacts.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
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
    ZesuSsz.Automation2.VmClosed.zesu_closed_term scalar;
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

(* A list index `Z.to_nat e` whose `e` holds `bv_unsigned` of a chain of
   closed offsets on a word w, and w's own `bv_unsigned` elsewhere, as in
   `bv_unsigned (w + c1 + c2) - (bv_unsigned w - k)` for a load from a frame
   array. The offsets reduce to one signed literal s, so the address is
   `bv_unsigned w + s` when it does not wrap, and `e` is then a literal. *)
Lemma zesu_wrapped_offset_word (width : N) (word : bv width) :
  bv_unsigned word = bv_wrap width (bv_unsigned word + 0).
Proof. rewrite Z.add_0_r. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

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

(* A proof of [bv_unsigned word = bv_wrap width (bv_unsigned w + sum)], where
   w is the word below the closed offsets. *)
Ltac zesu_wrapped_offset_chain word :=
  match word with
  | bv_add ?inner ?step =>
      let _ := match goal with _ => ZesuSsz.Automation2.VmClosed.zesu_vm_closed step end in
      let proof := zesu_wrapped_offset_chain inner in
      constr:(zesu_wrapped_offset_step _ _ _ inner step proof)
  | _ => constr:(zesu_wrapped_offset_word _ word)
  end.

(* 0 <= bv_unsigned w + s < 2^64 from the facts selected for w. The facts may
   sit folded in a predicate over the value w is read from, so that value is
   the search root. *)
Ltac zesu_wrapped_index_range root :=
  let collect := ltac2:(v w |-
    let value := Option.get (Ltac1.to_constr v) in
    let word := Option.get (Ltac1.to_constr w) in
    let source := match Constr.Unsafe.kind word with
      | Constr.Unsafe.App _ args => Array.get args (Int.sub (Array.length args) 1)
      | _ => word end in
    ZesuSsz.Automation2.RangeFacts.zesu_range_collect value value source) in
  collect (bv_unsigned root) root;
  ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_isolate ());
  ZesuSsz.Automation2.RangeFacts.zesu_selected_casts;
  ZesuSsz.Automation2.RangeFacts.zesu_selected_closed_bounds;
  lazymatch goal with |- (0 <= ?value < ?bound)%Z =>
    let reduced := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed bound in
    change (0 <= value < reduced)%Z
  end;
  lia.

(* Prove `Z.to_nat expression = n` for a nat literal n and pass the equation
   to [location]. The address range, the offset and the index are proved,
   never assumed. An index on two different words is not constant: refused. *)
Ltac zesu_wrapped_index_literal expression location :=
  assert_fails (has_evar expression);
  match expression with
  | context[bv_unsigned (bv_add ?inner ?step)] =>
      ZesuSsz.Automation2.VmClosed.zesu_vm_closed step;
      let word := constr:(bv_add inner step) in
      let chain := zesu_wrapped_offset_chain word in
      lazymatch type of chain with
      | bv_unsigned _ = bv_wrap ?width (bv_unsigned ?root + ?sum) =>
          assert_fails (ZesuSsz.Automation2.VmClosed.zesu_vm_closed root);
          lazymatch eval pattern (bv_unsigned word) in expression with
          | ?shape _ =>
              lazymatch eval cbv beta in (shape 0) with
              | context[bv_unsigned root] => idtac
              end
          end;
          let offset := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (bv_swrap width sum) in
          let address := constr:(bv_unsigned root + offset) in
          let Haddress := fresh "HindexAddress" in
          assert (Haddress : bv_unsigned word = address) by
            (refine (zesu_wrapped_offset_small width (bv_unsigned root) sum offset address word chain _ _ _);
             [vm_compute; reflexivity | reflexivity | zesu_wrapped_index_range root]);
          let reduced := lazymatch eval pattern (bv_unsigned word) in expression with
            | ?shape _ => eval cbv beta in (shape address) end in
          let literal := lazymatch eval pattern (bv_unsigned root) in reduced with
            | ?shape _ => eval vm_compute in (shape 0) end in
          lazymatch literal with Z0 => idtac | Zpos _ => idtac end;
          let index := eval vm_compute in (Z.to_nat literal) in
          let Hindex := fresh "HindexLiteral" in
          assert (Hindex : Z.to_nat expression = index) by
            (rewrite Haddress; rewrite ?Z.div_1_r; lia);
          clear Haddress;
          location Hindex;
          clear Hindex
      end
  end.

(* Last alternative of the run loops: fires only on such an index under
   `drop` in the goal or in a list lookup hypothesis. *)
Ltac zesu_wrapped_index_step :=
  first [
    lazymatch goal with |- context[drop (Z.to_nat ?expression) _] =>
      zesu_wrapped_index_literal expression ltac:(fun Hindex => rewrite Hindex) end
  | match goal with
    | Hlookup : _ !! Z.to_nat ?expression = Some _ |- _ =>
        zesu_wrapped_index_literal expression ltac:(fun Hindex => rewrite Hindex in Hlookup)
    end].


Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.PureFacts.
Require ZesuSsz.Automation2.VmClosed.
Require ZesuSsz.Automation2.RangeFacts.
From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Automation2.LiaHook.
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
    zesu_reduce_closed_Z_aliases; cbv [bv_unsigned bv_modulus] in *; zesu_lia);
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
  zesu_lia.

(* Library linear arithmetic: `lia` itself is the project hook (LiaHook.v). *)
Ltac zesu_plain_lia := Coq.micromega.Zify.zify; xlia Coq.micromega.Lia.zchecker.

(* The variable an address or index expression is built on. *)
Ltac zesu_term_root t :=
  lazymatch t with
  | @bv_unsigned _ ?w => zesu_term_root w
  | Z_to_bv _ ?z => zesu_term_root z
  | Z.add ?l _ => zesu_term_root l
  | Z.sub ?l _ => zesu_term_root l
  | @bv_add _ ?l _ => zesu_term_root l
  | @bv_sub _ ?l _ => zesu_term_root l
  | _ => constr:(t)
  end.

(* The value of an expression over [root] at a sample root value. Used only
   to decide which resource or literal to aim at; every use is proved. *)
Ltac zesu_eval_at_root root e :=
  let f := eval pattern root in e in
  lazymatch f with
  | ?g _ =>
      lazymatch type of root with
      | Z => let d := eval vm_compute in (g 2952790016%Z) in d
      | _ => let d := eval vm_compute in (g (Z_to_bv 64 2952790016)) in d
      end
  end.

(* The integer root [z] cancels in [e]: the same value at two sample root
   values. An index that keeps its root is not a literal (and its value at a
   sample root must not reach unary arithmetic). *)
Ltac zesu_root_cancels z e :=
  lazymatch eval pattern z in e with
  | ?g _ =>
      let low := eval vm_compute in (g 0%Z) in
      let high := eval vm_compute in (g 2952790016%Z) in
      constr_eq low high
  end.

Ltac zesu_clear_all_hyps := repeat match goal with H : _ |- _ => clear H end.

(* The frame of a load may sit on an integer root z, `Z_to_bv 64 z + c1 + c2`:
   the offset chain of [zesu_wrapped_offset_chain] with root `Z_to_bv width z`. *)
Lemma zesu_zroot_offset_word (width : N) (z : Z) :
  bv_unsigned (Z_to_bv width z) = bv_wrap width (z + 0).
Proof. rewrite Z_to_bv_unsigned Z.add_0_r. reflexivity. Qed.

Ltac zesu_zroot_chain word :=
  lazymatch word with
  | bv_add ?inner ?step =>
      let _ := match goal with _ => ZesuSsz.Automation2.VmClosed.zesu_vm_closed step end in
      let proof := zesu_zroot_chain inner in
      constr:(zesu_wrapped_offset_step _ _ _ inner step proof)
  | Z_to_bv ?width ?z => constr:(zesu_zroot_offset_word width z)
  end.

(* 0 <= z + s < 2^64 from the order facts on z (no div, mod or length fact). *)
Ltac zesu_zroot_range_select z :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | (_ <= _ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ < _)%Z => idtac
      end;
      lazymatch T with context [z] => idtac end;
      lazymatch T with
      | context [Z.modulo] => fail | context [Z.div] => fail | context [@length] => fail
      | _ => idtac end;
      revert H
  end;
  zesu_clear_all_hyps; intros;
  change (bv_modulus 64) with 18446744073709551616 in *;
  zesu_plain_lia.
Ltac zesu_zroot_range z :=
  first [ solve [zesu_zroot_range_select z]
        | ZesuSsz.Automation2.PureFacts.zesu_saturate_derived_facts; solve [zesu_zroot_range_select z] ].

(* [k] receives `Haddress : bv_unsigned word = z + s` (s a signed literal) and z. *)
Ltac zesu_zroot_address word k :=
  let chain := zesu_zroot_chain word in
  lazymatch type of chain with
  | bv_unsigned _ = bv_wrap ?width (?z + ?sum) =>
      assert_fails (ZesuSsz.Automation2.VmClosed.zesu_vm_closed z);
      let offset := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (bv_swrap width sum) in
      let address := lazymatch offset with Z0 => constr:(z) | _ => constr:((z + offset)%Z) end in
      let Haddress := fresh "HzrootAddress" in
      assert (Haddress : bv_unsigned word = address) by
        (refine (zesu_wrapped_offset_small width z sum offset address word chain _ _ _);
         [vm_compute; reflexivity | first [reflexivity | symmetry; apply Z.add_0_r] | zesu_zroot_range z]);
      k Haddress z
  end.

(* Prove `Z.to_nat expression = n` for a nat literal n and pass the equation
   to [location]. The address range, the offset and the index are proved,
   never assumed. An index on two different words is not constant: refused. *)
Ltac zesu_wrapped_index_literal_word expression location :=
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
            (rewrite Haddress; rewrite ?Z.div_1_r; zesu_lia);
          clear Haddress;
          location Hindex;
          clear Hindex
      end
  end.

(* The index of a load from a frame on an integer root under `Z_to_bv`. *)
Ltac zesu_wrapped_index_literal_zroot expression location :=
  assert_fails (has_evar expression);
  match expression with
  | context[bv_unsigned (bv_add ?inner ?step)] =>
      ZesuSsz.Automation2.VmClosed.zesu_vm_closed step;
      let word := constr:(bv_add inner step) in
      zesu_zroot_address word ltac:(fun Haddress z =>
        lazymatch type of Haddress with
        | _ = ?address =>
          let reduced := lazymatch eval pattern (bv_unsigned word) in expression with
            | ?shape _ => eval cbv beta in (shape address) end in
          zesu_root_cancels z reduced;
          let literal := lazymatch eval pattern z in reduced with
            | ?shape _ => eval vm_compute in (shape 0%Z) end in
          lazymatch literal with Z0 => idtac | Zpos _ => idtac end;
          let index := eval vm_compute in (Z.to_nat literal) in
          let Hindex := fresh "HindexLiteral" in
          assert (Hindex : Z.to_nat expression = index) by
            (rewrite Haddress; rewrite ?Z.div_1_r; clear; zesu_plain_lia);
          clear Haddress;
          location Hindex;
          clear Hindex
        end)
  end.

(* An index that is integer arithmetic over one root: `Z.to_nat (z + c - (z - k))`. *)
Ltac zesu_wrapped_index_literal_integer expression location :=
  assert_fails (has_evar expression);
  lazymatch expression with context [@bv_unsigned] => fail | _ => idtac end;
  let z := zesu_term_root expression in
  assert_fails (ZesuSsz.Automation2.VmClosed.zesu_vm_closed z);
  zesu_root_cancels z expression;
  let literal := zesu_eval_at_root z expression in
  lazymatch literal with Z0 => idtac | Zpos _ => idtac end;
  let index := eval vm_compute in (Z.to_nat literal) in
  let Hindex := fresh "HindexLiteral" in
  assert (Hindex : Z.to_nat expression = index) by (zesu_clear_all_hyps; zesu_plain_lia);
  location Hindex;
  clear Hindex.

(* The index over a word root, over an integer root under `Z_to_bv`, or as
   integer arithmetic over one root. *)
Ltac zesu_wrapped_index_literal expression location :=
  first [ zesu_wrapped_index_literal_word expression location
        | zesu_wrapped_index_literal_zroot expression location
        | zesu_wrapped_index_literal_integer expression location ].

(* Last alternative of the run loops: fires only on such an index under
   `drop` in the goal (every occurrence is tried) or in a list lookup
   hypothesis. *)
Ltac zesu_wrapped_index_step :=
  first [
    match goal with |- context[drop (Z.to_nat ?expression) _] =>
      zesu_wrapped_index_literal expression ltac:(fun Hindex => rewrite Hindex) end
  | match goal with
    | Hlookup : _ !! Z.to_nat ?expression = Some _ |- _ =>
        zesu_wrapped_index_literal expression ltac:(fun Hindex => rewrite Hindex in Hlookup)
    end].

(* An array-bound side condition on such an index: once the index is a
   literal, the list's known length decides the bound by computation. *)
Ltac zesu_wrapped_index_bound_goal :=
  lazymatch goal with
  | |- (Z.to_nat ?expression + _ <= length ?values)%nat =>
      zesu_wrapped_index_literal expression ltac:(fun Hindex => rewrite Hindex)
  | |- (Z.to_nat ?expression < length ?values)%nat =>
      zesu_wrapped_index_literal expression ltac:(fun Hindex => rewrite Hindex)
  end;
  lazymatch goal with
  | |- context [length ?values] =>
      match goal with Hlength : length values = _ |- _ => rewrite Hlength end
  end;
  ZesuSsz.Automation2.VmClosed.zesu_vm_closed_decide.


(* A word stored byte by byte and read back: the explicit list
   `[Z_to_bv 8 (z ≫ (8 * 0)); …; Z_to_bv 8 (z ≫ (8 * (n - 1)))]` read as a
   little-endian word of 8n bits is `Z_to_bv (8n) z`. The list spine is
   matched by conversion against `map _ (seq 0 n)`, so a list of any other
   shape is left alone. *)
From stdpp Require Import bitblast.
Local Open Scope Z_scope.
Lemma zesu_word_shift_bytes_from (n k : nat) (z : Z) :
  little_endian_to_bv 8 (map (fun i : nat => Z_to_bv 8 (z ≫ (8 * Z.of_nat i))) (seq k n)) =
  Z.modulo (z ≫ (8 * Z.of_nat k)) (2 ^ (Z.of_nat n * 8)).
Proof.
  revert k. induction n as [|n IH]; intros k.
  - cbn. rewrite Z.mod_1_r. reflexivity.
  - cbn [List.seq List.map]. unfold little_endian_to_bv in *. cbn [fmap list_fmap].
    cbn [list_numbers.little_endian_to_Z]. rewrite IH. rewrite Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus.
    replace (Z.of_nat (S k)) with (Z.of_nat k + 1)%Z by lia.
    replace (Z.of_nat (S n) * 8)%Z with (8 + Z.of_nat n * 8)%Z by lia.
    cbn [Z.of_N]. bitblast. f_equal; lia.
Qed.
Lemma zesu_word_explicit_list (w : N) (n : nat) (z : Z) :
  Z.of_N w = Z.of_nat n * 8 ->
  Z_to_bv w (little_endian_to_bv 8 (map (fun i : nat => Z_to_bv 8 (z ≫ (8 * Z.of_nat i))) (seq 0 n))) =
  Z_to_bv w z.
Proof.
  intros Hw. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite zesu_word_shift_bytes_from.
  unfold bv_wrap, bv_modulus. rewrite Hw. change (Z.of_nat 0) with 0.
  rewrite Z.mul_0_r. rewrite Z.shiftr_0_r.
  apply Z.mod_mod. apply Z.pow_nonzero; lia.
Qed.
Ltac zesu_word_explicit_list_rewrite :=
  progress repeat match goal with
  | |- context [Z_to_bv ?w (little_endian_to_bv 8 ?l)] =>
      lazymatch l with cons (Z_to_bv 8 (Z.shiftr ?z _)) _ =>
        let n := eval lazy [length] in (length l) in
        let E := fresh "HwordList" in
        assert (E : Z_to_bv w (little_endian_to_bv 8 l) = Z_to_bv w z)
          by exact (zesu_word_explicit_list w n z eq_refl);
        rewrite E; clear E
      end
  end.

(* The same word read back by a load: `bv_concat` of the bytes
   `Z_to_bv 8 (z ≫ _)` of one integer `z`, against `Z_to_bv w z`. Every leaf
   must be a byte of that `z` (`zesu_word_concat_bytes_of`); then the
   equation is bit-blasted, each bit an index equation. The equation holds
   for every `z`, so it is proved in a context cleared of hypotheses: bitblast
   asks lia several hundred times per word, and on a block's context (about
   240 facts on nextUint64 0000) those calls cost 350 of its 1,800 s. *)
Ltac zesu_word_concat_bytes_of t z :=
  lazymatch t with
  | bv_concat _ ?high ?low =>
      zesu_word_concat_bytes_of high z; zesu_word_concat_bytes_of low z
  | Z_to_bv 8 (Z.shiftr ?z' _) => constr_eq z z'
  end.
Ltac zesu_word_concat_bytes_eq :=
  lazymatch goal with
  | |- @eq (bv _) (bv_concat ?n ?high ?low) (Z_to_bv ?n ?z) =>
      zesu_word_concat_bytes_of (bv_concat n high low) z
  | |- @eq (bv _) (Z_to_bv ?n ?z) (bv_concat ?n ?high ?low) =>
      zesu_word_concat_bytes_of (bv_concat n high low) z; symmetry
  end;
  solve [zesu_clear_all_hyps; bv_simplify; bitblast; f_equal; zesu_lia].

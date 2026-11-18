Require Import ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.Hooks.
Require Import ZesuSsz.Automation2.PureFacts.
Require Import ZesuSsz.Automation2.ResourceGroups.
Require Import ZesuSsz.Automation2.TracePrefixTail.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
Require SailStdpp.MachineWord.
Require ZesuSsz.Automation2.RangeFacts.
Require Import ZesuSsz.Contracts.NamedEquation.
From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Automation2.LiaHook.
Set Default Proof Mode "Classic".

Section interior_byte_slice.
Context `{!islaG Sigma}.

(* The continuation restores the same bytes after the callee returns. *)
Lemma zesu_byte_array_lend_slice (base : Z) (bytes : list (bv 8))
    (start count : nat) :
  (start + count <= length bytes)%nat ->
  base ↦ₘ∗ bytes -∗
  (base + Z.of_nat start) ↦ₘ∗ take count (drop start bytes) ∗
  ((base + Z.of_nat start) ↦ₘ∗ take count (drop start bytes) -∗
    base ↦ₘ∗ bytes).
Proof.
  iIntros (Hbounds) "Harray".
  iDestruct (mem_mapsto_array_region 8%N base (DfracOwn 1)
    bytes start count with "Harray") as "(Hprefix & Hslice & Hsuffix)"; [done|].
  have Hstride : Z.of_N (8 / 8) = 1%Z by (vm_cast_no_check (eq_refl (1%Z))).
  iEval (rewrite Hstride Z.mul_1_l) in "Hslice Hsuffix".
  iFrame "Hslice". iIntros "Hslice".
  iPoseProof (mem_mapsto_array_app_combine_at 8%N base (DfracOwn 1)
    (take start bytes) (take count (drop start bytes)) start
    with "Hprefix [Hslice]") as "Hfirst".
  { rewrite length_take. lia. }
  { rewrite Hstride Z.mul_1_l. iExact "Hslice". }
  iPoseProof (mem_mapsto_array_app_combine_at 8%N base (DfracOwn 1)
    (take start bytes ++ take count (drop start bytes))
    (drop (start + count) bytes) (start + count)
    with "Hfirst [Hsuffix]") as "Hwhole".
  { rewrite length_app !length_take length_drop. lia. }
  { rewrite Hstride Z.mul_1_l. iExact "Hsuffix". }
  rewrite -drop_drop -app_assoc take_drop take_drop.
  iExact "Hwhole".
Qed.
End interior_byte_slice.
Print Assumptions zesu_byte_array_lend_slice.

Class ZesuStepInteriorByteSlice : Prop := zesu_step_interior_byte_slice : True.

(* One step from an address towards the word it is an offset of: an unsigned
   value reads as its word, a sum or difference as its left operand, a local
   definition as its body, a named word (a register a call boundary kept) as
   its value. Fails at a word with no such step. *)
Ltac zesu_byte_slice_address_next term :=
  lazymatch term with
  | @bv_unsigned _ ?word => constr:(word)
  | Z.add ?left _ => constr:(left)
  | Z.sub ?left _ => constr:(left)
  | @bv_add _ ?left _ => constr:(left)
  | @bv_sub _ ?left _ => constr:(left)
  | _ =>
      match goal with
      | local := ?body : _ |- _ =>
          let _ := constr:(ltac:(constr_eq local term; exact I) : True) in
          constr:(body)
      | _ : zesu_named_eq term ?value |- _ => constr:(value)
      end
  end.

(* The word an array's base is an offset of (no definitions unfolded: a base
   is the caller's argument or stack pointer as the contract states it). *)
Ltac zesu_byte_slice_base_root base :=
  lazymatch base with
  | @bv_unsigned _ ?word => zesu_byte_slice_base_root word
  | Z.add ?left _ => zesu_byte_slice_base_root left
  | Z.sub ?left _ => zesu_byte_slice_base_root left
  | @bv_add _ ?left _ => zesu_byte_slice_base_root left
  | @bv_sub _ ?left _ => zesu_byte_slice_base_root left
  | _ => constr:(base)
  end.

(* An array can hold the slice only if the slice address is reached from the
   array's base word, or a fact places a word on the address's way inside the
   array's bytes (a callee's sealed domain over `drop (.. word ..) bytes`).
   Syntactic: an array that fails here is skipped before any arithmetic. *)
Ltac zesu_byte_slice_reaches term root bytes :=
  first [
    constr_eq term root
  | is_var term;
    match goal with
    | _ : context[drop (Z.to_nat ?offset) bytes] |- _ =>
        lazymatch offset with context[term] => idtac end
    end
  | let next := zesu_byte_slice_address_next term in
    zesu_byte_slice_reaches next root bytes ].

Ltac zesu_byte_slice_related address base bytes :=
  let root := zesu_byte_slice_base_root base in
  zesu_byte_slice_reaches address root bytes.

Ltac zesu_byte_slice_start address base :=
  lazymatch address with
  | bv_unsigned (?register + ?offset)%bv =>
      lazymatch base with
      | (bv_unsigned register + ?baseOffset)%Z =>
          let start := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (Z.to_nat (bv_unsigned offset - baseOffset)) in
          constr:(start)
      | _ => constr:(Z.to_nat (address - base))
      end
  | _ => constr:(Z.to_nat (address - base))
  end.

(* The size that a pure fact states for the requested slice, as a value: a
   fact `size = Z.of_nat (length slice)`, or such an equation among its
   conjuncts. *)
Ltac zesu_byte_slice_size_stated fact slice :=
  match fact with
  | ?left /\ _ => zesu_byte_slice_size_stated left slice
  | _ /\ ?right => zesu_byte_slice_size_stated right slice
  | @eq Z ?size ?measure =>
      let measure := eval cbn in measure in
      lazymatch measure with
      | Z.of_nat (@length _ ?measured) =>
          let measured := eval cbn in measured in
          lazymatch constr:((measured, slice)) with
          | (?same, ?same) => let size := eval cbn in size in constr:(size)
          end
      end
  end.

(* What a registered lemma (a `ZesuDerivedFacts` instance) derives from a
   fact. A callee's call-site domain is sealed: its interface registers the
   facts a caller may read from it, and the step reads them only this way,
   never by unfolding. One fact may have several registered lemmas, so the
   search asks for a conclusion that states the slice's length (alone or as
   a first conjunct) before it takes whichever lemma comes first. *)
Ltac zesu_byte_slice_derived fact slice :=
  let derivation := match constr:(tt) with
    | _ => constr:(@ZesuSsz.Automation.PureFacts.zesu_derived_facts
             fact (_ = Z.of_nat (length slice) /\ _) _)
    | _ => constr:(@ZesuSsz.Automation.PureFacts.zesu_derived_facts
             fact (_ = Z.of_nat (length slice)) _)
    | _ => constr:(@ZesuSsz.Automation.PureFacts.zesu_derived_facts fact _ _)
    end in
  lazymatch type of derivation with _ -> ?derived => derived end.

(* The size for the slice that a fact states, or that a registered lemma
   derives from it (one derivation, no chains). *)
Ltac zesu_byte_slice_size_in fact slice :=
  match constr:(tt) with
  | _ => zesu_byte_slice_size_stated fact slice
  | _ =>
      let derived := zesu_byte_slice_derived fact slice in
      zesu_byte_slice_size_stated derived slice
  end.

Ltac zesu_byte_slice_size rest slice :=
  match rest with
  | context[(⌜?size = Z.of_nat (length slice)⌝)%I] => constr:(size)
  | context[@bi_pure _ ?fact] =>
      lazymatch fact with context[slice] => zesu_byte_slice_size_in fact slice end
  end.

(* A closed size is evaluated; any other size is counted as it stands. *)
Ltac zesu_byte_slice_count size :=
  match constr:(tt) with
  | _ => ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (Z.to_nat size)
  | _ => constr:(Z.to_nat size)
  end.

(* Bounds of a slice whose start or size is symbolic: the derived facts of
   the context (a callee's consumed count, its input length), slice lengths
   unfolded, sums and differences of words without wrap, and element-type and
   width aliases normalized so that the arithmetic sees one atom per term. *)
Ltac zesu_byte_slice_alias_normalize :=
  repeat match goal with
  | H : context[SailStdpp.MachineWord.MachineWord.Z_idx ?z] |- _ =>
      let v := eval vm_compute in (SailStdpp.MachineWord.MachineWord.Z_idx z) in
      change (SailStdpp.MachineWord.MachineWord.Z_idx z) with v in H
  | |- context[SailStdpp.MachineWord.MachineWord.Z_idx ?z] =>
      let v := eval vm_compute in (SailStdpp.MachineWord.MachineWord.Z_idx z) in
      change (SailStdpp.MachineWord.MachineWord.Z_idx z) with v
  | H : context[@length ?T ?l] |- _ =>
      let T' := eval cbv in T in assert_fails (constr_eq T T');
      change (@length T l) with (@length T' l) in H
  | |- context[@length ?T ?l] =>
      let T' := eval cbv in T in assert_fails (constr_eq T T');
      change (@length T l) with (@length T' l)
  | H : context[@List.nth ?T ?k ?l ?d] |- _ =>
      let T' := eval cbv in T in assert_fails (constr_eq T T');
      change (@List.nth T k l d) with (@List.nth T' k l d) in H
  | |- context[@List.nth ?T ?k ?l ?d] =>
      let T' := eval cbv in T in assert_fails (constr_eq T T');
      change (@List.nth T k l d) with (@List.nth T' k l d)
  end.

(* A hypothesis word convertible to a goal word is restated in the goal's
   form, whatever alias it was elaborated at. *)
Ltac zesu_byte_slice_goal_atoms :=
  repeat match goal with
  | |- context[@bv_unsigned ?n ?a] =>
      match goal with
      | H : context[@bv_unsigned ?m ?b] |- _ =>
          assert_fails (constr_eq a b);
          assert_fails (has_evar b);
          unify (@bv_unsigned m b) (@bv_unsigned n a);
          change (@bv_unsigned m b) with (@bv_unsigned n a) in H
      end
  end.

Ltac zesu_byte_slice_unsigned_range n x :=
  assert_fails (has_evar x);
  lazymatch goal with
  | _ : (0 <= @bv_unsigned n x < _)%Z |- _ => fail
  | _ => pose proof (bv_unsigned_in_range n x)
  end.

Ltac zesu_byte_slice_unsigned_ranges :=
  repeat match goal with
  | |- context[@bv_unsigned ?n ?x] => zesu_byte_slice_unsigned_range n x
  | _ : context[@bv_unsigned ?n ?x] |- _ => zesu_byte_slice_unsigned_range n x
  end.

(* A word read from list bytes (a callee's output) is an opaque atom to
   arithmetic: that it is positive holds only where a fact states it (a
   branch on the word; the decodeItem interface states no such bound, since a
   successful decode may return an empty payload). Such a premise comes from
   that fact or fails; it never reaches `lia`, which on a decodeParentHeader
   caller's context grew past 24 GiB on it. *)
Lemma zesu_byte_slice_unsigned_pos_of_neq n (w : bv n) :
  bv_unsigned w <> 0%Z -> (0 < bv_unsigned w)%Z.
Proof. pose proof (bv_unsigned_in_range n w). lia. Qed.

Ltac zesu_byte_slice_list_word_positive_goal :=
  lazymatch goal with
  | |- (0 < @bv_unsigned _ ?w)%Z =>
      lazymatch w with
      | bv_concat _ _ _ => idtac
      | Z_to_bv _ (little_endian_to_bv _ _) => idtac
      end
  end.

Ltac zesu_byte_slice_positive_from_facts :=
  lazymatch goal with
  | |- (0 < @bv_unsigned ?n ?w)%Z =>
      first [assumption |
        match goal with
        | H : not (@eq Z (@bv_unsigned _ ?v) Z0) |- _ =>
            unify v w; exact (zesu_byte_slice_unsigned_pos_of_neq n w H)
        | H : not (@eq Z Z0 (@bv_unsigned _ ?v)) |- _ =>
            unify v w; exact (zesu_byte_slice_unsigned_pos_of_neq n w (not_eq_sym H))
        end]
  end.

(* A derived fact stated under premises: each premise the context shows,
   directly or by arithmetic, is discharged. A premise is tried once: a fact
   whose premise fails is dropped from this local proof, so a later success
   does not retry every failed premise. *)
Ltac zesu_byte_slice_discharge_premises :=
  repeat match goal with
  | H : ?P -> ?Q |- _ =>
      lazymatch type of P with Prop => idtac end;
      first [
        let Hp := fresh "Hpremise" in
        assert (Hp : P) by (first [assumption |
          tryif zesu_byte_slice_list_word_positive_goal
          then zesu_byte_slice_positive_from_facts else zesu_lia]);
        specialize (H Hp); clear Hp
      | clear H ]
  end;
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

(* A named value (a register a call boundary kept under a name) reads as its
   value: the arithmetic sees the name's equation, also between the unsigned
   values of a named word. *)
Ltac zesu_byte_slice_named_values :=
  repeat match goal with
  | H : zesu_named_eq ?name ?value |- _ =>
      let E := fresh "HsliceNamed" in
      pose proof (proj1 (zesu_named_eq_iff name value) H) as E; clear H;
      lazymatch type of name with
      | bv ?n => pose proof (f_equal (@bv_unsigned n) E)
      | _ => idtac
      end
  end.

(* Closed integer subterms of one selected fact, evaluated (a contract's
   named constants). The fact is small; the goal is not touched. *)
Ltac zesu_byte_slice_reduce_closed_in H :=
  repeat match type of H with
  | context[?term] =>
      lazymatch type of term with Z => idtac end;
      lazymatch term with Z0 => fail | Zpos _ => fail | Zneg _ => fail | _ => idtac end;
      let value := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed term in
      progress change term with value in H
  end.

(* The owning array's base word is the caller's own value (a contract
   argument's pointer): its range facts sit folded in the caller's
   precondition over that argument. Project the conjuncts that state the
   base, as the region bounds do, and evaluate their constants. *)
Ltac zesu_byte_slice_base_ranges base :=
  let root := lazymatch base with
    | bv_unsigned (?accessor ?argument) => constr:(argument)
    | _ => base end in
  let collect := ltac2:(v p r |- ZesuSsz.Automation2.RangeFacts.zesu_range_collect
    (Option.get (Ltac1.to_constr v)) (Option.get (Ltac1.to_constr p))
    (Option.get (Ltac1.to_constr r))) in
  collect base base root;
  let reduce := ltac:(fun H => zesu_byte_slice_reduce_closed_in H) in
  let reduce_selected := ltac2:(r |- List.iter (fun h => let (name, _, _) := h in
    if ZesuSsz.Automation2.RangeFacts.zesu_name_prefix (Ident.to_string name) "HrangeFact" 0
    then Ltac1.apply r [Ltac1.of_constr (Control.hyp name)] Ltac1.run
    else ()) (Control.hyps ())) in
  reduce_selected reduce.

Ltac zesu_byte_slice_moduli :=
  repeat match goal with
  | H : context[bv_modulus ?n] |- _ =>
      let v := eval vm_compute in (bv_modulus n) in change (bv_modulus n) with v in H
  | |- context[bv_modulus ?n] =>
      let v := eval vm_compute in (bv_modulus n) in change (bv_modulus n) with v
  end.

Ltac zesu_byte_slice_bound_arith :=
  zesu_byte_slice_named_values;
  ZesuSsz.Automation.PureFacts.zesu_saturate_derived_facts;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with
  | H : context[length (take _ _)] |- _ => rewrite length_take in H
  | H : context[length (drop _ _)] |- _ => rewrite length_drop in H
  end;
  rewrite ?length_take ?length_drop ?bv_add_unsigned ?bv_sub_unsigned; unfold bv_wrap;
  zesu_byte_slice_unsigned_ranges;
  zesu_byte_slice_alias_normalize;
  zesu_byte_slice_moduli;
  zesu_byte_slice_discharge_premises;
  zesu_byte_slice_goal_atoms;
  repeat match goal with
  | |- context[(?a mod ?m)%Z] => rewrite (Z.mod_small a m); [|zesu_lia]
  end;
  zesu_lia.

(* The bound arithmetic with the range facts of the owning array's base. *)
Ltac zesu_byte_slice_bound_arith_at base :=
  try zesu_byte_slice_base_ranges base;
  zesu_byte_slice_bound_arith.

(* The facts a lend's side goal can use: those that mention a value word of
   the goal (a word, integer, count or byte list; local definitions read
   through to the words they are built from), and the facts over contract
   arguments alone (the caller's precondition, where the base's range sits).
   One hop: a fact is not kept because it shares a word with another kept
   fact, and a contract argument links nothing (every call's sealed facts
   mention the caller's input). A block context chains its calls (each
   call's cursor is the last one's plus its consumed count), so the
   transitive closure is the whole context: the derived-fact saturation on
   it ran past 800 s on a decodeParentHeader block. A fact whose words cannot
   be read is kept. *)
Ltac2 zesu_byte_slice_value_word (name : ident) :=
  let ty := Constr.type (Control.hyp name) in
  lazy_match! ty with
  | bv _ => true
  | Z => true
  | nat => true
  | N => true
  | bool => true
  | list _ => true
  | _ => false
  end.

Ltac2 zesu_byte_slice_focus () :=
  let hyps := Control.hyps () in
  let variables term :=
    Control.once_plus (fun () => Some (ZesuSsz.Automation2.ContextCollection.zesu_context_variables term))
      (fun _ => None) in
  let seeds := match variables (Control.goal ()) with
    | Some found => found
    | None => Control.zero (Tactic_failure None) end in
  let rec close found :=
    let next := List.fold_left (fun found declaration =>
      let (name, body, _) := declaration in
      match body with
      | Some value =>
          if ZesuSsz.Automation2.ContextCollection.zesu_context_member name found then
            match variables value with
            | Some inner => ZesuSsz.Automation2.ContextCollection.zesu_context_union found inner
            | None => found
            end
          else found
      | None => found
      end) found hyps in
    if Int.equal (List.length next) (List.length found) then found else close next in
  let seeds := List.filter zesu_byte_slice_value_word (close seeds) in
  List.iter (fun declaration =>
    let (name, body, ty) := declaration in
    match body with
    | Some _ => ()
    | None =>
        if ZesuSsz.Automation2.ContextCollection.zesu_context_proposition ty then
          match variables ty with
          | Some found =>
              let words := List.filter zesu_byte_slice_value_word found in
              if Int.equal (List.length words) 0 then ()
              else if ZesuSsz.Automation2.ContextCollection.zesu_context_intersects words seeds then ()
              else Control.once_plus (fun () => Std.clear [name]) (fun _ => ())
          | None => ()
          end
        else ()
    end) (List.rev hyps).

(* One arithmetic side goal of a lend, on the focused context: `lia`
   (budgeted), then the bound arithmetic. *)
Ltac zesu_byte_slice_arith base :=
  rewrite ?length_take ?length_drop;
  ltac2:(zesu_byte_slice_focus ());
  first [solve [zesu_lia] | solve [zesu_byte_slice_bound_arith_at base]].

Ltac zesu_lend_interior_byte_slice :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T ?body) =>
      let witness := zesu_tuple_witness T in
      let opened := eval cbv beta iota delta [li_fst] in (body witness) in
      lazymatch opened with
      | ((?address ↦ₘ∗ ?slice) ∗ ?rest)%I =>
          has_evar slice;
          assert_fails (has_evar address);
          let size := zesu_byte_slice_size rest slice in
          let count := zesu_byte_slice_count size in
          assert_fails (has_evar count);
              iMatchHyp ltac:(fun Harray resource =>
                lazymatch resource with
                | (?base ↦ₘ∗ ?bytes)%I =>
                    let element := type of bytes in
                    let element := eval cbv in element in
                    lazymatch element with list (bv 8) => idtac end;
                    zesu_byte_slice_related address base bytes;
                    assert_fails (unify address base);
                    let start := zesu_byte_slice_start address base in
                    let Haddress := fresh "HsliceAddress" in
                    let Hbounds := fresh "HsliceBounds" in
                    assert (Haddress : (base + Z.of_nat start = address)%Z)
                      by zesu_byte_slice_arith base;
                    assert (Hbounds : (start + count <= length bytes)%nat)
                      by zesu_byte_slice_arith base;
                    let Hsize := fresh "HsliceSize" in
                    let Hlength := fresh "HsliceLength" in
                    assert (Hsize : size = Z.of_nat count)
                      by (first [reflexivity | solve [zesu_lia]
                                | (rewrite Z2Nat.id;
                                   [reflexivity | zesu_byte_slice_arith base])]);
                    assert (Hlength :
                      size = Z.of_nat (length (take count (drop start bytes))))
                      by (rewrite Hsize length_take length_drop; zesu_lia);
                    iDestruct (zesu_byte_array_lend_slice base bytes start count
                      Hbounds with Harray) as "[Hslice Hrestore]";
                    iEval (rewrite Haddress) in "Hslice Hrestore";
                    unify slice (take count (drop start bytes));
                    first [
                      lazymatch rest with
                      | context[spec_trace ?generated] =>
                          let candidate := eval cbv beta iota delta [li_fst] in
                            (witness.1ₗ) in
                          let abstracted := eval pattern candidate in generated in
                          lazymatch abstracted with
                          | ?prefix _ =>
                              let marker := constr:(fun _ : list seq_label => False) in
                              let probe := eval cbv beta in (prefix marker) in
                              iMatchHyp ltac:(fun Htrace resource =>
                                lazymatch resource with
                                | spec_trace ?declared =>
                                    let tail := zesu_matching_trace_tail marker probe declared in
                                    unify candidate tail;
                                    iPoseProof (spec_trace_mono declared generated
                                      with Htrace) as "HsliceTrace";
                                    [zesu_trace_prefix_inclusion |]
                                end)
                          end
                      end
                    | idtac];
                    iExists witness
                end)
      end
  end.

Ltac zesu_lend_interior_byte_slice_if_enabled :=
  let _ := constr:(_ : ZesuStepInteriorByteSlice) in
  zesu_lend_interior_byte_slice.

Ltac zesu_restore_interior_byte_slice :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ ((?address ↦ₘ∗ ?bytes) ∗ _)%I =>
      let target := constr:((address ↦ₘ∗ bytes)%I) in
      assert_fails (has_evar target);
      iMatchHyp ltac:(fun Hrestore resource =>
        lazymatch resource with
        | (?borrowed -∗ ?whole)%I =>
            constr_eq whole target;
            iMatchHyp ltac:(fun Hslice returned =>
              constr_eq returned borrowed;
              iPoseProof (Hrestore with Hslice) as "?")
        end)
  end.

Ltac zesu_restore_interior_byte_slice_if_enabled :=
  let _ := constr:(_ : ZesuStepInteriorByteSlice) in
  zesu_restore_interior_byte_slice.

(* Both halves as one search step, for a pass that lists steps by goal. *)
Ltac zesu_interior_byte_slice_step :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ _ _) => zesu_lend_interior_byte_slice_if_enabled
  | |- envs_entails _ ((_ ↦ₘ∗ _) ∗ _)%I => zesu_restore_interior_byte_slice_if_enabled
  end.

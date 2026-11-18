Require Import ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.Hooks.
Require Import ZesuSsz.Automation2.PureFacts.
Require Import ZesuSsz.Automation2.ResourceGroups.
Require Import ZesuSsz.Automation2.TracePrefixTail.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.NamedEquation.
From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Automation2.LiaHook.
Require ZesuSsz.Automation2.ArithContext.
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

(* One arithmetic side goal of a lend, on the focused context: `lia`, then
   the shared context arithmetic (ArithContext) with the range facts of the
   owning array's base. *)
Ltac zesu_byte_slice_arith base :=
  rewrite ?length_take ?length_drop;
  ZesuSsz.Automation2.ArithContext.zesu_arith_focus;
  first [solve [zesu_lia] | solve [ZesuSsz.Automation2.ArithContext.zesu_arith_context_solve_at base]].

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

(** Call-site declarations: what a call's own block states about the call.

    The generator (tools/block/call_boundary.py, call_site_declarations) states, in the entry of
    the block that ends in call k, the call's input slice under the names the return site uses:

      ⌜zesu_named_eq callk_input_offset OFF⌝ ∗ ⌜zesu_named_eq callk_input_length LEN⌝ ∗
      ⌜zesu_named_eq callk_input (take (Z.to_nat callk_input_length)
                                      (drop (Z.to_nat callk_input_offset) BYTES))⌝ ∗
      ⌜0 <= callk_input_offset /\ 0 <= callk_input_length /\
       callk_input_offset + callk_input_length <= Z.of_nat (length BYTES) /\
       Z.of_nat (length callk_input) = callk_input_length⌝ ∗
      bv_unsigned ARGV ↦ₘ∗ callk_input ∗
      (bv_unsigned ARGV ↦ₘ∗ callk_input -∗ BASE ↦ₘ∗ BYTES)

    The split is the entry's statement, not a proof script's. Two generic steps read it:

    - the predecessor's exit (the goal is that statement, its binders instantiated by the named
      equations) lends the slice from the owned [BASE ↦ₘ∗ BYTES] at the stated offset and length:
      [zesu_lend_declared_call_input]. The base is the wand's; the bounds are the stated bounds
      fact, proved once as a pure goal; nothing is searched;
    - after the call (the callee returns the piece at its argument address), a goal that asks for
      the whole array takes it from the declared wand: [zesu_restore_declared_call_input].

    The call itself finds the piece at its own argument address term, as stated. *)
From iris.proofmode Require Import environments.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.ResourceGroups.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Export ZesuSsz.Contracts.NamedEquation.
Require ZesuSsz.Automation2.VmClosed.
Require ZesuSsz.Automation2.PureFacts.
Require ZesuSsz.Automation2.MemoryAddress.
Set Default Proof Mode "Classic".

Section zesu_call_declarations.
Context `{!islaG Sigma}.

(* The slice at [base + off] of [len] bytes, and the wand that gives the whole array back. *)
Lemma zesu_byte_array_lend_declared (base off len : Z) (bytes : list (bv 8)) :
  (0 <= off)%Z -> (0 <= len)%Z -> (off + len <= Z.of_nat (length bytes))%Z ->
  base ↦ₘ∗ bytes -∗
  (base + off) ↦ₘ∗ take (Z.to_nat len) (drop (Z.to_nat off) bytes) ∗
  ((base + off) ↦ₘ∗ take (Z.to_nat len) (drop (Z.to_nat off) bytes) -∗ base ↦ₘ∗ bytes).
Proof.
  iIntros (Hoff Hlen Hend) "Harray".
  iDestruct (mem_mapsto_array_region 8%N base (DfracOwn 1)
    bytes (Z.to_nat off) (Z.to_nat len) with "Harray") as "(Hprefix & Hslice & Hsuffix)"; [lia|].
  have Hstride : Z.of_N (8 / 8) = 1%Z by (vm_cast_no_check (eq_refl (1%Z))).
  iEval (rewrite Hstride Z.mul_1_l Z2Nat.id; [|lia]) in "Hslice".
  iEval (rewrite Hstride Z.mul_1_l) in "Hsuffix".
  iFrame "Hslice". iIntros "Hslice".
  iPoseProof (mem_mapsto_array_app_combine_at 8%N base (DfracOwn 1)
    (take (Z.to_nat off) bytes) (take (Z.to_nat len) (drop (Z.to_nat off) bytes)) (Z.to_nat off)
    with "Hprefix [Hslice]") as "Hfirst".
  { rewrite length_take. lia. }
  { rewrite Hstride Z.mul_1_l Z2Nat.id; [iExact "Hslice"|lia]. }
  iPoseProof (mem_mapsto_array_app_combine_at 8%N base (DfracOwn 1)
    (take (Z.to_nat off) bytes ++ take (Z.to_nat len) (drop (Z.to_nat off) bytes))
    (drop (Z.to_nat off + Z.to_nat len) bytes) (Z.to_nat off + Z.to_nat len)
    with "Hfirst [Hsuffix]") as "Hwhole".
  { rewrite length_app !length_take length_drop. lia. }
  { rewrite Hstride Z.mul_1_l. iExact "Hsuffix". }
  rewrite -drop_drop -app_assoc take_drop take_drop.
  iExact "Hwhole".
Qed.

(* The predecessor's exit: the stated bounds stay the goal's pure fact, with the equation of the
   piece's address to [base + off]; the slice's length follows from them. The owned whole array
   pays for the piece and the wand. *)
Lemma zesu_tac_lend_declared_slice Δ (base address off len : Z) (bytes : list (bv 8)) (R : iProp Sigma) :
  envs_entails Δ (⌜((0 <= off /\ 0 <= len /\ off + len <= Z.of_nat (List.length bytes)) /\
                    base + off = address)%Z⌝ ∗ (base ↦ₘ∗ bytes ∗ R)) ->
  envs_entails Δ (⌜(0 <= off /\ 0 <= len /\ off + len <= Z.of_nat (List.length bytes) /\
                    Z.of_nat (List.length (take (Z.to_nat len) (drop (Z.to_nat off) bytes))) = len)%Z⌝ ∗
    ((address ↦ₘ∗ take (Z.to_nat len) (drop (Z.to_nat off) bytes)) ∗
     (((address ↦ₘ∗ take (Z.to_nat len) (drop (Z.to_nat off) bytes)) -∗ base ↦ₘ∗ bytes) ∗ R))).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "[%Hfacts [Hbytes $]]".
  destruct Hfacts as [(Hoff & Hlen & Hend) <-].
  iSplitR; [iPureIntro; rewrite length_take length_drop; lia|].
  iDestruct (zesu_byte_array_lend_declared base off len bytes with "Hbytes") as "[$ $]"; done.
Qed.

(* The same inside Lithium's packed binders, when the entry's remaining binders are still open
   (the declaration mentions none of them). *)
Lemma zesu_tac_lend_declared_slice_ex {A B} Δ (base address off len : Z) (bytes : list (bv 8))
    (R : A *ₗ B → iProp Sigma) :
  envs_entails Δ (⌜((0 <= off /\ 0 <= len /\ off + len <= Z.of_nat (List.length bytes)) /\
                    base + off = address)%Z⌝ ∗ (base ↦ₘ∗ bytes ∗ ∃ₗ x, R x)) ->
  envs_entails Δ (∃ₗ x, ⌜(0 <= off /\ 0 <= len /\ off + len <= Z.of_nat (List.length bytes) /\
                    Z.of_nat (List.length (take (Z.to_nat len) (drop (Z.to_nat off) bytes))) = len)%Z⌝ ∗
    ((address ↦ₘ∗ take (Z.to_nat len) (drop (Z.to_nat off) bytes)) ∗
     (((address ↦ₘ∗ take (Z.to_nat len) (drop (Z.to_nat off) bytes)) -∗ base ↦ₘ∗ bytes) ∗ R x))).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "[%Hfacts [Hbytes [%x HR]]]". iExists x.
  destruct Hfacts as [(Hoff & Hlen & Hend) <-].
  iSplitR; [iPureIntro; rewrite length_take length_drop; lia|].
  iDestruct (zesu_byte_array_lend_declared base off len bytes with "Hbytes") as "[$ $]"; done.
Qed.

(* The same when the declaration and the entry's own resources sit left of the caller's
   continuation: [⌜bounds⌝ ∗ ((piece ∗ (wand ∗ M)) ∗ K)] (the form an entry followed by its
   continuation takes). *)
Lemma zesu_tac_lend_declared_slice_framed Δ (base address off len : Z) (bytes : list (bv 8))
    (M K : iProp Sigma) :
  envs_entails Δ (⌜((0 <= off /\ 0 <= len /\ off + len <= Z.of_nat (List.length bytes)) /\
                    base + off = address)%Z⌝ ∗ (base ↦ₘ∗ bytes ∗ (M ∗ K))) ->
  envs_entails Δ (⌜(0 <= off /\ 0 <= len /\ off + len <= Z.of_nat (List.length bytes) /\
                    Z.of_nat (List.length (take (Z.to_nat len) (drop (Z.to_nat off) bytes))) = len)%Z⌝ ∗
    (((address ↦ₘ∗ take (Z.to_nat len) (drop (Z.to_nat off) bytes)) ∗
     (((address ↦ₘ∗ take (Z.to_nat len) (drop (Z.to_nat off) bytes)) -∗ base ↦ₘ∗ bytes) ∗ M)) ∗ K)).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "[%Hfacts [Hbytes [$ $]]]".
  destruct Hfacts as [(Hoff & Hlen & Hend) <-].
  iSplitR; [iPureIntro; rewrite length_take length_drop; lia|].
  iDestruct (zesu_byte_array_lend_declared base off len bytes with "Hbytes") as "[$ $]"; done.
Qed.

Lemma zesu_tac_lend_declared_slice_framed_ex {A B} Δ (base address off len : Z) (bytes : list (bv 8))
    (M K : A *ₗ B → iProp Sigma) :
  envs_entails Δ (⌜((0 <= off /\ 0 <= len /\ off + len <= Z.of_nat (List.length bytes)) /\
                    base + off = address)%Z⌝ ∗ (base ↦ₘ∗ bytes ∗ ∃ₗ x, M x ∗ K x)) ->
  envs_entails Δ (∃ₗ x, ⌜(0 <= off /\ 0 <= len /\ off + len <= Z.of_nat (List.length bytes) /\
                    Z.of_nat (List.length (take (Z.to_nat len) (drop (Z.to_nat off) bytes))) = len)%Z⌝ ∗
    (((address ↦ₘ∗ take (Z.to_nat len) (drop (Z.to_nat off) bytes)) ∗
     (((address ↦ₘ∗ take (Z.to_nat len) (drop (Z.to_nat off) bytes)) -∗ base ↦ₘ∗ bytes) ∗ M x)) ∗ K x)).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "[%Hfacts [Hbytes [%x [HM HK]]]]". iExists x.
  destruct Hfacts as [(Hoff & Hlen & Hend) <-].
  iSplitR; [iPureIntro; rewrite length_take length_drop; lia|]. iFrame "HM HK".
  iDestruct (zesu_byte_array_lend_declared base off len bytes with "Hbytes") as "[$ $]"; done.
Qed.
End zesu_call_declarations.

(* The step recognizes the declaration by its bounds fact at the head of the goal (the slice-length
   conjunct over [take]/[drop] is the declaration's own); the lemma's unification checks the piece
   and the wand behind it (up to conversion: Iris's connectives are primitive projections, so a
   syntactic pattern on the nested separating conjunctions misses forms Lithium leaves). The
   declaration and the entry's resources come either right-nested with the rest or grouped left
   of the continuation ([_framed]).
   [bounds] closes the lend's pure premise (the stated bounds over the predecessor's values, and
   the address equation) when it can; otherwise the premise stays Lithium's pure goal. Hooks passes
   the interior-slice bound arithmetic (InteriorByteSlice.v, which imports Hooks). *)
Ltac zesu_lend_declared_call_input bounds :=
  lazymatch goal with
  | |- envs_entails _ (bi_sep (bi_pure (_ /\ _ /\ _ /\ Z.of_nat (List.length (take _ (drop _ _))) = _)) _) =>
      first [notypeclasses refine (zesu_tac_lend_declared_slice _ _ _ _ _ _ _ _)
            |notypeclasses refine (zesu_tac_lend_declared_slice_framed _ _ _ _ _ _ _ _ _)]
  | |- envs_entails _ (@bi_exist _ (li_prod _ _) (λ x, bi_sep
         (bi_pure (_ /\ _ /\ _ /\ Z.of_nat (List.length (take _ (drop _ _))) = _)) _)) =>
      first [notypeclasses refine (zesu_tac_lend_declared_slice_ex _ _ _ _ _ _ _ _)
            |notypeclasses refine (zesu_tac_lend_declared_slice_framed_ex _ _ _ _ _ _ _ _ _)]
  end;
  try (notypeclasses refine (tac_sep_pure _ _ _ _ _); [solve [bounds] |]).

(** The call's output buffer: the entry states it as its own region at the region's address
    (the form the return site states), with [zesu_call_address (bv_unsigned ARGV) REGION]
    (Contracts/NamedEquation.v): the call's argument address term is that address. The
    predecessor proves the equation (a pure goal); at the call the step rewrites the argument
    address in the goal to the region's, so the callee's precondition and its returned resources
    name the region as stated. *)

Ltac zesu_rewrite_declared_call_address :=
  match goal with
  | H : zesu_call_address ?a ?d |- envs_entails _ ?G =>
      lazymatch G with context [a] => idtac end;
      rewrite (H : a = d)
  end.

(* The equation a predecessor states for its successor's call. *)
Ltac zesu_call_address_goal :=
  lazymatch goal with
  | |- envs_entails _ (bi_sep (bi_pure (zesu_call_address _ _)) _) =>
      unfold zesu_call_address
  end.

(* The whole array a goal asks for (first conjunct, also under an existential that does not
   bind it), from the declared wand and the piece the call returned. *)
Ltac zesu_restore_declared_call_input :=
  zesu_expose_environment_alias;
  let target := lazymatch goal with
    | |- envs_entails _ ((?address ↦ₘ∗ ?bytes) ∗ _)%I => constr:((address ↦ₘ∗ bytes)%I)
    | |- envs_entails _ (@bi_exist _ _ (λ x, bi_sep (?address ↦ₘ∗ ?bytes) _)) => constr:((address ↦ₘ∗ bytes)%I)
    end in
  assert_fails (has_evar target);
  iMatchHyp ltac:(fun Hrestore resource =>
    lazymatch resource with
    | (?borrowed -∗ ?whole)%I =>
        constr_eq whole target;
        iMatchHyp ltac:(fun Hslice returned =>
          constr_eq returned borrowed;
          iPoseProof (Hrestore with Hslice) as "?")
    end).

(** The callee's frame: a call spec claims its frame at [bv_unsigned SP - k] where SP is the
    caller's stack register, typically [bv_add sp (BV 64 c)] for a negative [c]; the caller's
    entries own that frame in their normal form [bv_unsigned sp - d - ...]. Where the claim is
    asked inside an owned uninitialized region (its bounds justify the conversion, as for a stack
    write), the step states [bv_unsigned (bv_add sp c) = bv_unsigned sp - |c|] and rewrites the
    whole goal: the claim, the frame the callee returns (in the same goal) and any context
    resource then share the entries' normal form, so the return site's frame is found by its
    address. *)
Ltac zesu_frame_claim_arithmetic :=
  first [ZesuSsz.Automation2.MemoryAddress.zesu_stack_arithmetic |
    ZesuSsz.Automation2.PureFacts.zesu_saturate_derived_facts;
    ZesuSsz.Automation2.MemoryAddress.zesu_stack_arithmetic].

Ltac zesu_frame_claim_address :=
  lazymatch goal with
  | |- envs_entails _ ((?address ↦ₘ? _) ∗ _)%I =>
    match address with
    | context [bv_unsigned (bv_add ?base ?offset)] =>
        ZesuSsz.Automation2.VmClosed.zesu_vm_closed offset;
        let displacement := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (bv_signed offset) in
        lazymatch displacement with Zneg _ => idtac end;
        let distance := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (Z.opp displacement) in
        iMatchHyp ltac:(fun _ body =>
          lazymatch body with
          | (?lower ↦ₘ? ?count)%I =>
              let Heq := fresh "HframeClaimAddress" in
              assert (Heq : bv_unsigned (bv_add base offset) = (bv_unsigned base - distance)%Z)
                by zesu_frame_claim_arithmetic;
              let Hbound := fresh "HframeClaimRegion" in
              assert (Hbound : (lower <= address < lower + count)%Z)
                by (rewrite Heq; zesu_frame_claim_arithmetic);
              clear Hbound; rewrite Heq; clear Heq
          end)
    end
  end.

(** The frame the callee returned: it comes back in the context at the callee's claim form
    [bv_unsigned (bv_add sp c) - k] (the callee's spec, after the claim step rewrote the goal),
    while the caller's entry asks for the same region in its normal form. When a requested
    [↦ₘ?] region of the same size is that context region up to the stack arithmetic, the step
    states the equation and rewrites the context resource to the requested address. *)
Ltac zesu_frame_return_address :=
  lazymatch goal with
  | |- envs_entails _ ((?address ↦ₘ? ?count) ∗ _)%I =>
    iMatchHyp ltac:(fun H body =>
      lazymatch body with
      | (?owned ↦ₘ? count)%I =>
        tryif constr_eq owned address then fail else idtac;
        match owned with
        | context [bv_unsigned (bv_add ?base ?offset)] =>
            ZesuSsz.Automation2.VmClosed.zesu_vm_closed offset;
            let displacement := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (bv_signed offset) in
            lazymatch displacement with Zneg _ => idtac end;
            let distance := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (Z.opp displacement) in
            let Heq := fresh "HframeReturnAddress" in
            assert (Heq : bv_unsigned (bv_add base offset) = (bv_unsigned base - distance)%Z)
              by zesu_frame_claim_arithmetic;
            let Hsame := fresh "HframeReturnSame" in
            assert (Hsame : owned = address) by (rewrite Heq; zesu_frame_claim_arithmetic);
            clear Heq; iEval (rewrite Hsame) in H; clear Hsame
        end
      end)
  end.

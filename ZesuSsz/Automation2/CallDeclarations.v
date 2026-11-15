(** Call-site declarations: what a call's own block states about the call.

    The generator (tools/block/call_boundary.py, call_site_declarations) states, in the entry of
    the block that ends in call k, the call's input slice under the names the return site uses:

      ⌜zesu_named_eq callk_input_offset OFF⌝ ∗ ⌜zesu_named_eq callk_input_length LEN⌝ ∗
      ⌜zesu_named_eq callk_input (take (Z.to_nat callk_input_length)
                                      (drop (Z.to_nat callk_input_offset) BYTES))⌝ ∗
      ⌜0 <= callk_input_offset /\ 0 <= callk_input_length /\
       callk_input_offset + callk_input_length <= Z.of_nat (length BYTES)⌝ ∗
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
   piece's address to [base + off]; the owned whole array pays for the piece and the wand. *)
Lemma zesu_tac_lend_declared_slice Δ (base address off len : Z) (bytes : list (bv 8)) (R : iProp Sigma) :
  envs_entails Δ (⌜((0 <= off /\ 0 <= len /\ off + len <= Z.of_nat (List.length bytes)) /\
                    base + off = address)%Z⌝ ∗ (base ↦ₘ∗ bytes ∗ R)) ->
  envs_entails Δ (⌜(0 <= off /\ 0 <= len /\ off + len <= Z.of_nat (List.length bytes))%Z⌝ ∗
    ((address ↦ₘ∗ take (Z.to_nat len) (drop (Z.to_nat off) bytes)) ∗
     (((address ↦ₘ∗ take (Z.to_nat len) (drop (Z.to_nat off) bytes)) -∗ base ↦ₘ∗ bytes) ∗ R))).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "[%Hfacts [Hbytes $]]".
  destruct Hfacts as [(Hoff & Hlen & Hend) <-].
  iDestruct (zesu_byte_array_lend_declared base off len bytes with "Hbytes") as "[$ $]"; done.
Qed.

(* The same inside Lithium's packed binders, when the entry's remaining binders are still open
   (the declaration mentions none of them). *)
Lemma zesu_tac_lend_declared_slice_ex {A B} Δ (base address off len : Z) (bytes : list (bv 8))
    (R : A *ₗ B → iProp Sigma) :
  envs_entails Δ (⌜((0 <= off /\ 0 <= len /\ off + len <= Z.of_nat (List.length bytes)) /\
                    base + off = address)%Z⌝ ∗ (base ↦ₘ∗ bytes ∗ ∃ₗ x, R x)) ->
  envs_entails Δ (∃ₗ x, ⌜(0 <= off /\ 0 <= len /\ off + len <= Z.of_nat (List.length bytes))%Z⌝ ∗
    ((address ↦ₘ∗ take (Z.to_nat len) (drop (Z.to_nat off) bytes)) ∗
     (((address ↦ₘ∗ take (Z.to_nat len) (drop (Z.to_nat off) bytes)) -∗ base ↦ₘ∗ bytes) ∗ R x))).
Proof.
  rewrite envs_entails_unseal => ->. iIntros "[%Hfacts [Hbytes [%x HR]]]". iExists x.
  destruct Hfacts as [(Hoff & Hlen & Hend) <-].
  iDestruct (zesu_byte_array_lend_declared base off len bytes with "Hbytes") as "[$ $]"; done.
Qed.
End zesu_call_declarations.

Ltac zesu_lend_declared_call_input :=
  lazymatch goal with
  | |- envs_entails _ (bi_sep (bi_pure (_ /\ _ /\ _))
         (bi_sep (_ ↦ₘ∗ take _ (drop _ _)) (bi_sep (bi_wand (_ ↦ₘ∗ _) (_ ↦ₘ∗ _)) _))) =>
      notypeclasses refine (zesu_tac_lend_declared_slice _ _ _ _ _ _ _ _)
  | |- envs_entails _ (@bi_exist _ (li_prod _ _) (λ x, bi_sep (bi_pure (_ /\ _ /\ _))
         (bi_sep (_ ↦ₘ∗ take _ (drop _ _)) (bi_sep (bi_wand (_ ↦ₘ∗ _) (_ ↦ₘ∗ _)) (@?R x))))) =>
      notypeclasses refine (zesu_tac_lend_declared_slice_ex _ _ _ _ _ _ _ _)
  end.

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

(* The whole array a goal asks for, from the declared wand and the piece the call returned. *)
Ltac zesu_restore_declared_call_input :=
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

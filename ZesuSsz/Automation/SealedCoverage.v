(* C3: open a sealed predicate, lazily, and only the one that holds the
   address.

   A boundary seals its resources behind `Global Opaque` so that the frame
   the proof search sees stays inside rule 20's cap of twelve conjuncts.
   That is why the automation stops: the word a block loads is inside the
   seal, so no array is visible in the context and every rule that hunts
   for one fails. Post-withdrawals is the first case -- its word at
   `sp + 1136` lives in `writeSuccessExactPostWithdrawalsUntouched`.

   Opening every seal at block entry would give the search back the wide
   frame the seals were introduced to remove. So the rule is lazy: it
   fires only when a lookup has already failed, opens only the one bundle
   whose declared coverage contains the address, and then the lookup is
   retried. A bundle that does not cover the address is left sealed.

   Coverage is declared, not guessed: one `ZesuSealed` instance per sealed
   predicate, carrying its unfolded form, the address ranges it holds and
   the registers it holds. The instances sit beside the `_unfold` lemmas --
   `tools/det/gen_coverage.py` emits them for `Interfaces.v`, and the
   segment generator emits one for every boundary it produces. *)

Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.isla.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
From Coq Require Import Lists.List Strings.String.
Import ListNotations.

Definition zesu_range := (Z * Z)%type.

Definition zesu_range_holds (range : zesu_range) (address : Z) : bool :=
  Z.leb (fst range) address && Z.ltb address (snd range).

Definition zesu_ranges_hold (ranges : list zesu_range) (address : Z) : bool :=
  existsb (fun range => zesu_range_holds range address) ranges.

Section sealed.
  Context `{!islaG Sigma} `{!threadG}.

  (* `sealed` is equivalent to `unfolded`, and holds the memory in
     `ranges` and the registers in `registers`. The equivalence is the
     predicate's own `_unfold` lemma. *)
  Class ZesuSealed (sealed unfolded : iProp Sigma)
      (ranges : list zesu_range) (registers : list string) : Prop :=
    zesu_sealed_unfold : sealed ⊣⊢ unfolded.

  (* A seal whose body carries an abstract `iProp` parameter cannot state
     what it holds: the parameter may hold anything. Claiming a narrow
     range for it would be a false declaration, and claiming everything
     would give up the laziness. So it is a second tier, tried only after
     every declared coverage has been checked and none matched. *)
  Class ZesuSealedOpaqueTail (sealed unfolded : iProp Sigma) : Prop :=
    zesu_sealed_opaque_unfold : sealed ⊣⊢ unfolded.

End sealed.

(* Fire only after a lookup failed, and open only the bundle that covers
   the address. `iSelect` walks the spatial context; the first hypothesis
   whose type resolves a `ZesuSealed` instance whose ranges hold the
   address is rewritten in place, and nothing else is touched. *)
(* `iMatchHyp` walks the whole context and backtracks; `iSelect _` offers
   only its last match and stops, which is no search at all. *)
Ltac zesu_open_declared_cover address :=
  iMatchHyp ltac:(fun H sealed =>
    let instance := constr:(_ : ZesuSealed sealed _ _ _) in
    lazymatch type of instance with
    | ZesuSealed _ _ ?ranges _ =>
        lazymatch eval vm_compute in (zesu_ranges_hold ranges address) with
        | true =>
            iEval (rewrite (zesu_sealed_unfold (ZesuSealed := instance))) in H
        end
    end).

(* The register half of the same declaration. A bundle says which
   registers it holds, so a register lookup that failed can open the one
   bundle that holds it and leave every other sealed. *)
Ltac zesu_open_declared_cover_register register :=
  iMatchHyp ltac:(fun H sealed =>
    let instance := constr:(_ : ZesuSealed sealed _ _ _) in
    lazymatch type of instance with
    | ZesuSealed _ _ _ ?registers =>
        lazymatch eval vm_compute in
          (existsb (String.eqb register) registers) with
        | true =>
            iEval (rewrite (zesu_sealed_unfold (ZesuSealed := instance))) in H
        end
    end).

Ltac zesu_open_opaque_tail :=
  iMatchHyp ltac:(fun H sealed =>
    let instance := constr:(_ : ZesuSealedOpaqueTail sealed _) in
    iEval (rewrite (zesu_sealed_opaque_unfold
                     (ZesuSealedOpaqueTail := instance))) in H).

(* A transparent bundle is not a seal: `LithiumUnfold` says the search may
   look inside it anywhere, and Lithium does so in the goal. In the
   context it does not, because the split step matches `_ ∗ _`
   syntactically and a definition applied to its arguments is not that.
   So a lookup can fail with the word one delta step away.

   The chain under post-withdrawals is four such steps deep:
   `…CallerFrameRaw`, `…CallerFrameRestRaw`, `…MemoryFrame`,
   `writeSuccessExactValueMemory`, and only the last one names the array
   the block reads from. Unfolding them at block entry is the eager
   opening rule 20 forbids; unfolding one of them after a lookup has
   already failed is the same laziness the sealed tiers have. *)
Ltac zesu_open_transparent_bundle :=
  iMatchHyp ltac:(fun H body =>
    let head := get_head body in
    let _ := constr:(_ : LithiumUnfold head) in
    iEval (progress unfold head; cbv zeta) in H).

(* The same tier, aimed. A register lookup names no range, so the
   untargeted tier has nothing to steer by and opens whichever bundle
   comes first: measured on tail fields 2, that took the frame from 47
   to 139 and the probe from 21 seconds to 105. Opening only a bundle
   that turns out to hold the register keeps the frame where it was:
   `iMatchHyp` backtracks the unfold when the guard fails, so a bundle
   that does not hold it is left exactly as it was. *)
Ltac zesu_open_transparent_bundle_with_register register :=
  iMatchHyp ltac:(fun H body =>
    let head := get_head body in
    let _ := constr:(_ : LithiumUnfold head) in
    iEval (progress unfold head; cbv zeta) in H;
    lazymatch goal with
    | |- context [(register ↦ᵣ _)%I] => idtac
    end).

Ltac zesu_open_sealed_covering address :=
  first [zesu_open_declared_cover address
        |zesu_open_opaque_tail
        |zesu_open_transparent_bundle].

Ltac zesu_open_sealed_for_lookup :=
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      zesu_open_sealed_covering address
  (* A register lookup fails for the same reason a word lookup does: the
     register is inside a bundle nobody opened. The declared coverage
     names the registers as well as the ranges. *)
  | |- envs_entails _ (find_in_context (FindRegMapsTo ?register) _) =>
      first [zesu_open_declared_cover_register register
            |zesu_open_transparent_bundle_with_register register
            |zesu_open_opaque_tail]
  (* A handover states the word through the bound variable, so the
     address cannot be read out from under the binder and there is no
     coverage to check against. Only the opaque tier applies here, and it
     is still lazy: the goal has already stalled. *)
  | |- envs_entails _ (@bi_exist _ (li_prod (bv 64) unit) _) =>
      first [zesu_open_opaque_tail | zesu_open_transparent_bundle]
  end;
  (* An opened seal arrives as one conjunction. The block's introduction
     phase splits what it is given at entry; a seal opened later has to
     be split here, or the resources inside stay invisible. *)
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".

Ltac zesu_open_sealed_for_lookup_if_enabled :=
  zesu_rule_set_v2_on; zesu_open_sealed_for_lookup.

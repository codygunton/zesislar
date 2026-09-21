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

Require Import ZesuSsz.Automation.Finish.
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

Ltac zesu_open_opaque_tail :=
  iMatchHyp ltac:(fun H sealed =>
    let instance := constr:(_ : ZesuSealedOpaqueTail sealed _) in
    iEval (rewrite (zesu_sealed_opaque_unfold
                     (ZesuSealedOpaqueTail := instance))) in H).

Ltac zesu_open_sealed_covering address :=
  first [zesu_open_declared_cover address | zesu_open_opaque_tail].

Ltac zesu_open_sealed_for_lookup :=
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      zesu_open_sealed_covering address
  (* A handover states the word through the bound variable, so the
     address cannot be read out from under the binder and there is no
     coverage to check against. Only the opaque tier applies here, and it
     is still lazy: the goal has already stalled. *)
  | |- envs_entails _ (@bi_exist _ (li_prod (bv 64) unit) _) =>
      zesu_open_opaque_tail
  end;
  (* An opened seal arrives as one conjunction. The block's introduction
     phase splits what it is given at entry; a seal opened later has to
     be split here, or the resources inside stay invisible. *)
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".

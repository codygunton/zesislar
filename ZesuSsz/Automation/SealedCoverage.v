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
Require Import ZesuSsz.Automation.BoundedArithmetic.
Require Import ZesuSsz.Automation.UninitRegions.
Require Import ZesuSsz.Automation.Hooks.
Require Import isla.isla.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments tactics.
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
Ltac zesu_closed_coverage_term value :=
  assert_fails (is_var value);
  assert_fails (is_evar value);
  lazymatch value with
  | (fun _ => _) => fail
  | ?function ?argument =>
      zesu_closed_coverage_term function;
      zesu_closed_coverage_term argument
  | _ => idtac
  end.

Ltac zesu_declared_range_arithmetic ranges address :=
  lazymatch ranges with
  | (?lower, ?upper) :: ?rest =>
      first [let Hcoverage := fresh "Hcoverage" in
             assert (Hcoverage : (lower <= address < upper)%Z)
               by (timeout 2 (first [zesu_finish_lia | bv_solve]));
             clear Hcoverage
            | zesu_declared_range_arithmetic rest address]
  end.

Ltac zesu_declared_ranges_hold ranges address :=
  tryif zesu_closed_coverage_term (ranges, address)
  then lazymatch eval vm_compute in (zesu_ranges_hold ranges address) with
       | true => idtac
       end
  else zesu_declared_range_arithmetic ranges address.


Ltac zesu_open_declared_cover address :=
  iMatchHyp ltac:(fun H sealed =>
    let instance := constr:(_ : ZesuSealed sealed _ _ _) in
    lazymatch type of instance with
    | ZesuSealed _ ?raw ?ranges _ =>
        zesu_declared_ranges_hold ranges address;
        let head := get_head raw in
        iEval (rewrite (zesu_sealed_unfold (ZesuSealed := instance))) in H;
        lazymatch head with
        | @mem_mapsto => idtac
        | @mem_mapsto_array => idtac
        | @mem_mapsto_uninit => idtac
        | @bi_sep => idtac
        | _ => iEval (unfold head) in H
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

Ltac zesu_normalize_lookup_address_aliases :=
  repeat lazymatch goal with
  | |- envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      match goal with
      | local := _ : _ |- _ =>
          lazymatch address with context [local] => unfold local end
      end
  end.

Ltac zesu_open_sealed_for_lookup :=
  li_unfold_lets_in_context;
  zesu_normalize_lookup_address_aliases;
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

(* A load handoff exposes its address before choosing the loaded value. *)
Ltac zesu_open_sealed_load_handoff :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?A ?continuation) =>
      let witness := constr:(_ : Inhabited A) in
      let body := eval cbn beta in (continuation inhabitant) in
      let address := lazymatch body with
        | context[(?address ↦ₘ _)%I] => address
        | context[(?address ↦ₘ∗ _)%I] => address
        end in
      iMatchHyp ltac:(fun H sealed =>
        first [let instance := constr:(_ : ZesuSealed sealed _ _ _) in
        lazymatch type of instance with
        | ZesuSealed _ ?raw _ _ =>
            let head := get_head raw in
            let opened := eval unfold head in raw in
            first [lazymatch opened with
                    | context[(?owned ↦ₘ _)%I] => unify owned address
                    end
                  | lazymatch opened with
                    | context[(?owned ↦ₘ∗ _)%I] => unify owned address
                    end];
            iEval (rewrite (zesu_sealed_unfold (ZesuSealed := instance))) in H;
        lazymatch head with
        | @mem_mapsto => idtac
        | @mem_mapsto_array => idtac
        | @mem_mapsto_uninit => idtac
        | @bi_sep => idtac
        | _ => iEval (unfold head) in H
        end
        end
        | let head := get_head sealed in
          let _ := constr:(_ : LithiumUnfold head) in
          let opened := eval unfold head in sealed in
          first [lazymatch opened with
                  | context[(?owned ↦ₘ _)%I] => unify owned address
                  end
                | lazymatch opened with
                  | context[(?owned ↦ₘ∗ _)%I] => unify owned address
                  end];
          iEval (progress unfold head) in H]);
      repeat iDestruct select (_ ∗ _)%I as "[? ?]"
  end.

(* The switch for this one rule. `Automation/Switch.v` provides it
   with every other v2 step; `Automation/Switches/…` provides it
   alone, which is how one benchmark arm measures one rule. *)
Class ZesuStepSealedOpen : Prop := zesu_step_sealed_open : True.

Ltac zesu_step_sealed_open_on :=
  let _ := constr:(_ : ZesuStepSealedOpen) in idtac.

Ltac zesu_open_sealed_for_lookup_if_enabled :=
  zesu_step_sealed_open_on; zesu_open_sealed_for_lookup.

(* A stalled handoff may demand another declaration of the same memory.
   Open the goal declaration and only a matching owned declaration. *)
Ltac zesu_open_declared_memory_goal :=
  lazymatch goal with
  | |- envs_entails _ (?sealed ∗ _)%I =>
      let instance := constr:(_ : ZesuSealed sealed _ _ _) in
      lazymatch type of instance with
      | ZesuSealed _ ?raw _ _ =>
          let head := get_head raw in
          let opened := eval unfold head in raw in
          try (iMatchHyp ltac:(fun H owned =>
            let owner := constr:(_ : ZesuSealed owned _ _ _) in
            lazymatch type of owner with
            | ZesuSealed _ ?ownedRaw _ _ =>
                let ownedHead := get_head ownedRaw in
                let ownedOpened := eval unfold ownedHead in ownedRaw in
                unify ownedOpened opened;
                iEval (rewrite (zesu_sealed_unfold (ZesuSealed := owner)); unfold ownedHead) in H
            end));
          iEval (rewrite (zesu_sealed_unfold (ZesuSealed := instance)));
          iEval (unfold head);
          repeat iDestruct select (_ ∗ _)%I as "[? ?]"
      end
  end.
Ltac zesu_open_declared_memory_for_raw_goal :=
  lazymatch goal with
  | |- envs_entails _ (?atom ∗ _)%I =>
      let head := get_head atom in
      lazymatch head with
      | @mem_mapsto => idtac
      | @mem_mapsto_array => idtac
      | @mem_mapsto_uninit => idtac
      end;
      iMatchHyp ltac:(fun H owned =>
        let owner := constr:(_ : ZesuSealed owned _ _ _) in
        lazymatch type of owner with
        | ZesuSealed _ ?raw _ _ =>
            let rawHead := get_head raw in
            let opened := eval unfold rawHead in raw in
            lazymatch opened with
            | (?first ∗ _)%I => unify first atom
            | _ => unify opened atom
            end;
            iEval (rewrite (zesu_sealed_unfold (ZesuSealed := owner)); unfold rawHead) in H
        end);
      repeat iDestruct select (_ ∗ _)%I as "[? ?]"
  end.

Ltac zesu_with_uninit_target body action :=
  lazymatch body with
  | (?address ↦ₘ? ?size)%I => action address size
  | (?left ∗ ?right)%I => first [zesu_with_uninit_target left action | zesu_with_uninit_target right action]
  end.

Ltac zesu_uninit_requested_range lower upper address size :=
  tryif has_evar (lower, upper, address, size) then fail 0 else idtac;
  let Hrange := fresh "HuninitRange" in
  assert (Hrange : (0 <= size /\ lower <= address /\ address + size <= upper)%Z)
    by zesu_region_bounds;
  clear Hrange.

Ltac zesu_uninit_declared_range ranges address size :=
  lazymatch ranges with
  | (?lower, ?upper) :: ?rest =>
      first [zesu_uninit_requested_range lower upper address size
            | zesu_uninit_declared_range rest address size]
  end.

Ltac zesu_uninit_owned_range body address size :=
  lazymatch body with
  | (?base ↦ₘ? ?count)%I =>
      zesu_uninit_requested_range base (base + count)%Z address size
  | (?left ∗ ?right)%I =>
      first [zesu_uninit_owned_range left address size
            | zesu_uninit_owned_range right address size]
  end.

Ltac zesu_open_declared_uninit_goal :=
  lazymatch goal with
  | |- envs_entails _ ?body =>
      zesu_with_uninit_target body ltac:(fun address size =>
      iMatchHyp ltac:(fun H owned =>
        let owner := constr:(_ : ZesuSealed owned _ _ _) in
        lazymatch type of owner with
        | ZesuSealed _ ?raw ?ranges _ =>
          zesu_uninit_declared_range ranges address size;
          let head := get_head raw in
          let opened := eval unfold head in raw in
          zesu_uninit_owned_range opened address size;
          iEval (rewrite (zesu_sealed_unfold (ZesuSealed := owner)); unfold head) in H
        end));
      repeat iDestruct select (_ ∗ _)%I as "[? ?]"
  end.

Ltac zesu_open_declared_memory_goal_if_enabled :=
  zesu_step_sealed_open_on;
  first [zesu_normalize_uninit_wrapped_address | zesu_open_declared_uninit_goal | zesu_open_declared_memory_goal | zesu_open_declared_memory_for_raw_goal].

Ltac zesu_open_declared_memory_witness_goal :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T ?body) =>
      let witness := zesu_tuple_witness T in
      let instantiated := eval cbv beta in (body witness) in
      lazymatch instantiated with
      | (?sealed ∗ _)%I =>
          let instance := constr:(_ : ZesuSealed sealed _ _ _) in
          iExists witness; red_li_prod;
          zesu_open_declared_memory_goal
      end
  end.
Ltac zesu_open_declared_memory_witness_goal_if_enabled :=
  zesu_step_sealed_open_on; zesu_open_declared_memory_witness_goal.

Ltac zesu_normalize_uninit_wrapped_address_if_enabled :=
  zesu_step_sealed_open_on; zesu_normalize_uninit_wrapped_address.

Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Automation2.Hooks.
From stdpp Require Import bitvector.definitions bitvector.tactics list.
From Coq Require Import ZArith.ZArith NArith.NArith Lia Lists.List.
Local Open Scope Z_scope.
Require Import ZesuSsz.Automation2.ByteArrayLengths.
Require Import ZesuSsz.Automation2.ResourceGroups.
Require Import ZesuSsz.Automation2.RangeFacts.
Require ZesuSsz.Automation2.ByteArrayAssembly.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import iris.proofmode.environments.
Local Open Scope Z_scope.

Class ZesuStepStoreMemoryLookup : Prop := {}.

#[export] Instance zesu_store_integer_address `{ZesuStepStoreMemoryLookup} :
  ZesuSsz.Automation2.Hooks.ZesuStepIntegerArrayAddress := I.
#[export] Instance zesu_store_array_bounds `{ZesuStepStoreMemoryLookup} :
  ZesuSsz.Automation2.Hooks.ZesuStepArrayBounds := I.
#[export] Instance zesu_store_region_bounds `{ZesuStepStoreMemoryLookup} :
  ZesuSsz.Automation2.ByteArrayLengths.ZesuStepArrayRegionBounds := I.

(* Prove each complete address equality before rewriting a splice index.
   The root recognizer rejects symbolic offsets before closed evaluation. *)
Ltac zesu_store_unsigned_splice_indices :=
  repeat multimatch goal with
  | |- context [Z.to_nat (bv_unsigned ?pointer - ?base)] =>
      assert_fails (has_evar pointer);
      assert_fails (has_evar base);
      let expanded := eval cbv beta zeta in pointer in
      ZesuSsz.Automation2.MemoryAddress.zesu_integer_pointer_root expanded
        ltac:(fun _ =>
          let integer := ZesuSsz.Automation2.MemoryAddress.zesu_stack_integer_address expanded in
          let equality := fresh "HstoreUnsignedAddress" in
          assert (equality : bv_unsigned pointer = integer) by
            ZesuSsz.Automation2.MemoryAddress.zesu_stack_arithmetic;
          progress rewrite equality;
          clear equality)
  end.

(* Isolate the proved address and the matching length before linear arithmetic. *)
Ltac zesu_store_selected_linear :=
  cbn [Z.of_N Z.of_nat];
  repeat match goal with
  | |- context [(?left - ?right)%Z] =>
      replace (left - right)%Z with 0%Z by lia
  end;
  rewrite ?Z.sub_diag ?Z.div_1_r ?Z.mod_1_r;
  cbn; solve [lia].

Ltac zesu_store_select_length continuation :=
  match goal with
  | Hlength : List.length ?values = ?count |- context [List.length ?values] =>
      let selected := fresh "HstoreSelectedLength" in
      pose proof Hlength as selected;
      continuation selected
  end.

Ltac zesu_store_splice_bounds :=
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuStepStoreMemoryLookup);
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail 0 "store bounds require a pure side condition"
  | |- SHELVED_SIDECOND _ => unshelve_sidecond
  | _ => idtac
  end;
  first [
    lazymatch goal with
    | |- context [bv_unsigned ?pointer] =>
        let expanded := eval cbv beta zeta in pointer in
        let integer := ZesuSsz.Automation2.MemoryAddress.zesu_stack_integer_address expanded in
        let equality := fresh "HstoreSelectedAddress" in
        assert (equality : bv_unsigned pointer = integer) by
          solve [ZesuSsz.Automation2.RangeFacts.zesu_address_equality];
        rewrite equality;
        first [zesu_store_select_length ltac:(fun selected =>
          clear - equality selected; rewrite selected) | clear - equality];
        zesu_store_selected_linear
    end
  | zesu_store_select_length ltac:(fun selected =>
      clear - selected; rewrite selected; zesu_store_selected_linear)
  | solve [reflexivity] ].

(* Rebase indexed byte cells without changing their addresses or fractions. *)
Lemma zesu_indexed_byte_cells_array `{!islaG Sigma}
    (address : nat -> Z) (base : Z) (q : dfrac) (cells : list (bv 8)) :
  (0 <= base /\ base + Z.of_nat (length cells) <= 2^64) ->
  (forall i, address i = base + Z.of_nat i) ->
  ([∗ list] i ↦ v ∈ cells, mem_mapsto (address i) q v) ⊣⊢
  mem_mapsto_array base q cells.
Proof.
 intros Hbound Haddress. rewrite mem_mapsto_array_eq. iSplit.
 - iIntros "Hcells". iExists 1%N. iSplit; first done.
   cbn [Z.of_N]. iSplit; first (iPureIntro; lia).
   iApply (big_sepL_mono with "Hcells"). intros i v Hlookup.
   rewrite Haddress. replace (Z.of_nat i * 1) with (Z.of_nat i) by lia. done.
 - iIntros "[%len [%Hwidth [%Hrange Hcells]]]".
   assert (len = 1)%N by lia. subst len. cbn [Z.of_N].
   iApply (big_sepL_mono with "Hcells"). intros i v Hlookup.
   rewrite Haddress. replace (Z.of_nat i * 1) with (Z.of_nat i) by lia. done.
Qed.
(* Test the owner before traversing its pure source facts. *)
Ltac zesu_store_has_indexed_byte_tail :=
  iMatchHyp ltac:(fun _ body =>
    multimatch body with
    | context [@big_opL _ _ _ _ ?function ?cells] =>
        let atom := eval cbv beta in (function 0%nat (BV 8 0)) in
        lazymatch atom with @mem_mapsto _ _ 8 _ _ _ => idtac end
    end).

(* Retain the structural length equation; the range bound alone is insufficient. *)
Ltac zesu_store_retain_tail_length cells :=
  ZesuSsz.Automation2.PureFacts.zesu_integer_array_facts;
  let count := fresh "storeTailCount" in
  evar (count : nat);
  let fact := fresh "HstoreTailLength" in
  assert (fact : List.length cells = count) by
    (unfold count;
     repeat progress (rewrite ?skipn_length ?firstn_length ?length_app; cbn [List.length]);
     repeat match goal with
     | Hlength : List.length ?values = ?size |- context [List.length ?values] =>
         progress rewrite Hlength
     end;
     reflexivity);
  unfold count in fact; clear count.

Ltac zesu_store_fold_indexed_byte_tail :=
  zesu_store_has_indexed_byte_tail;
  ZesuSsz.Automation2.ByteArrayAssemblyCodec.zesu_byte_array_normalize_stride;
  iMatchHyp ltac:(fun name body =>
    multimatch body with
    | context [@big_opL _ _ _ _ ?function ?cells] =>
      let atom := eval cbv beta in (function 0%nat (BV 8 0)) in
      lazymatch atom with
      | @mem_mapsto ?Sigma ?heap 8 ?base ?fraction _ =>
        zesu_store_retain_tail_length cells;
        let address := constr:(fun i : nat => ltac:(
          let atom := eval cbv beta in (function i (BV 8 0)) in
          lazymatch atom with @mem_mapsto _ _ 8 ?value _ _ => exact value end)) in
        let base := eval cbn [Z.of_nat Nat.add Nat.mul] in base in
        let Haddress := fresh "HindexedAddress" in
        assert (Haddress : forall i, address i = base + Z.of_nat i) by
          (intro i; cbn [Nat.add Nat.mul]; rewrite ?Nat2Z.inj_succ ?Nat2Z.inj_add; lia);
        let Hbound := fresh "HindexedBound" in
        assert (Hbound : 0 <= base /\ base + Z.of_nat (length cells) <= 2^64) by
          (first [assumption |
            multimatch goal with
            | Hrange : 0 <= ?origin /\ ?upper <= 2^64 |- _ =>
                let Hcopy := fresh "HindexedSourceRange" in
                pose proof Hrange as Hcopy;
                clear - Hcopy;
                cbn [List.length Z.of_N] in Hcopy;
                rewrite ?Nat2Z.inj_succ in Hcopy;
                lia
            end]);
        iEval (rewrite (zesu_indexed_byte_cells_array address base fraction cells Hbound Haddress)) in name;
        clear Haddress Hbound
      end
    end).

(* Derive a lookup from an actual owned image and the public semantic rule.
   The typed root limits candidate selection. The range is still proved. *)
Ltac zesu_store_codec_array_lookup :=
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuStepStoreMemoryLookup);
  ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
  repeat match goal with
  | Hlocal := _ |- environments.envs_entails _
      (find_in_context (FindMemMapsTo ?address) _) =>
      lazymatch address with context[Hlocal] =>
        unfold Hlocal in *; clear Hlocal
      end
  end;
  lazymatch goal with
  | |- environments.envs_entails _
      (find_in_context (FindMemMapsTo (bv_unsigned ?pointer)) _) =>
      let expanded := eval cbv beta zeta in pointer in
      ZesuSsz.Automation2.MemoryAddress.zesu_integer_pointer_root expanded ltac:(fun base =>
        let integer := ZesuSsz.Automation2.MemoryAddress.zesu_stack_integer_address expanded in
        iMatchHyp ltac:(fun name body =>
          lazymatch body with
          | @mem_mapsto_array ?sigma ?heap ?width ?lower ?fraction ?values =>
              assert_fails (has_evar lower);
              assert_fails (has_evar values);
              constr_eq fraction (DfracOwn 1);
              lazymatch lower with context[base] =>
                let sourceIsla := constr:(_ : islaG sigma) in
                constr_eq heap (@islaG_gen_heapG sigma sourceIsla);
                let range := fresh "HownedCodecArrayRange" in
                assert (range : (lower <= integer < lower +
                  Z.of_nat (length values) * Z.of_N (N.div width 8))%Z) by
                  (first [solve [ZesuSsz.Automation2.RangeFacts.zesu_selected_array_range] |
                    cbn [length N.to_nat];
                    repeat (rewrite length_bv_to_little_endian; [|lia]);
                    cbn [length N.to_nat];
                    try (autounfold with zesu_contract_constants);
                    ZesuSsz.Automation2.MemoryAddress.zesu_stack_arithmetic]);
                let found := fresh "HownedArraySemanticLookup" in
                pose proof (@tac_mem_mapsto_array_eq sigma sourceIsla integer
                  width lower integer values (or_introl range)) as found;
                let equality := fresh "HownedArrayReadAddress" in
                assert (equality : bv_unsigned pointer = integer) by
                  (first [solve [ZesuSsz.Automation2.RangeFacts.zesu_address_equality] |
                    ZesuSsz.Automation2.MemoryAddress.zesu_stack_arithmetic]);
                rewrite equality;
                liEnsureInvariant;
                liStep
              end
          end))
  end.

Ltac zesu_store_memory_lookup_core :=
  first [ zesu_store_codec_array_lookup
  | ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
    zesu_store_unsigned_splice_indices;
    progress ZesuSsz.Automation2.Hooks.zesu_integer_array_address_if_enabled;
    liEnsureInvariant;
    liStep ].

(* A wider access to a run of owned byte cells reads the run as one array. *)
Lemma zesu_byte_cells_one `{!islaG Sigma} (base : Z) (index : nat) (fraction : dfrac)
    (byte : bv 8) :
  (base + Z.of_nat index * 1) ↦ₘ{fraction} byte -∗
  (base + Z.of_nat index * 1) ↦ₘ{fraction}∗ (byte :: nil).
Proof. iIntros "Hbyte". rewrite mem_mapsto_array_singleton. iExact "Hbyte". Qed.

Lemma zesu_byte_cells_cons `{!islaG Sigma} (base : Z) (index : nat) (fraction : dfrac)
    (byte : bv 8) (tail : list (bv 8)) :
  (base + Z.of_nat index * 1) ↦ₘ{fraction} byte -∗
  (base + Z.of_nat (S index) * 1) ↦ₘ{fraction}∗ tail -∗
  (base + Z.of_nat index * 1) ↦ₘ{fraction}∗ (byte :: tail).
Proof.
  iIntros "Hbyte Htail".
  iApply (ZesuSsz.Automation2.ByteArrayAssembly.zesu_byte_array_cons with "Hbyte").
  replace (base + Z.of_nat index * 1 + 1) with (base + Z.of_nat (S index) * 1)
    by (rewrite Nat2Z.inj_succ; ring).
  iExact "Htail".
Qed.

Lemma zesu_byte_cells_base `{!islaG Sigma} (address : Z) (fraction : dfrac)
    (bytes : list (bv 8)) :
  (address + Z.of_nat 0 * 1) ↦ₘ{fraction}∗ bytes -∗ address ↦ₘ{fraction}∗ bytes.
Proof.
  iIntros "Hbytes". replace (address + Z.of_nat 0 * 1) with address by (simpl; ring).
  iExact "Hbytes".
Qed.

Lemma zesu_byte_array_join `{!islaG Sigma} (address : Z) (count : nat) (fraction : dfrac)
    (left right : list (bv 8)) :
  length left = count ->
  address ↦ₘ{fraction}∗ left -∗
  (address + Z.of_nat count * 1) ↦ₘ{fraction}∗ right -∗
  address ↦ₘ{fraction}∗ (left ++ right).
Proof.
  iIntros (Hcount) "Hleft Hright".
  iApply (mem_mapsto_array_app_combine_at 8 address fraction left right count Hcount
    with "Hleft [Hright]").
  change (Z.of_N (8 `div` 8)) with 1%Z.
  rewrite Z.mul_1_l Z.mul_1_r. iExact "Hright".
Qed.

(* The byte width of a lookup, read from its single-cell continuation. *)
Ltac zesu_access_width continuation :=
  let probe := eval cbv beta iota in (continuation (MKMapsTo 8%N (BV 8 0))) in
  lazymatch probe with
  | @bi_exist _ (@eq N ?width 8%N) _ => width
  | @bi_sep _ (@bi_pure _ (@eq N 8%N ?width)) _ => width
  end.

Ltac zesu_integer_cell_match integer address :=
  assert_succeeds (assert (integer = address)%Z by (clear; Lia.lia)).

Ltac zesu_name_byte_cell address fraction :=
  iMatchHyp ltac:(fun H body =>
    lazymatch body with
    | @mem_mapsto _ _ 8 ?available ?owned _ =>
        constr_eq available address; constr_eq owned fraction;
        iRename H into "HzesuByteCell"
    end).

Ltac zesu_fold_first_byte_cell base index fraction :=
  zesu_name_byte_cell (base + Z.of_nat index * 1)%Z fraction;
  iDestruct (zesu_byte_cells_one base index fraction with "HzesuByteCell")
    as "HzesuByteRun".

Ltac zesu_fold_next_byte_cell base index fraction :=
  zesu_name_byte_cell (base + Z.of_nat index * 1)%Z fraction;
  iDestruct (zesu_byte_cells_cons base index fraction with "HzesuByteCell HzesuByteRun")
    as "HzesuByteRun".

Ltac zesu_name_byte_array address fraction :=
  iMatchHyp ltac:(fun H body =>
    lazymatch body with
    | @mem_mapsto_array _ _ 8 ?available ?owned _ =>
        constr_eq available address; constr_eq owned fraction;
        iRename H into "HzesuByteNext"
    end).

Ltac zesu_join_byte_run base count fraction :=
  iDestruct (zesu_byte_cells_base base fraction with "HzesuByteRun") as "HzesuByteRun";
  first [
    zesu_name_byte_array (base + Z.of_nat count * 1)%Z fraction;
    let run := iTypeOf (INamed "HzesuByteRun") in
    lazymatch run with
    | Some (_, @mem_mapsto_array _ _ 8 _ _ ?left) =>
        let Hlength := fresh "HzesuRunLength" in
        assert (Hlength : length left = count) by reflexivity;
        iDestruct (zesu_byte_array_join base count fraction left _ Hlength
          with "HzesuByteRun HzesuByteNext") as "HzesuByteRun";
        clear Hlength
    end
  | idtac ];
  iDestruct "HzesuByteRun" as "?".

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Ltac2 zesu_byte_cell_owner (owner : constr) :=
  lazy_match! owner with
  | @mem_mapsto _ _ 8 (?base + Z.of_nat ?index * 1) ?fraction _ => Some (base, index, fraction)
  | _ => None
  end.

Ltac2 rec zesu_spatial_owners (spatial : constr) (found : constr list) :=
  match Constr.Unsafe.kind spatial with
  | Constr.Unsafe.App _ arguments =>
      if Int.equal (Array.length arguments) 4
      then zesu_spatial_owners (Array.get arguments 1) (Array.get arguments 3 :: found)
      else found
  | _ => found
  end.

Ltac2 rec zesu_nat_value (term : constr) :=
  lazy_match! term with
  | O => 0
  | S ?previous => Int.add 1 (zesu_nat_value previous)
  end.

Ltac2 zesu_has_byte_cell (owners : constr list) base index fraction :=
  List.exist (fun owner =>
    match zesu_byte_cell_owner owner with
    | Some cell =>
        let (other, position, owned) := cell in
        Bool.and (Constr.equal other base)
          (Bool.and (Constr.equal position index) (Constr.equal owned fraction))
    | None => false
    end) owners.

(* Find the cell at the integer address, extend it to the maximal run of
   adjacent cells with one fraction, and fold the run when it covers the
   access. Fail without change otherwise. *)
Ltac2 zesu_fold_byte_cells (integer : constr) (count : int) :=
  if Int.le count 1 then Control.zero (Tactic_failure None) else ();
  let spatial := lazy_match! goal with
    | [ |- environments.envs_entails (environments.Envs _ ?spatial _) _ ] => spatial
    end in
  let owners := zesu_spatial_owners spatial [] in
  let matches := List.filter (fun owner =>
    match zesu_byte_cell_owner owner with
    | Some cell =>
        let (base, index, _) := cell in
        match Control.case (fun () =>
          ltac1:(i a |- zesu_integer_cell_match i a) (Ltac1.of_constr integer)
            (Ltac1.of_constr constr:(($base + Z.of_nat $index * 1)%Z))) with
        | Val _ => true
        | Err _ => false
        end
    | None => false
    end) owners in
  match matches with
  | [] => Control.zero (Tactic_failure None)
  | owner :: _ =>
    match zesu_byte_cell_owner owner with
    | None => Control.zero (Tactic_failure None)
    | Some cell =>
      let (base, index, fraction) := cell in
      let rec low current :=
        lazy_match! current with
        | S ?previous => if zesu_has_byte_cell owners base previous fraction
                         then low previous else current
        | O => current
        end in
      let rec high current :=
        let next := constr:(S $current) in
        if zesu_has_byte_cell owners base next fraction then high next else current in
      let first := low index in
      let last := high index in
      if Int.lt (Int.sub (zesu_nat_value last) (zesu_nat_value index)) (Int.sub count 1)
      then Control.zero (Tactic_failure None) else ();
      ltac1:(b i q |- zesu_fold_first_byte_cell b i q)
        (Ltac1.of_constr base) (Ltac1.of_constr last) (Ltac1.of_constr fraction);
      let rec down current :=
        if Constr.equal current first then () else
        lazy_match! current with
        | S ?previous =>
            ltac1:(b i q |- zesu_fold_next_byte_cell b i q)
              (Ltac1.of_constr base) (Ltac1.of_constr previous) (Ltac1.of_constr fraction);
            down previous
        end in
      down last;
      ltac1:(iDestruct "HzesuByteRun" as "?")
    end
  end.

Ltac2 rec zesu_array_requests (term : constr) (found : (constr * constr) list) :=
  let found := lazy_match! term with
    | @mem_mapsto_array _ _ 8 ?address ?fraction _ => (address, fraction) :: found
    | _ => found
    end in
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head arguments =>
      Array.fold_left (fun found argument => zesu_array_requests argument found)
        (zesu_array_requests head found) arguments
  | Constr.Unsafe.Lambda _ body => zesu_array_requests body found
  | Constr.Unsafe.Prod _ body => zesu_array_requests body found
  | _ => found
  end.

Ltac2 zesu_has_byte_array (owners : constr list) address fraction :=
  List.exist (fun owner =>
    lazy_match! owner with
    | @mem_mapsto_array _ _ 8 ?available ?owned _ =>
        Bool.and (Constr.equal available address) (Constr.equal owned fraction)
    | _ => false
    end) owners.

(* A frame that requests an array at an address owned as byte cells from
   index zero receives the cells, and an array right after them, as one array. *)
Ltac2 zesu_join_frame_byte_array () :=
  let (spatial, conclusion) := lazy_match! goal with
    | [ |- environments.envs_entails (environments.Envs _ ?spatial _) ?conclusion ] =>
        (spatial, conclusion)
    end in
  let owners := zesu_spatial_owners spatial [] in
  let requests := zesu_array_requests conclusion [] in
  let candidates := List.filter (fun request =>
    let (address, fraction) := request in
    Bool.and (zesu_has_byte_cell owners address constr:(O) fraction)
      (Bool.neg (zesu_has_byte_array owners address fraction))) requests in
  match candidates with
  | [] => Control.zero (Tactic_failure None)
  | request :: _ =>
      let (base, fraction) := request in
      let rec high current :=
        let next := constr:(S $current) in
        if zesu_has_byte_cell owners base next fraction then high next else current in
      let last := high constr:(O) in
      ltac1:(b i q |- zesu_fold_first_byte_cell b i q)
        (Ltac1.of_constr base) (Ltac1.of_constr last) (Ltac1.of_constr fraction);
      let rec down current :=
        lazy_match! current with
        | O => ()
        | S ?previous =>
            ltac1:(b i q |- zesu_fold_next_byte_cell b i q)
              (Ltac1.of_constr base) (Ltac1.of_constr previous) (Ltac1.of_constr fraction);
            down previous
        end in
      down last;
      ltac1:(b n q |- zesu_join_byte_run b n q)
        (Ltac1.of_constr base) (Ltac1.of_constr constr:(S $last)) (Ltac1.of_constr fraction)
  end.

Ltac zesu_join_frame_byte_array := ltac2:(zesu_join_frame_byte_array ()).

Ltac zesu_store_fold_byte_cells :=
  try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
  repeat match goal with
  | Hlocal := _ |- environments.envs_entails _
      (find_in_context (FindMemMapsTo ?address) _) =>
      lazymatch address with context[Hlocal] =>
        unfold Hlocal in *; clear Hlocal
      end
  end;
  lazymatch goal with
  | |- environments.envs_entails _
      (find_in_context (FindMemMapsTo (bv_unsigned ?pointer)) ?continuation) =>
      let width := zesu_access_width continuation in
      let count := eval vm_compute in (N.to_nat (width / 8)) in
      let expanded := eval cbv beta zeta in pointer in
      let integer := ZesuSsz.Automation2.MemoryAddress.zesu_stack_integer_address expanded in
      let run := ltac2:(z n |- zesu_fold_byte_cells (Option.get (Ltac1.to_constr z))
        (zesu_nat_value (Option.get (Ltac1.to_constr n)))) in
      run integer count
  end.

Ltac zesu_store_memory_lookup :=
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuStepStoreMemoryLookup);
  first [ zesu_store_memory_lookup_core
  | lazymatch goal with
    | |- environments.envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac
    end;
    progress (zesu_store_fold_indexed_byte_tail;
      ZesuSsz.Automation2.ResourceGroups.zesu_open_resource_groups)
  | zesu_store_fold_byte_cells ].

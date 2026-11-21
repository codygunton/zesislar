Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Automation2.Hooks.
From stdpp Require Import bitvector.definitions bitvector.tactics list.
From Coq Require Import ZArith.ZArith NArith.NArith Lia Lists.List.
Require Import ZesuSsz.Automation2.LiaHook.
Local Open Scope Z_scope.
Require Import ZesuSsz.Automation2.ByteArrayLengths.
Require Import ZesuSsz.Automation2.ResourceGroups.
Require Import ZesuSsz.Automation2.RangeFacts.
Require ZesuSsz.Automation2.ByteArrayAssembly.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require ZesuSsz.Automation2.WrappedWord.
Require ZesuSsz.Automation2.CallSlice.
Require ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.ByteExtractCodec281.
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
      replace (left - right)%Z with 0%Z by zesu_lia
  end;
  rewrite ?Z.sub_diag ?Z.div_1_r ?Z.mod_1_r;
  cbn; solve [zesu_lia].

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
          (intro i; cbn [Nat.add Nat.mul]; rewrite ?Nat2Z.inj_succ ?Nat2Z.inj_add; zesu_lia);
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
                zesu_lia
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
                    repeat (rewrite length_bv_to_little_endian; [|zesu_lia]);
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
  assert_succeeds (assert (integer = address)%Z by (clear; zesu_lia)).

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
  let (environment, conclusion) := lazy_match! goal with
    | [ |- environments.envs_entails ?environment ?conclusion ] => (environment, conclusion)
    end in
  (* Lithium keeps the environment as a local definition; read through it. *)
  let environment := match Constr.Unsafe.kind environment with
    | Constr.Unsafe.Var name =>
        match List.find_opt (fun hypothesis =>
          let (other, _, _) := hypothesis in Ident.equal other name) (Control.hyps ()) with
        | Some (_, Some body, _) => body
        | _ => environment
        end
    | _ => environment
    end in
  let spatial := lazy_match! environment with
    | environments.Envs _ ?spatial _ => spatial
    end in
  let owners := zesu_spatial_owners spatial [] in
  (* Scan the goal only when the context owns a byte cell at index zero. *)
  if List.exist (fun owner =>
       match zesu_byte_cell_owner owner with
       | Some cell => let (_, index, _) := cell in Constr.equal index constr:(O)
       | None => false
       end) owners
  then () else Control.zero (Tactic_failure None);
  let requests := zesu_array_requests conclusion [] in
  let candidates := List.filter (fun request =>
    let (address, fraction) := request in
    Bool.and (zesu_has_byte_cell owners address constr:(O) fraction)
      (Bool.neg (zesu_has_byte_array owners address fraction))) requests in
  match candidates with
  | [] => Control.zero (Tactic_failure None)
  | request :: _ =>
      let (base, fraction) := request in
      ltac1:(try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias);
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

(* Frame join: the successor asks for one byte array at an address where the
   block holds a run of cells, uninitialised pieces and byte arrays. *)
Lemma zesu_cell_bytes `{!islaG Sigma} (len : N) (a : Z) q (value : bv (8 * len)) :
  a ↦ₘ{q} value -∗
  a ↦ₘ{q}∗ bv_to_little_endian (N.to_nat len) 8 (bv_unsigned value) ∗
  ⌜Z.of_nat (length (bv_to_little_endian (N.to_nat len) 8 (bv_unsigned value))) = Z.of_N len⌝.
Proof.
  iIntros "H".
  iDestruct (ZesuSsz.Contracts.IslarisMemory.mem_mapsto_mapsto_to_byte_array_N with "H") as "$".
  iPureIntro. rewrite length_bv_to_little_endian; ZesuSsz.Automation2.WrappedWord.zesu_plain_lia.
Qed.
Lemma zesu_uninit_bytes `{!islaG Sigma} (a n m : Z) q :
  n = m -> a ↦ₘ{q}? n -∗ ∃ values : list (bv 8), ⌜Z.of_nat (length values) = m⌝ ∗ a ↦ₘ{q}∗ values.
Proof. intros ->. iApply ZesuSsz.Contracts.IslarisMemory.mem_mapsto_uninit_to_byte_array. Qed.
Lemma zesu_byte_array_join_sized `{!islaG Sigma} (a a2 : Z) q (left right : list (bv 8)) (n m s : Z) :
  Z.of_nat (length left) = n -> Z.of_nat (length right) = m -> a2 = a + n -> s = n + m ->
  a ↦ₘ{q}∗ left -∗ a2 ↦ₘ{q}∗ right -∗
  a ↦ₘ{q}∗ (left ++ right) ∗ ⌜Z.of_nat (length (left ++ right)) = s⌝.
Proof.
  iIntros (Hn Hm -> ->) "Hl Hr".
  iSplitL; [|iPureIntro; rewrite length_app; ZesuSsz.Automation2.WrappedWord.zesu_plain_lia].
  iApply (ZesuSsz.Contracts.IslarisMemory.mem_mapsto_array_app_combine 8 with "Hl").
  replace (a + Z.of_N (8 `div` 8) * Z.of_nat (length left)) with (a + n); [done|].
  subst n. change (Z.of_N (8 `div` 8)) with 1. ZesuSsz.Automation2.WrappedWord.zesu_plain_lia.
Qed.

(* The number of elements of an explicit list spine; fails on any other list. *)
Ltac zesu_spine_length l :=
  lazymatch l with
  | nil => constr:(O)
  | cons _ ?t => let n := zesu_spine_length t in constr:(S n)
  end.

(* One piece at an address accepted by [a2pred] as a byte array "HzesuPiece"
   with its length fact; [k] receives the address, the length and the fact. *)
Ltac zesu_piece_bytes ra a2pred k :=
  iMatchHyp ltac:(fun H res =>
    lazymatch res with
    | (?a2 ↦ₘ ?v)%I =>
        a2pred a2;
        lazymatch type of v with
        | bv ?w =>
          let len := eval vm_compute in (w / 8)%N in
          let m := eval vm_compute in (Z.of_N len) in
          iRename H into "HzesuPiece";
          let Hl := fresh "HpieceLength" in
          iDestruct (zesu_cell_bytes len a2 with "HzesuPiece") as "[HzesuPiece HzesuPure]";
          iDestruct "HzesuPure" as %Hl;
          change (Z.of_N len) with m in Hl;
          k a2 m Hl
        end
    | (?a2 ↦ₘ? ?m0)%I =>
        a2pred a2;
        let m := ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root ra m0 in
        lazymatch m with Zpos _ => idtac end;
        let Hm := fresh "HregionSize" in
        assert (Hm : m0 = m) by (clear; ZesuSsz.Automation2.WrappedWord.zesu_plain_lia);
        iRename H into "HzesuPiece";
        let values := fresh "pieceBytes" in
        let Hl := fresh "HpieceLength" in
        iDestruct (zesu_uninit_bytes a2 m0 m _ Hm with "HzesuPiece") as (values) "[HzesuPure HzesuPiece]";
        iDestruct "HzesuPure" as %Hl;
        clear Hm;
        (* the length of the new byte list, in the form the length steps read *)
        let c := eval vm_compute in (Z.to_nat m) in
        let Hn := fresh "HpieceBytesLength" in
        assert (Hn : length values = c) by (apply Nat2Z.inj; rewrite Hl; reflexivity);
        k a2 m Hl
    | (?a2 ↦ₘ∗ ?l2)%I =>
        a2pred a2;
        let Hl := fresh "HpieceLength" in
        (* the length as a numeral: a [length] fact at any element type, its
           [Z.of_nat] form, or the spine of an explicit list *)
        first
        [ match goal with
          | Hlen : length l2 = ?c |- _ =>
              let m := eval vm_compute in (Z.of_nat c) in
              assert (Hl : Z.of_nat (length l2) = m) by exact (f_equal Z.of_nat Hlen)
          end
        | match goal with
          | Hlen : Z.of_nat (length l2) = ?m |- _ =>
              lazymatch m with Z0 => idtac | Zpos _ => idtac end;
              assert (Hl : Z.of_nat (length l2) = m) by exact Hlen
          end
        | let c := zesu_spine_length l2 in
          let m := eval vm_compute in (Z.of_nat c) in
          assert (Hl : Z.of_nat (length l2) = m) by reflexivity ];
        lazymatch type of Hl with
        | _ = ?m => iRename H into "HzesuPiece"; k a2 m Hl
        end
    end).

(* [a2] lies at offset [n] (a numeral) from [a], both built on root [ra]:
   the difference is computed only when, the root abstracted, it is closed. *)
Ltac zesu_root_offset_is ra a a2 n :=
  let r2 := ZesuSsz.Automation2.WrappedWord.zesu_term_root a2 in constr_eq ra r2;
  lazymatch eval pattern ra in ((a2 - a)%Z) with
  | ?g _ => assert_fails (idtac; match g with context [?v] => is_var v end)
  end;
  let d := ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root ra constr:((a2 - a)%Z) in
  constr_eq d n.

(* Join every adjacent piece on root [ra] after the run "HzesuRun" of [n]
   bytes at [a]. A piece starting inside the run (an overlap) or after its
   end (a gap) is not adjacent: the run ends. *)
Ltac zesu_join_frame_loop ra a n Hlen :=
  first
  [ zesu_piece_bytes ra
      ltac:(fun a2 => zesu_root_offset_is ra a a2 n)
      ltac:(fun a2 m Hl =>
        let s := eval vm_compute in (n + m)%Z in
        let Ha := fresh "HpieceAdjacent" in
        assert (Ha : a2 = (a + n)%Z) by (clear; ZesuSsz.Automation2.WrappedWord.zesu_plain_lia);
        let Hlen2 := fresh "HrunLength" in
        iDestruct (zesu_byte_array_join_sized a a2 _ _ _ n m s Hlen Hl Ha eq_refl with "HzesuRun HzesuPiece")
          as "[HzesuRun HzesuPure]";
        iDestruct "HzesuPure" as %Hlen2;
        clear Hlen Hl Ha;
        zesu_join_frame_loop ra a s Hlen2)
  | idtac ].

(* Fold the pieces owned from address [a] on (byte cells, uninitialised
   regions of closed size, byte arrays of numeral length, at element type
   [bv 8] or a definition of it) into the one byte array "HzesuRun", with
   the fact "Z.of_nat (length run) = size" in the context. The first piece
   is the one at offset 0 from [a]; fails when there is none. *)
Ltac zesu_fold_byte_run a :=
  let ra := ZesuSsz.Automation2.WrappedWord.zesu_term_root a in
  zesu_piece_bytes ra
    ltac:(fun a2 => zesu_root_offset_is ra a a2 0%Z)
    ltac:(fun a2 m Hl =>
      iRename "HzesuPiece" into "HzesuRun";
      zesu_join_frame_loop ra a2 m Hl).

(* The requested array's address, under a `∗` head or a Lithium existential head. *)
Ltac zesu_requested_byte_array k :=
  lazymatch goal with
  | |- environments.envs_entails _ (bi_sep (@mem_mapsto_array _ _ 8%N ?a (DfracOwn 1) ?l) _) =>
      lazymatch l with _ :: _ => fail | _ ++ _ => fail | _ => idtac end; k a
  | |- environments.envs_entails _ (@bi_exist _ _ ?body) =>
      lazymatch body with
      | (fun x => bi_sep (@mem_mapsto_array _ _ 8%N ?a (DfracOwn 1) (@?l x)) _) =>
          lazymatch l with
          | (fun _ => _ :: _) => fail | (fun _ => _ ++ _) => fail | _ => idtac end; k a
      end
  end.

(* A cell at the requested address and no array there: the cell and every
   adjacent cell, uninitialised piece and byte array as one array. *)
Ltac zesu_join_frame_run :=
  zesu_requested_byte_array ltac:(fun a =>
      assert_fails (has_evar a);
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      assert_fails (iMatchHyp ltac:(fun H res =>
        lazymatch res with (?a2 ↦ₘ∗ _)%I => constr_eq a a2 end));
      iMatchHyp ltac:(fun H res =>
        lazymatch res with (?a2 ↦ₘ _)%I => constr_eq a a2 end);
      let ra := ZesuSsz.Automation2.WrappedWord.zesu_term_root a in
      zesu_piece_bytes ra ltac:(fun a2 => constr_eq a a2)
        ltac:(fun a2 m Hl =>
          iRename "HzesuPiece" into "HzesuRun";
          zesu_join_frame_loop ra a m Hl);
      iDestruct "HzesuRun" as "?").

(* The run "HzesuRun" of [n] bytes at [a] grown by adjacent pieces until it
   is exactly [K] bytes long; fails when no choice of adjacent pieces reaches
   [K] (a gap, or a piece that would go past it). *)
Ltac zesu_join_frame_loop_upto ra a n K Hlen :=
  first
  [ constr_eq n K
  | lazymatch eval vm_compute in (Z.ltb n K) with true => idtac end;
    zesu_piece_bytes ra
      ltac:(fun a2 => zesu_root_offset_is ra a a2 n)
      ltac:(fun a2 m Hl =>
        let s := eval vm_compute in (n + m)%Z in
        lazymatch eval vm_compute in (Z.leb s K) with true => idtac end;
        let Ha := fresh "HpieceAdjacent" in
        assert (Ha : a2 = (a + n)%Z) by (clear; ZesuSsz.Automation2.WrappedWord.zesu_plain_lia);
        let Hlen2 := fresh "HrunLength" in
        iDestruct (zesu_byte_array_join_sized a a2 _ _ _ n m s Hlen Hl Ha eq_refl with "HzesuRun HzesuPiece")
          as "[HzesuRun HzesuPure]";
        iDestruct "HzesuPure" as %Hlen2;
        clear Hlen Hl Ha;
        zesu_join_frame_loop_upto ra a s K Hlen2) ].

(* The run's bytes are the requested explicit list: by computation on closed
   bytes, else byte by byte with `bv_solve` in a context cleared of every
   proposition. *)
Ltac zesu_run_list_eq :=
  first [ vm_compute; reflexivity
        | repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => clear H end end;
          unfold bv_to_little_endian; simpl; repeat f_equal; bv_solve ].

(* decodeParentHeader 03bc: the successor asks for one byte array at `a`
   spelled as an explicit list of [K] bytes (stored words and zero bytes),
   where the block holds a cell at `a` and no array there. The cell and the
   adjacent cells, uninitialised pieces and byte arrays that make up exactly
   [K] bytes, as one array, once its bytes are shown to be the requested list.
   Without it Lithium's cell-against-array instance asks the bytes after the
   cell as one cell of their whole width. *)
Ltac zesu_join_frame_explicit_at a L :=
  assert_fails (has_evar L);
  let c := zesu_spine_length L in
  let K := eval vm_compute in (Z.of_nat c) in
  try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
  try iEval (rewrite <- isla.ghost_state.mem_mapsto_array_eq);
  assert_fails (iMatchHyp ltac:(fun H res =>
    lazymatch res with (?a2 ↦ₘ∗ _)%I => constr_eq a a2 end));
  let ra := ZesuSsz.Automation2.WrappedWord.zesu_term_root a in
  iMatchHyp ltac:(fun H res =>
    lazymatch res with
    | (?a2 ↦ₘ ?v)%I =>
        constr_eq a a2;
        lazymatch type of v with
        | bv ?w =>
            let len := eval vm_compute in (w / 8)%N in
            let m := eval vm_compute in (Z.of_N len) in
            lazymatch eval vm_compute in (Z.ltb m K) with true => idtac end;
            iRename H into "HzesuRun";
            let Hl := fresh "HpieceLength" in
            iDestruct (zesu_cell_bytes len a with "HzesuRun") as "[HzesuRun HzesuPure]";
            iDestruct "HzesuPure" as %Hl;
            change (Z.of_N len) with m in Hl;
            zesu_join_frame_loop_upto ra a m K Hl
        end
    end);
  lazymatch iTypeOf (INamed "HzesuRun") with
  | Some (_, (_ ↦ₘ∗ ?run)%I) =>
      let E := fresh "HrunBytes" in
      assert (E : run = L) by zesu_run_list_eq;
      iEval (rewrite E) in "HzesuRun"; clear E
  end;
  iDestruct "HzesuRun" as "?".

Ltac zesu_join_frame_explicit :=
  lazymatch goal with
  | |- environments.envs_entails _ (bi_sep (@mem_mapsto_array _ _ 8%N ?a (DfracOwn 1) ?L) _) =>
      zesu_join_frame_explicit_at a L
  | |- environments.envs_entails _ (@bi_exist _ _ (fun x =>
        bi_sep (@mem_mapsto_array _ _ 8%N ?a (DfracOwn 1) ?L) _)) =>
      zesu_join_frame_explicit_at a L
  | |- environments.envs_entails _ (bi_sep (@bi_exist _ _ (fun x =>
        bi_sep (@mem_mapsto_array _ _ 8%N ?a (DfracOwn 1) ?L) _)) _) =>
      zesu_join_frame_explicit_at a L
  | |- environments.envs_entails _ (bi_sep
        (@isla.ghost_state.mem_mapsto_array_def _ _ 8%N ?a (DfracOwn 1) ?L) _) =>
      zesu_join_frame_explicit_at a L
  | |- environments.envs_entails _ (@bi_exist _ _ (fun x =>
        bi_sep (@isla.ghost_state.mem_mapsto_array_def _ _ 8%N ?a (DfracOwn 1) ?L) _)) =>
      zesu_join_frame_explicit_at a L
  | |- environments.envs_entails _ (bi_sep (@bi_exist _ _ (fun x =>
        bi_sep (@isla.ghost_state.mem_mapsto_array_def _ _ 8%N ?a (DfracOwn 1) ?L) _)) _) =>
      zesu_join_frame_explicit_at a L
  end.

(* decodeParentHeader 0514 return slots: the successor asks for one byte
   array at `a` as an explicit list some of whose bytes are its own
   existential (`∃ x : _ *ₗ … *ₗ unit, a ↦ₘ∗ L x ∗ G x`, padding bytes of a
   result struct), where the block holds a cell at `a` and no array there.
   The cell and the adjacent cells, uninitialised pieces and byte arrays that
   make up exactly the requested length are folded into one array (as in
   `zesu_join_frame_explicit_at`), the unknown bytes of the uninitialised
   pieces become variables, and the request's existential is instantiated
   byte by byte with the held bytes. The instantiation is forced: the request
   is the held array itself, so `run = L x` fixes every byte `L x` exposes;
   an existential byte appears as an element (or its `bv_extract 0 8`) and
   gets the held byte at its position; every closed element must be the held
   byte (syntactically, by the low byte of a little-endian word, by closed
   computation, or by `bv_solve` in a context cleared of propositions); a
   component the list does not fix refuses the step. The lemma gives back
   exactly the request at that witness and `G` of it. *)
Lemma zesu_byte_array_exist_inst `{!islaG Sigma} {A : Type} (a : Z) (run : list (bv 8))
    (L : A → list (bv 8)) (G : A → iProp Sigma) (x0 : A) :
  run = L x0 → a ↦ₘ∗ run -∗ G x0 -∗ ∃ x, a ↦ₘ∗ L x ∗ G x.
Proof. intros ->. iIntros "Ha HG". iExists x0. iFrame. Qed.
Lemma zesu_le_word_low_byte (n : N) (b : bv 8) (l : list (bv 8)) :
  (8 <= n)%N -> bv_extract 0 8 (Z_to_bv n (little_endian_to_bv 8 (b :: l))) = b.
Proof.
  intros Hn. apply bv_eq. rewrite bv_extract_unsigned. rewrite Z_to_bv_unsigned.
  unfold little_endian_to_bv. cbn [fmap list_fmap little_endian_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_wrap, bv_modulus in *.
  rewrite Z.shiftr_0_r. bitblast.
Qed.
Lemma zesu_extract_byte_self (k : N) (b : bv 8) : k = 0%N -> bv_extract k 8 b = b.
Proof.
  intros ->. apply bv_eq. rewrite bv_extract_unsigned. rewrite Z.shiftr_0_r.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
(* A requested byte of a word the request spells as a concatenation of
   bytes (`bv_concat n hi lo`, `lo : bv 8`): byte 0 is `lo`, byte k >= 8 is
   byte k - 8 of `hi`. The widths and indices are closed numerals, so the
   premises are closed equations; nothing is computed on the bytes. *)
Lemma zesu_byte_concat_low (l : bv 8) (n m : N) (hi : bv m) (lo : bv 8) :
  n = (m + 8)%N -> l = lo -> l = bv_extract 0 8 (bv_concat n hi lo).
Proof.
  intros Hn ->. apply bv_eq. rewrite bv_extract_unsigned. rewrite bv_concat_unsigned; [|exact Hn].
  pose proof (bv_unsigned_in_range _ lo) as Hlo. pose proof (bv_unsigned_in_range _ hi) as Hhi.
  unfold bv_wrap, bv_modulus in *. rewrite Z.shiftr_0_r. bitblast.
Qed.
Lemma zesu_byte_concat_high (l : bv 8) (n m k k' : N) (hi : bv m) (lo : bv 8) :
  n = (m + 8)%N -> (k' + 8 = k)%N -> l = bv_extract k' 8 hi ->
  l = bv_extract k 8 (bv_concat n hi lo).
Proof.
  intros Hn <- ->. apply bv_eq. rewrite !bv_extract_unsigned. rewrite bv_concat_unsigned; [|exact Hn].
  pose proof (bv_unsigned_in_range _ lo) as Hlo. pose proof (bv_unsigned_in_range _ hi) as Hhi.
  unfold bv_wrap, bv_modulus in *. bitblast. f_equal. lia.
Qed.
Ltac zesu_run_byte_concat k n hi lo :=
  lazymatch type of lo with bv 8 => idtac end;
  lazymatch type of hi with
  | bv ?m =>
      lazymatch eval vm_compute in (N.eqb n (m + 8)%N) with true => idtac end;
      lazymatch eval vm_compute in (N.eqb k 0) with
      | true => change k with 0%N; apply (zesu_byte_concat_low _ n m hi lo eq_refl)
      | false =>
          lazymatch eval vm_compute in (N.leb 8 k) with true => idtac end;
          let k' := eval vm_compute in (k - 8)%N in
          apply (zesu_byte_concat_high _ n m k k' hi lo eq_refl eq_refl)
      end
  end.
Ltac zesu_li_evars A :=
  lazymatch A with
  | li_prod ?B ?C => let e := open_constr:(_ : B) in let r := zesu_li_evars C in constr:(li_pair e r)
  | unit => constr:(tt)
  end.
Ltac zesu_run_spine_vars :=
  lazymatch iTypeOf (INamed "HzesuRun") with
  | Some (_, (_ ↦ₘ∗ ?run)%I) =>
    first [ match goal with
            | H : length ?v = ?c |- _ =>
                is_var v; lazymatch run with context [v] => idtac end;
                lazymatch c with
                | S _ => let b := fresh "pieceByte" in
                         destruct v as [|b v]; [discriminate H|]; simpl in H; apply eq_add_S in H
                | O => destruct v; [clear H|discriminate H]
                end
            end; zesu_run_spine_vars
          | idtac ]
  end.
Ltac zesu_run_byte :=
  match goal with
  | |- _ = ?r => is_evar r; reflexivity
  | |- ?l = bv_extract ?k 8 ?e =>
      is_evar e; unify e l; symmetry; apply zesu_extract_byte_self; vm_compute; reflexivity
  | |- _ = bv_extract ?k 8 (bv_concat ?n ?hi ?lo) =>
      assert_fails (has_evar k); zesu_run_byte_concat k n hi lo; zesu_run_byte
  | |- ?g =>
      assert_fails (has_evar g);
      first [ lazymatch g with ?l = ?r => constr_eq l r end; reflexivity
            | lazymatch g with
              | bv_extract 0 8 (Z_to_bv ?n (little_endian_to_bv 8 (?b :: ?l))) = _ =>
                  rewrite (zesu_le_word_low_byte n b l (proj1 (N.leb_le 8 n) eq_refl))
              end;
              lazymatch goal with |- ?l = ?r => constr_eq l r end; reflexivity
            | ZesuSsz.Automation2.VmClosed.zesu_vm_closed g; vm_compute; reflexivity
            | repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => clear H end end;
              bv_solve ]
  end.
Ltac zesu_run_list_inst :=
  rewrite <- ?byte_extracts_codec281; unfold byte_extracts281;
  repeat match goal with
  | |- context [N.to_nat ?k] =>
      let c := eval vm_compute in (N.to_nat k) in change (N.to_nat k) with c
  end;
  cbn [seq fmap list_fmap app];
  repeat match goal with
  | |- context [(8 * N.of_nat ?i)%N] =>
      let k := eval vm_compute in (8 * N.of_nat i)%N in change (8 * N.of_nat i)%N with k
  end;
  repeat (apply (f_equal2 (@cons _)); [zesu_run_byte|]); reflexivity.
Ltac zesu_join_frame_explicit_exist :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ ?A (fun x =>
        bi_sep (@mem_mapsto_array _ _ 8%N ?a (DfracOwn 1) (@?L x)) (@?G x))) =>
      lazymatch A with li_prod _ _ => idtac end;
      assert_fails (has_evar a);
      let n := eval lazy [length] in (fun x => length (L x)) in
      let K := lazymatch n with (fun _ => ?c) => eval vm_compute in (Z.of_nat c) end in
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      try iEval (rewrite <- isla.ghost_state.mem_mapsto_array_eq);
      assert_fails (iMatchHyp ltac:(fun H res =>
        lazymatch res with (?a2 ↦ₘ∗ _)%I => constr_eq a a2 end));
      let ra := ZesuSsz.Automation2.WrappedWord.zesu_term_root a in
      iMatchHyp ltac:(fun H res =>
        lazymatch res with
        | (?a2 ↦ₘ ?v)%I =>
            constr_eq a a2;
            lazymatch type of v with
            | bv ?w =>
                let len := eval vm_compute in (w / 8)%N in
                let m := eval vm_compute in (Z.of_N len) in
                lazymatch eval vm_compute in (Z.ltb m K) with true => idtac end;
                iRename H into "HzesuRun";
                let Hl := fresh "HpieceLength" in
                iDestruct (zesu_cell_bytes len a with "HzesuRun") as "[HzesuRun HzesuPure]";
                iDestruct "HzesuPure" as %Hl;
                change (Z.of_N len) with m in Hl;
                zesu_join_frame_loop_upto ra a m K Hl
            end
        end);
      zesu_run_spine_vars;
      lazymatch goal with
      | |- environments.envs_entails _ (@bi_exist _ ?A (fun x =>
            bi_sep (@mem_mapsto_array _ _ 8%N ?a (DfracOwn 1) (@?L x)) (@?G x))) =>
      lazymatch iTypeOf (INamed "HzesuRun") with
      | Some (_, (_ ↦ₘ∗ ?run)%I) =>
          let w0 := zesu_li_evars A in
          let Lw := eval cbv beta in (L w0) in
          let Lw := eval cbv [li_fst li_snd] in Lw in
          let E := fresh "HrunBytes" in
          assert (E : run = Lw) by zesu_run_list_inst;
          assert_fails (has_evar w0);
          iApply (zesu_byte_array_exist_inst a run L G w0 E with "HzesuRun");
          clear E
      end end
  end.

(* The goal's head requests a byte array at `a` (any list): tested before the
   environment is read, so the step below costs one match on other goals. *)
Ltac zesu_requested_byte_array_base k :=
  lazymatch goal with
  | |- environments.envs_entails _ (bi_sep (@mem_mapsto_array _ _ 8%N ?a _ _) _) => k a
  | |- environments.envs_entails _ (@bi_exist _ _ ?body) =>
      lazymatch body with
      | (fun x => bi_sep (@mem_mapsto_array _ _ 8%N ?a _ (@?l x)) (@?rest x)) => k a
      end
  end.

(* Byte cells from index zero kept as one group `c0 ∗ c1 ∗ …` (as a store
   into a byte array leaves them), at the base of the array the goal requests:
   the group's cells as separate hypotheses. *)
Ltac zesu_open_requested_byte_cell_group :=
  zesu_requested_byte_array_base ltac:(fun requested =>
    try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
    iMatchHyp ltac:(fun H res =>
      lazymatch res with
      | (@mem_mapsto _ _ 8%N (?base + Z.of_nat O * 1)%Z _ _ ∗ _)%I =>
          constr_eq base requested;
          iDestruct H as "[? HzesuCellGroup]";
          repeat (
            let rest := iTypeOf (INamed "HzesuCellGroup") in
            lazymatch rest with
            | Some (_, (@mem_mapsto _ _ 8%N (?other + Z.of_nat _ * 1)%Z _ _ ∗ _)%I) =>
                constr_eq other base; iDestruct "HzesuCellGroup" as "[? HzesuCellGroup]"
            end);
          iDestruct "HzesuCellGroup" as "?"
      end)).

(* A word cell asked for as the explicit list of its byte extracts (the shape
   a successor states for a stored word): the cell as that byte array. *)
Lemma zesu_word_little_endian_extracts (w : bv 64) :
  bv_to_little_endian 8 8 (bv_unsigned w) =
    [bv_extract 0 8 w; bv_extract 8 8 w; bv_extract 16 8 w; bv_extract 24 8 w;
     bv_extract 32 8 w; bv_extract 40 8 w; bv_extract 48 8 w; bv_extract 56 8 w].
Proof.
  unfold bv_to_little_endian. cbn [Z_to_little_endian fmap list_fmap Z.of_nat Pos.of_succ_nat].
  simpl. repeat f_equal; apply bv_eq; rewrite bv_extract_unsigned Z_to_bv_unsigned;
    unfold bv_wrap; rewrite ?Z.shiftr_shiftr ?Z.land_ones; try lia; rewrite ?Zmod_mod; reflexivity.
Qed.

Lemma zesu_subsume_word_cell_bytes `{!islaG Sigma} {B : Type} (a : Z) (w : bv 64)
    (P T : B → iProp Sigma) :
  (a ↦ₘ∗ [bv_extract 0 8 w; bv_extract 8 8 w; bv_extract 16 8 w; bv_extract 24 8 w;
          bv_extract 32 8 w; bv_extract 40 8 w; bv_extract 48 8 w; bv_extract 56 8 w] -∗
   ∃ x, P x ∗ T x) ⊢ subsume (a ↦ₘ w) P T.
Proof.
  iIntros "HG Hw". iApply "HG".
  iDestruct (zesu_cell_bytes 8 a (DfracOwn 1) w with "Hw") as "[Hb _]".
  change (N.to_nat 8) with 8%nat.
  rewrite (zesu_word_little_endian_extracts w). iExact "Hb".
Qed.

(* The same request under a successor existential (its first resource,
   independent of the witness), with the extracts taken of another spelling
   `v` of the word: the cell's value `w` as loaded (`Z_to_bv 64 (… (take 8
   (drop 0 bytes)))`) against `bv_concat` of the bytes `nth k bytes`. The
   equation `v = w` is closed first, by the block tail's word-window closer
   (BlockTail.v, a later module: called by name); without it the step does
   not act. *)
Lemma zesu_exist_word_cell_bytes `{!islaG Sigma} {B : Type} (a : Z) (w v : bv 64)
    (T : B → iProp Sigma) :
  v = w →
  a ↦ₘ w -∗ (∃ x, T x) -∗
  ∃ x, a ↦ₘ∗ [bv_extract 0 8 v; bv_extract 8 8 v; bv_extract 16 8 v; bv_extract 24 8 v;
              bv_extract 32 8 v; bv_extract 40 8 v; bv_extract 48 8 v; bv_extract 56 8 v] ∗ T x.
Proof.
  intros ->. iIntros "Hw [%x HT]". iExists x. iFrame "HT".
  iDestruct (zesu_cell_bytes 8 a (DfracOwn 1) w with "Hw") as "[Hb _]".
  change (N.to_nat 8) with 8%nat.
  rewrite (zesu_word_little_endian_extracts w). iExact "Hb".
Qed.
(* The same request when the successor existential is itself the left part
   of a separating conjunction (`(∃ x, cells ∗ T x) ∗ R`: the successor's
   pure tail and its continuation follow the existential). *)
Lemma zesu_exist_word_cell_bytes_sep `{!islaG Sigma} {B : Type} (a : Z) (w v : bv 64)
    (T : B → iProp Sigma) (R : iProp Sigma) :
  v = w →
  a ↦ₘ w -∗ ((∃ x, T x) ∗ R) -∗
  (∃ x, a ↦ₘ∗ [bv_extract 0 8 v; bv_extract 8 8 v; bv_extract 16 8 v; bv_extract 24 8 v;
               bv_extract 32 8 v; bv_extract 40 8 v; bv_extract 48 8 v; bv_extract 56 8 v] ∗ T x) ∗ R.
Proof.
  intros E. iIntros "Hw [HT HR]". iFrame "HR".
  iApply (zesu_exist_word_cell_bytes a w v T E with "Hw HT").
Qed.

(* And with no existential: the cells are the first resource of the request. *)
Lemma zesu_word_cell_bytes_sep `{!islaG Sigma} (a : Z) (w v : bv 64) (R : iProp Sigma) :
  v = w →
  a ↦ₘ w -∗ R -∗
  a ↦ₘ∗ [bv_extract 0 8 v; bv_extract 8 8 v; bv_extract 16 8 v; bv_extract 24 8 v;
         bv_extract 32 8 v; bv_extract 40 8 v; bv_extract 48 8 v; bv_extract 56 8 v] ∗ R.
Proof.
  intros ->. iIntros "Hw HR". iFrame "HR".
  iDestruct (zesu_cell_bytes 8 a (DfracOwn 1) w with "Hw") as "[Hb _]".
  change (N.to_nat 8) with 8%nat.
  rewrite (zesu_word_little_endian_extracts w). iExact "Hb".
Qed.

(* The request may go on past the word: `a ↦ₘ∗ (extracts ++ rest)` (05a4:
   the word and the byte stored after it, asked as one 9-byte array). The
   cell gives the first eight bytes; the request keeps `(a + 8) ↦ₘ∗ rest` in
   the place of the array. Tried only after the exact eight-byte shapes. *)
Lemma zesu_word_cell_bytes_rest `{!islaG Sigma} (a : Z) (w v : bv 64) (rest : list (bv 8)) :
  v = w →
  a ↦ₘ w -∗ (a + 8) ↦ₘ∗ rest -∗
  a ↦ₘ∗ (bv_extract 0 8 v :: bv_extract 8 8 v :: bv_extract 16 8 v :: bv_extract 24 8 v ::
         bv_extract 32 8 v :: bv_extract 40 8 v :: bv_extract 48 8 v :: bv_extract 56 8 v :: rest).
Proof.
  intros ->. iIntros "Hw Hr".
  iDestruct (zesu_cell_bytes 8 a (DfracOwn 1) w with "Hw") as "[Hb _]".
  change (N.to_nat 8) with 8%nat.
  rewrite (zesu_word_little_endian_extracts w).
  iApply (mem_mapsto_array_app_combine_at 8 a (DfracOwn 1)
    [bv_extract 0 8 w; bv_extract 8 8 w; bv_extract 16 8 w; bv_extract 24 8 w;
     bv_extract 32 8 w; bv_extract 40 8 w; bv_extract 48 8 w; bv_extract 56 8 w]
    rest 8 eq_refl with "Hb [Hr]").
  have -> : a + Z.of_N (8 `div` 8) * 8%nat = a + 8 by vm_compute; lia.
  iExact "Hr".
Qed.

(* The three request shapes of the exact rule, with at least one byte after
   the word (an empty rest is the exact shape). *)
Lemma zesu_exist_word_cell_bytes_rest `{!islaG Sigma} {B : Type} (a : Z) (w v : bv 64)
    (b : bv 8) (rest : list (bv 8)) (T : B → iProp Sigma) :
  v = w →
  a ↦ₘ w -∗ (∃ x, (a + 8) ↦ₘ∗ (b :: rest) ∗ T x) -∗
  ∃ x, a ↦ₘ∗ (bv_extract 0 8 v :: bv_extract 8 8 v :: bv_extract 16 8 v :: bv_extract 24 8 v ::
              bv_extract 32 8 v :: bv_extract 40 8 v :: bv_extract 48 8 v :: bv_extract 56 8 v ::
              b :: rest) ∗ T x.
Proof.
  intros E. iIntros "Hw [%x [Hr HT]]". iExists x. iFrame "HT".
  iApply (zesu_word_cell_bytes_rest a w v (b :: rest) E with "Hw Hr").
Qed.

Lemma zesu_exist_word_cell_bytes_rest_sep `{!islaG Sigma} {B : Type} (a : Z) (w v : bv 64)
    (b : bv 8) (rest : list (bv 8)) (T : B → iProp Sigma) (R : iProp Sigma) :
  v = w →
  a ↦ₘ w -∗ ((∃ x, (a + 8) ↦ₘ∗ (b :: rest) ∗ T x) ∗ R) -∗
  (∃ x, a ↦ₘ∗ (bv_extract 0 8 v :: bv_extract 8 8 v :: bv_extract 16 8 v :: bv_extract 24 8 v ::
               bv_extract 32 8 v :: bv_extract 40 8 v :: bv_extract 48 8 v :: bv_extract 56 8 v ::
               b :: rest) ∗ T x) ∗ R.
Proof.
  intros E. iIntros "Hw [HT HR]". iFrame "HR".
  iApply (zesu_exist_word_cell_bytes_rest a w v b rest T E with "Hw HT").
Qed.

Lemma zesu_word_cell_bytes_rest_sep `{!islaG Sigma} (a : Z) (w v : bv 64) (b : bv 8)
    (rest : list (bv 8)) (R : iProp Sigma) :
  v = w →
  a ↦ₘ w -∗ ((a + 8) ↦ₘ∗ (b :: rest) ∗ R) -∗
  a ↦ₘ∗ (bv_extract 0 8 v :: bv_extract 8 8 v :: bv_extract 16 8 v :: bv_extract 24 8 v ::
         bv_extract 32 8 v :: bv_extract 40 8 v :: bv_extract 48 8 v :: bv_extract 56 8 v ::
         b :: rest) ∗ R.
Proof.
  intros E. iIntros "Hw [Hr HR]". iFrame "HR".
  iApply (zesu_word_cell_bytes_rest a w v (b :: rest) E with "Hw Hr").
Qed.

Ltac zesu_exist_word_cell_with a v :=
  assert_fails (has_evar v);
  iMatchHyp ltac:(fun H res =>
    lazymatch res with
    | (@mem_mapsto _ _ 64%N ?a2 (DfracOwn 1) ?w)%I =>
        constr_eq a a2;
        let E := fresh "HwordCellValue" in
        assert (E : v = w) by
          (first [ reflexivity
                 | ltac2:(Ltac1.run (Ltac1.ref
                     [@ZesuSsz; @Automation2; @BlockTail; @zesu_tail_window_goal])) ]);
        try iEval (rewrite <- isla.ghost_state.mem_mapsto_array_eq);
        first [ iApply (zesu_exist_word_cell_bytes a w v _ E with H)
              | iApply (zesu_exist_word_cell_bytes_sep a w v _ _ E with H)
              | iApply (zesu_word_cell_bytes_sep a w v _ E with H)
              | iApply (zesu_exist_word_cell_bytes_rest a w v _ _ _ E with H)
              | iApply (zesu_exist_word_cell_bytes_rest_sep a w v _ _ _ _ E with H)
              | iApply (zesu_word_cell_bytes_rest_sep a w v _ _ _ E with H) ];
        clear E
    end).

Ltac zesu_subsume_word_cell_extracts :=
  lazymatch goal with
  | |- environments.envs_entails _ (subsume (@mem_mapsto _ _ 64%N ?a (DfracOwn 1) _) ?P _) =>
      lazymatch P with
      | (fun _ => @mem_mapsto_array _ _ 8%N ?a2 (DfracOwn 1) (bv_extract 0 8 _ :: _)) =>
          constr_eq a a2
      end;
      (* The run names the environment by a local definition; `iApply` needs
         the environment itself. *)
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      iApply zesu_subsume_word_cell_bytes; iIntros "?"
  | |- environments.envs_entails _ (@bi_exist _ _ (fun x =>
        bi_sep (@mem_mapsto_array _ _ 8%N ?a (DfracOwn 1) (bv_extract 0 8 ?v :: _)) _)) =>
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      zesu_exist_word_cell_with a v
  | |- environments.envs_entails _ (@bi_exist _ _ (fun x =>
        bi_sep (@isla.ghost_state.mem_mapsto_array_def _ _ 8%N ?a (DfracOwn 1)
          (bv_extract 0 8 ?v :: _)) _)) =>
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      zesu_exist_word_cell_with a v
  | |- environments.envs_entails _ (bi_sep (@bi_exist _ _ (fun x =>
        bi_sep (@mem_mapsto_array _ _ 8%N ?a (DfracOwn 1) (bv_extract 0 8 ?v :: _)) _)) _) =>
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      zesu_exist_word_cell_with a v
  | |- environments.envs_entails _ (bi_sep (@bi_exist _ _ (fun x =>
        bi_sep (@isla.ghost_state.mem_mapsto_array_def _ _ 8%N ?a (DfracOwn 1)
          (bv_extract 0 8 ?v :: _)) _)) _) =>
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      zesu_exist_word_cell_with a v
  | |- environments.envs_entails _ (bi_sep
        (@mem_mapsto_array _ _ 8%N ?a (DfracOwn 1) (bv_extract 0 8 ?v :: _)) _) =>
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      zesu_exist_word_cell_with a v
  | |- environments.envs_entails _ (bi_sep
        (@isla.ghost_state.mem_mapsto_array_def _ _ 8%N ?a (DfracOwn 1) (bv_extract 0 8 ?v :: _)) _) =>
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      zesu_exist_word_cell_with a v
  end.

(* A cell narrower than a word, of [len] bytes (8 * len bits, 2 <= len <= 7),
   asked for as the explicit list of its [len] byte extracts (decodeParentHeader
   0270: a 16-bit tag stored from x10 against `[bv_extract 0 8 x10;
   bv_extract 8 8 x10]`): the cell as that byte array, once the list is shown
   to be its little-endian bytes byte by byte. A 64-bit cell is never this
   rule's: it stays with `zesu_subsume_word_cell_extracts` above, whose
   subsumption form also accepts extracts of the existential's witness. *)
Lemma zesu_cell_as_bytes `{!islaG Sigma} (len : N) (a : Z) (w : bv (8 * len)) (l : list (bv 8)) :
  bv_to_little_endian (N.to_nat len) 8 (bv_unsigned w) = l →
  a ↦ₘ w -∗ a ↦ₘ∗ l.
Proof.
  intros <-. iIntros "Hw".
  iDestruct (zesu_cell_bytes len a (DfracOwn 1) w with "Hw") as "[$ _]".
Qed.

Lemma zesu_subsume_cell_bytes `{!islaG Sigma} {B : Type} (len : N) (a : Z) (w : bv (8 * len))
    (l : list (bv 8)) (P T : B → iProp Sigma) :
  bv_to_little_endian (N.to_nat len) 8 (bv_unsigned w) = l →
  (a ↦ₘ∗ l -∗ ∃ x, P x ∗ T x) ⊢ subsume (a ↦ₘ w) P T.
Proof.
  iIntros (E) "HG Hw". iApply "HG". iApply (zesu_cell_as_bytes len a w l E with "Hw").
Qed.

Lemma zesu_exist_cell_bytes `{!islaG Sigma} {B : Type} (len : N) (a : Z) (w : bv (8 * len))
    (l : list (bv 8)) (T : B → iProp Sigma) :
  bv_to_little_endian (N.to_nat len) 8 (bv_unsigned w) = l →
  a ↦ₘ w -∗ (∃ x, T x) -∗ ∃ x, a ↦ₘ∗ l ∗ T x.
Proof.
  intros E. iIntros "Hw [%x HT]". iExists x. iFrame "HT".
  iApply (zesu_cell_as_bytes len a w l E with "Hw").
Qed.

Lemma zesu_exist_cell_bytes_sep `{!islaG Sigma} {B : Type} (len : N) (a : Z) (w : bv (8 * len))
    (l : list (bv 8)) (T : B → iProp Sigma) (R : iProp Sigma) :
  bv_to_little_endian (N.to_nat len) 8 (bv_unsigned w) = l →
  a ↦ₘ w -∗ ((∃ x, T x) ∗ R) -∗ (∃ x, a ↦ₘ∗ l ∗ T x) ∗ R.
Proof.
  intros E. iIntros "Hw [HT HR]". iFrame "HR".
  iApply (zesu_exist_cell_bytes len a w l T E with "Hw HT").
Qed.

Lemma zesu_cell_bytes_sep `{!islaG Sigma} (len : N) (a : Z) (w : bv (8 * len))
    (l : list (bv 8)) (R : iProp Sigma) :
  bv_to_little_endian (N.to_nat len) 8 (bv_unsigned w) = l →
  a ↦ₘ w -∗ R -∗ a ↦ₘ∗ l ∗ R.
Proof.
  intros E. iIntros "Hw HR". iFrame "HR". iApply (zesu_cell_as_bytes len a w l E with "Hw").
Qed.

(* The cell width [n] (a numeral) as [len] bytes when 2 <= len <= 7 and the
   request [L] is an explicit list of [len] bytes headed by an extract at bit
   0; then [tac len]. Fails otherwise (a 64-bit cell, a byte cell, a longer or
   shorter request). *)
Ltac zesu_narrow_cell_split n L tac :=
  lazymatch L with bv_extract 0 8 _ :: _ => idtac end;
  let len := eval vm_compute in (N.div n 8) in
  let n8 := eval vm_compute in (8 * len)%N in
  constr_eq n n8;
  lazymatch eval vm_compute in (andb (N.leb 2 len) (N.leb len 7)) with true => idtac end;
  let k := zesu_spine_length L in
  let k2 := eval vm_compute in (N.to_nat len) in
  constr_eq k k2;
  tac len.

(* `bv_to_little_endian len 8 (bv_unsigned w) = L` byte by byte, in a context
   cleared of every proposition. *)
Ltac zesu_narrow_cell_bytes_eq :=
  repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => clear H end end;
  unfold bv_to_little_endian; simpl; repeat f_equal; bv_solve.

Ltac zesu_narrow_cell_with a L :=
  iMatchHyp ltac:(fun H res =>
    lazymatch res with
    | (@mem_mapsto _ _ ?n ?a2 (DfracOwn 1) ?w)%I =>
        constr_eq a a2;
        zesu_narrow_cell_split n L ltac:(fun len =>
          let E := fresh "HcellBytes" in
          assert (E : bv_to_little_endian (N.to_nat len) 8 (bv_unsigned w) = L)
            by zesu_narrow_cell_bytes_eq;
          try iEval (rewrite <- isla.ghost_state.mem_mapsto_array_eq);
          first [ iApply (zesu_exist_cell_bytes len a w L _ E with H)
                | iApply (zesu_exist_cell_bytes_sep len a w L _ _ E with H)
                | iApply (zesu_cell_bytes_sep len a w L _ E with H) ];
          clear E)
    end).

Ltac zesu_subsume_narrow_cell_extracts :=
  lazymatch goal with
  | |- environments.envs_entails _ (subsume (@mem_mapsto _ _ ?n ?a (DfracOwn 1) ?w) ?P _) =>
      lazymatch P with
      | (fun _ => @mem_mapsto_array _ _ 8%N ?a2 (DfracOwn 1) ?L) =>
          constr_eq a a2;
          zesu_narrow_cell_split n L ltac:(fun len =>
            let E := fresh "HcellBytes" in
            assert (E : bv_to_little_endian (N.to_nat len) 8 (bv_unsigned w) = L)
              by zesu_narrow_cell_bytes_eq;
            try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
            iApply (zesu_subsume_cell_bytes len a w L _ _ E); iIntros "?";
            clear E)
      end
  | |- environments.envs_entails _ (@bi_exist _ _ (fun x =>
        bi_sep (@mem_mapsto_array _ _ 8%N ?a (DfracOwn 1) ?L) _)) =>
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      zesu_narrow_cell_with a L
  | |- environments.envs_entails _ (@bi_exist _ _ (fun x =>
        bi_sep (@isla.ghost_state.mem_mapsto_array_def _ _ 8%N ?a (DfracOwn 1) ?L) _)) =>
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      zesu_narrow_cell_with a L
  | |- environments.envs_entails _ (bi_sep (@bi_exist _ _ (fun x =>
        bi_sep (@mem_mapsto_array _ _ 8%N ?a (DfracOwn 1) ?L) _)) _) =>
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      zesu_narrow_cell_with a L
  | |- environments.envs_entails _ (bi_sep (@bi_exist _ _ (fun x =>
        bi_sep (@isla.ghost_state.mem_mapsto_array_def _ _ 8%N ?a (DfracOwn 1) ?L) _)) _) =>
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      zesu_narrow_cell_with a L
  | |- environments.envs_entails _ (bi_sep (@mem_mapsto_array _ _ 8%N ?a (DfracOwn 1) ?L) _) =>
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      zesu_narrow_cell_with a L
  | |- environments.envs_entails _ (bi_sep
        (@isla.ghost_state.mem_mapsto_array_def _ _ 8%N ?a (DfracOwn 1) ?L) _) =>
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      zesu_narrow_cell_with a L
  end.

(* A store that covers a whole held array leaves it as the splice
   `take (Z.to_nat (p - base)) J ++ b0 :: … :: drop (Z.to_nat (p - base) + n) J`.
   Where the goal requests an array at that address (opened or sealed), the
   store's offset is 0 (address arithmetic in a context cleared to the range
   facts of the domain hypothesis, `CallSlice.zesu_call_slice_address`) and
   the drop starts at or after `length J` (a length fact of `J`), the held
   array is the stored bytes. *)
Ltac zesu_store_splice_offset_zero e :=
  let Hz := fresh "HspliceOffset" in
  assert (Hz : e = 0%Z) by ZesuSsz.Automation2.CallSlice.zesu_call_slice_address.

(* The stored bytes of a word `w`, unfolded from `bv_to_little_endian 8 8
   (bv_unsigned w)`, held at `a` while the goal asks for `w`'s byte extracts
   there: the held array in the requested spelling. *)
Ltac zesu_store_word_bytes_as_extracts a l :=
  lazymatch l with
  | bv_extract 0 8 ?w :: _ =>
      iMatchHyp ltac:(fun H res =>
        lazymatch res with
        | (?b ↦ₘ∗ ?bytes)%I =>
            constr_eq a b;
            iRename H into "HspliceWord";
            iEval (change bytes with (bv_to_little_endian 8 8 (bv_unsigned w));
                   rewrite (zesu_word_little_endian_extracts w)) in "HspliceWord";
            iDestruct "HspliceWord" as "?"
        end)
  end.

Ltac zesu_store_whole_array_splice :=
  lazymatch goal with
  | |- environments.envs_entails _ ?requested =>
      let a := lazymatch requested with
        | @bi_sep _ (isla.ghost_state.mem_mapsto_array_def ?a _ _) _ => a
        | @bi_exist _ _ (fun _ => @bi_sep _ (isla.ghost_state.mem_mapsto_array_def ?a _ _) _) => a
        | @bi_sep _ (@isla.ghost_state.mem_mapsto_array _ _ _ ?a _ _) _ => a
        | @bi_exist _ _ (fun _ => @bi_sep _ (@isla.ghost_state.mem_mapsto_array _ _ _ ?a _ _) _) => a
        end in
      (* the requested bytes, when they do not mention the existential *)
      let l := lazymatch requested with
        | @bi_sep _ (isla.ghost_state.mem_mapsto_array_def _ _ ?l) _ => l
        | @bi_exist _ _ (fun _ => @bi_sep _ (isla.ghost_state.mem_mapsto_array_def _ _ ?l) _) => l
        | @bi_sep _ (@isla.ghost_state.mem_mapsto_array _ _ _ _ _ ?l) _ => l
        | @bi_exist _ _ (fun _ => @bi_sep _ (@isla.ghost_state.mem_mapsto_array _ _ _ _ _ ?l) _) => l
        | _ => constr:(tt)
        end in
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      iMatchHyp ltac:(fun H res =>
        lazymatch res with
        | (?b ↦ₘ∗ (take (Z.to_nat ?e) ?J ++ _))%I =>
            constr_eq a b;
            let n := lazymatch goal with HJ : length J = ?n |- _ => n end in
            zesu_store_splice_offset_zero e;
            let Hz := lazymatch goal with Hz : e = 0%Z |- _ => Hz end in
            iRename H into "HspliceArray";
            iEval (rewrite Hz; change (Z.to_nat 0) with 0%nat; rewrite take_0 app_nil_l)
              in "HspliceArray";
            clear Hz;
            lazymatch goal with
            | |- context [drop ?index J] =>
                let Hd := fresh "HspliceDrop" in
                assert (Hd : (length J <= index)%nat) by
                  (lazymatch goal with HJ : length J = n |- _ =>
                     clear - HJ; rewrite HJ; cbn; zesu_lia end);
                iEval (rewrite (drop_ge J index Hd)) in "HspliceArray"; clear Hd
            end;
            iDestruct "HspliceArray" as "?"
        end);
      try zesu_store_word_bytes_as_extracts a l
  end.

(* Byte cells from index zero first, then the general run, then byte cells
   from index zero held as one group, then a word cell asked for as its byte
   extracts, then a held array a store covered whole, then a cell narrower
   than a word asked for as its byte extracts, then a cell and its adjacent
   pieces asked for as one explicit list. *)
Ltac zesu_join_frame_byte_array :=
  first [ ltac2:(zesu_join_frame_byte_array ()) | zesu_join_frame_run
        | zesu_open_requested_byte_cell_group; ltac2:(zesu_join_frame_byte_array ())
        | zesu_subsume_word_cell_extracts
        | zesu_store_whole_array_splice
        | zesu_subsume_narrow_cell_extracts
        | zesu_join_frame_explicit
        | zesu_join_frame_explicit_exist ].

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

(* Every alternative below acts only on a memory lookup, and none of the steps
   before that test (alias exposure, unfolding local names, splice rewrites)
   changes the target's head. Test the head once, before any of them. *)
Ltac zesu_store_lookup_goal :=
  lazymatch goal with
  | |- environments.envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac
  end.

(* Region sizes of uninitialised pieces as numerals. *)
Ltac zesu_uninit_sizes :=
  repeat iMatchHyp ltac:(fun H res =>
    lazymatch res with
    | (?a ↦ₘ? ?n0)%I =>
        lazymatch n0 with Z0 => fail | Zpos _ => fail | _ => idtac end;
        let ra := ZesuSsz.Automation2.WrappedWord.zesu_term_root a in
        let n := ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root ra n0 in
        let Hn := fresh "HregionSize" in
        assert (Hn : n0 = n) by (clear; ZesuSsz.Automation2.WrappedWord.zesu_plain_lia);
        iRename H into "HzesuRegion";
        iEval (rewrite Hn) in "HzesuRegion"; clear Hn;
        iDestruct "HzesuRegion" as "?"
    end).

(* The owner of the address is an uninitialised region or a single cell on
   the same root (decided at a sample root value); arrays are left to the
   other alternatives. *)
Ltac zesu_owner_uninit_or_cell z addr :=
  let d := ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root z addr in
  lazymatch d with Z0 => idtac | Zpos _ => idtac end;
  iMatchHyp ltac:(fun H res =>
    lazymatch res with
    | (?a ↦ₘ? ?n0)%I =>
        let ra := ZesuSsz.Automation2.WrappedWord.zesu_term_root a in
        constr_eq ra z;
        let lo := ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root z a in
        let n := ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root z n0 in
        let inside := eval vm_compute in ((lo <=? d)%Z && (d <? lo + n)%Z)%bool in
        lazymatch inside with true => idtac end
    | (?a ↦ₘ _)%I =>
        let ra := ZesuSsz.Automation2.WrappedWord.zesu_term_root a in
        constr_eq ra z;
        let lo := ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root z a in
        let same := eval vm_compute in (lo =? d)%Z in
        lazymatch same with true => idtac end
    end).

(* Fails when [root] is the root of the stack pointer register: frame stores
   and loads are the business of the stack-address steps. *)
Ltac zesu_refuse_stack_root root :=
  assert_fails (iMatchHyp ltac:(fun H res =>
    lazymatch res with
    | (?reg ↦ᵣ RVal_Bits ?value)%I =>
        constr_eq reg "x2"%string;
        let word := lazymatch value with bv_to_bvn ?w => w | _ => value end in
        let stack := ZesuSsz.Automation2.WrappedWord.zesu_term_root word in
        constr_eq stack root
    end)).

(* A store or load whose pointer is an integer root under `Z_to_bv`, owned by
   an uninitialised region or a cell on that root: the address as the integer
   `z + c`, region sizes as numerals, then Lithium's own lookup step. *)
Ltac zesu_store_lookup_integer_root :=
  lazymatch goal with
  | |- environments.envs_entails _ (find_in_context (FindMemMapsTo (bv_unsigned ?ptr)) _) =>
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      let zr := ZesuSsz.Automation2.WrappedWord.zesu_term_root ptr in
      zesu_refuse_stack_root zr;
      zesu_owner_uninit_or_cell zr constr:(bv_unsigned ptr);
      ZesuSsz.Automation2.WrappedWord.zesu_zroot_address ptr ltac:(fun Haddress z =>
        rewrite Haddress; clear Haddress;
        try (lazymatch goal with |- context [bv_unsigned (Z_to_bv 64 z)] => idtac end;
             ZesuSsz.Automation2.WrappedWord.zesu_zroot_address constr:(Z_to_bv 64 z)
               ltac:(fun Hroot _ => rewrite !Hroot; clear Hroot)));
      zesu_uninit_sizes;
      liEnsureInvariant;
      liStep
  end.

(* [k] receives `bv_unsigned word = bv_unsigned r + s` (s a signed literal)
   for a chain of closed offsets on a word root r (not `Z_to_bv`), the range
   proved from the facts selected for r. *)
Ltac zesu_word_root_address word k :=
  let chain := ZesuSsz.Automation2.WrappedWord.zesu_wrapped_offset_chain word in
  lazymatch type of chain with
  | bv_unsigned _ = bv_wrap ?width (bv_unsigned ?root + ?sum) =>
      lazymatch root with Z_to_bv _ _ => fail | _ => idtac end;
      assert_fails (ZesuSsz.Automation2.VmClosed.zesu_vm_closed root);
      let offset := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (bv_swrap width sum) in
      let address := constr:((bv_unsigned root + offset)%Z) in
      let Haddress := fresh "HwordRootAddress" in
      assert (Haddress : bv_unsigned word = address) by
        (refine (ZesuSsz.Automation2.WrappedWord.zesu_wrapped_offset_small
                   width (bv_unsigned root) sum offset address word chain _ _ _);
         [vm_compute; reflexivity | reflexivity
         | ZesuSsz.Automation2.WrappedWord.zesu_wrapped_index_range root]);
      k Haddress
  end.

(* Addresses and sizes of the memory resources on the word root [r] that read
   `bv_unsigned (r + c…)`, as `bv_unsigned r + s`. *)
Ltac zesu_word_root_owner_addresses r :=
  repeat iMatchHyp ltac:(fun H res =>
    let a := lazymatch res with
      | (?a ↦ₘ _)%I => a | (?a ↦ₘ∗ _)%I => a | (?a ↦ₘ? _)%I => a end in
    let ra := ZesuSsz.Automation2.WrappedWord.zesu_term_root a in
    constr_eq ra r;
    match res with
    | context [bv_unsigned (bv_add ?inner ?step)] =>
        let r2 := ZesuSsz.Automation2.WrappedWord.zesu_term_root inner in
        constr_eq r r2;
        zesu_word_root_address constr:(bv_add inner step) ltac:(fun Heq =>
          iEval (rewrite !Heq) in H; clear Heq)
    end).

(* A memory resource owned at exactly [address]: Lithium's lookup matches it. *)
Ltac zesu_address_owned_exactly address :=
  iMatchHyp ltac:(fun H res =>
    lazymatch res with
    | (?a ↦ₘ _)%I => constr_eq a address
    | (?a ↦ₘ∗ _)%I => constr_eq a address
    | (?a ↦ₘ? _)%I => constr_eq a address
    end).

(* The owner of the address [d] (a value at the sample root) on root [r]: a
   cell or an uninitialised region whose address is integer arithmetic over
   `bv_unsigned r`. [k] receives the owner's address and the offset of [d] in
   it. A byte array is never the owner here: Lithium's array lookup reads an
   access inside it as the array's elements (`nth`), the spelling successors
   state, so rewriting the address would leave the value in another spelling. *)
Ltac zesu_owner_offset r d k :=
  iMatchHyp ltac:(fun H res =>
    let a := lazymatch res with
      | (?a ↦ₘ _)%I => a | (?a ↦ₘ? _)%I => a end in
    let ra := ZesuSsz.Automation2.WrappedWord.zesu_term_root a in
    constr_eq ra r;
    lazymatch a with context [@bv_add] => fail | context [@bv_sub] => fail | _ => idtac end;
    let lo := ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root r a in
    let size := lazymatch res with
      | (_ ↦ₘ ?v)%I =>
          lazymatch type of v with bv ?w => eval vm_compute in (Z.of_N (w / 8)) end
      | (_ ↦ₘ? ?n)%I => ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root r n
      end in
    let off := eval vm_compute in (d - lo)%Z in
    let inside := eval vm_compute in ((0 <=? off) && (off <? size))%bool in
    lazymatch inside with true => idtac end;
    k a off).

(* A store or load whose pointer is a chain of closed offsets on a word root
   (a record field, not `Z_to_bv`), owned by a resource on that root: off the
   stack pointer's root the resources on the root first read
   `bv_unsigned r + s`; then the address is written in the owner's own
   spelling (plus a literal offset), region sizes as numerals, and Lithium's
   own lookup step runs. *)
Ltac zesu_store_lookup_word_root :=
  lazymatch goal with
  | |- environments.envs_entails _ (find_in_context (FindMemMapsTo (bv_unsigned ?ptr)) _) =>
      lazymatch ptr with bv_add _ _ => idtac end;
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      let r := ZesuSsz.Automation2.WrappedWord.zesu_term_root ptr in
      lazymatch r with Z_to_bv _ _ => fail | _ => idtac end;
      lazymatch type of r with bv _ => idtac end;
      assert_fails (zesu_address_owned_exactly constr:(bv_unsigned ptr));
      let d := ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root r constr:(bv_unsigned ptr) in
      lazymatch d with Zpos _ => idtac end;
      try (zesu_refuse_stack_root r; zesu_word_root_owner_addresses r);
      zesu_owner_offset r d ltac:(fun a off =>
        let target := lazymatch off with Z0 => a | _ => constr:((a + off)%Z) end in
        zesu_word_root_address ptr ltac:(fun Hword =>
          let Htarget := fresh "HownerAddress" in
          assert (Htarget : bv_unsigned ptr = target) by
            (rewrite Hword; clear; ZesuSsz.Automation2.WrappedWord.zesu_plain_lia);
          clear Hword; rewrite !Htarget; clear Htarget));
      zesu_uninit_sizes;
      liEnsureInvariant;
      liStep
  end.

Ltac zesu_store_memory_lookup :=
  zesu_store_lookup_goal;
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuStepStoreMemoryLookup);
  first [ zesu_store_memory_lookup_core
  | progress (zesu_store_fold_indexed_byte_tail;
      ZesuSsz.Automation2.ResourceGroups.zesu_open_resource_groups)
  | zesu_store_fold_byte_cells
  | zesu_store_lookup_integer_root
  | zesu_store_lookup_word_root ].

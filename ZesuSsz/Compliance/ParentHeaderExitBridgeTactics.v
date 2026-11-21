(* decodeParentHeader end bridges (exit design A): the frame lemmas and the
   shared tactic of the bridges from the generated exit packages to the
   contract exit (parentHeaderAllows, parentHeaderExitResources). Specific to
   this function's frame (400 bytes below the stack pointer, saved-register
   cells at offsets 320 to 392); no Automation2 rule. The bridges are in
   ParentHeaderTailExitBridge.v (the memcpy tail exit) and
   ParentHeaderDirectExitBridges.v (one per slot of the return block 0x0274). *)
Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderDomainRanges.
Require Import ZesuSsz.Contracts.ParentHeaderRung2.
Require Import ZesuSsz.Contracts.AbiBytes.
Local Open Scope Z_scope.

(* The statement of an end bridge: the exit package gives the contract exit. *)
Notation parentHeaderEndBridge args returnAddress package :=
  (package ⊢ ∃ outcome : ParentHeaderOutcome,
    ⌜bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\
     parentHeaderAllows (parentHeaderCall args) outcome⌝ ∗
    parentHeaderExitResources args outcome)%I (only parsing).

(* The meaning of a direct exit's result, as the exit-meaning declarations of
   the generated return packages take it. *)
Definition parentHeaderResultMeaning (args : ParentHeaderArgs) (result : list byte) : Prop :=
  ParentHeaderMeaningModuloKnownBugs (parentHeaderCall args) result.

Lemma parentHeader_frame_address (sp kb : bv 64) :
  400 <= bv_unsigned sp -> bv_unsigned kb < 400 ->
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551216)) kb) = bv_unsigned sp - 400 + bv_unsigned kb.
Proof.
  intros Hsp Hk. rewrite !bv_add_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l.
  change (bv_unsigned (BV 64 18446744073709551216)) with 18446744073709551216.
  change (bv_modulus 64) with (2 ^ 64).
  pose proof (bv_unsigned_in_range _ sp). pose proof (bv_unsigned_in_range _ kb).
  unfold bv_modulus in *. simpl in *.
  replace (bv_unsigned sp + 18446744073709551216 + bv_unsigned kb)
    with ((bv_unsigned sp - 400 + bv_unsigned kb) + 1 * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* A saved-register cell of the frame as its eight bytes at the frame base
   plus its numeral offset k. *)
Lemma parentHeader_cell_bytes_at `{!islaG Sigma} (sp kb w : bv 64) (k : Z) :
  400 <= bv_unsigned sp -> bv_unsigned kb = k -> 0 <= k < 400 ->
  bv_unsigned (bv_add (bv_add sp (BV 64 18446744073709551216)) kb) ↦ₘ w ⊢
  (bv_unsigned sp - 400 + k) ↦ₘ∗ bv_to_little_endian 8 8 (bv_unsigned w) ∗
  ⌜Z.of_nat (length (bv_to_little_endian 8 8 (bv_unsigned w))) = 8⌝.
Proof.
  intros Hsp <- Hk. rewrite parentHeader_frame_address; [|lia|lia]. iIntros "H".
  iApply (zesu_cell_bytes 8 with "H").
Qed.

(* A saved register reloaded from its eight frame bytes is the saved word. *)
Lemma parentHeader_word_of_bytes (w : bv 64) :
  bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
    (bv_concat 16 (bv_extract 56 8 w) (bv_extract 48 8 w)) (bv_extract 40 8 w))
    (bv_extract 32 8 w)) (bv_extract 24 8 w)) (bv_extract 16 8 w)) (bv_extract 8 8 w))
    (bv_extract 0 8 w) = w.
Proof. bv_simplify. bitblast; f_equal; lia. Qed.

Lemma parentHeader_sp_restore (sp : bv 64) :
  bv_add (bv_add sp (BV 64 18446744073709551216)) (BV 64 400) = sp.
Proof. bv_solve. Qed.

(* Every saved-register cell of the frame as its eight bytes. *)
Ltac parentHeader_cells_to_bytes :=
  repeat iMatchHyp ltac:(fun H res =>
    lazymatch res with
    | (bv_unsigned (bv_add (bv_add (parentHeaderStackPointer _) (BV 64 18446744073709551216)) ?kb) ↦ₘ _)%I =>
        let k := eval vm_compute in (bv_unsigned kb) in
        iRename H into "C";
        iDestruct (parentHeader_cell_bytes_at _ kb _ k with "C") as "[? %]";
        [lia|reflexivity|lia|]
    end).

(* The saved registers reloaded from their eight frame bytes as the saved
   words, the stack pointer restored. The occurrences are found by syntactic
   matching: a rewrite with the open lemma tries to unify its left side with
   every word assembled from bytes (result words, call records), which does
   not terminate in reasonable time. *)
Ltac parentHeader_saved_words :=
  cbn [List.nth];
  repeat match goal with
  | |- context [bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32
        (bv_concat 24 (bv_concat 16 (bv_extract 56 8 ?w) (bv_extract 48 8 ?w))
        (bv_extract 40 8 ?w)) (bv_extract 32 8 ?w)) (bv_extract 24 8 ?w))
        (bv_extract 16 8 ?w)) (bv_extract 8 8 ?w)) (bv_extract 0 8 ?w)] =>
      rewrite (parentHeader_word_of_bytes w)
  end;
  repeat match goal with
  | |- context [bv_add (bv_add ?sp (BV 64 18446744073709551216)) (BV 64 400)] =>
      rewrite (parentHeader_sp_restore sp)
  end.

(* Opens an exit package: binders, components and pure facts, with the saved
   words of parentHeader_saved_words. *)
Ltac parentHeader_exit_open :=
  rewrite -?(@mem_mapsto_array_eq _ _ 8);
  parentHeader_saved_words;
  iIntros "H";
  (* syntactic heads only: a failing IntoExist or IntoSep search on the
     package's large terms costs seconds per attempt *)
  repeat (lazymatch iTypeOf (INamed "H") with
          | Some (_, bi_exist _) => iDestruct "H" as (?) "H" end);
  repeat (lazymatch iTypeOf (INamed "H") with
          | Some (_, bi_sep _ _) => iDestruct "H" as "[? H]" end);
  repeat iDestruct select (⌜_⌝)%I as %?.

(* The contract exit of an opened package on [path]: the frame folded into
   its 400-byte array, the result region into one array (the generic fold of
   Automation2/StoreMemoryLookup.v), the outcome chosen, the registers and
   the remaining resources framed. Leaves the meaning goal. *)
Ltac parentHeader_exit_close path :=
  lazymatch goal with
  | H : bv_unsigned (parentHeaderReturnAddress ?args) = _ /\ parentHeaderArgsWellFormed _ |- _ =>
      let Hret := fresh "Hret" in let Hwf := fresh "Hwf" in
      destruct H as [Hret Hwf]; pose proof (parentHeaderStackRange args Hwf);
      parentHeader_cells_to_bytes;
      zesu_fold_byte_run (bv_unsigned (parentHeaderStackPointer args) - 400);
      iRename "HzesuRun" into "Frame";
      let Hframe := fresh "Hframe" in
      lazymatch goal with Hl : Z.of_nat (length _) = 400 |- _ => rename Hl into Hframe end;
      try (zesu_fold_byte_run (bv_unsigned (parentHeaderResultPointer args));
           iRename "HzesuRun" into "Result");
      lazymatch iTypeOf (INamed "Frame") with
      | Some (_, (_ ↦ₘ∗ ?frame)%I) =>
      iMatchHyp ltac:(fun _ res =>
        lazymatch res with
        | (bv_unsigned (parentHeaderResultPointer args) ↦ₘ∗ ?result)%I =>
            iExists {| headerExitPath := path; headerResultBytes := result;
                       headerAfterFrame := frame |};
            rewrite /parentHeaderExitResources /=;
            iSplit; [iPureIntro; split; [exact Hret|]; split;
                     [|split; [apply Nat2Z.inj; exact Hframe|first [exact I|reflexivity]]]|];
            [|iExists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _; iFrame]
        end)
      end
  end.

(* A direct-return bridge: the resources by the shared steps, the meaning
   from the package's generated exit-meaning premise (its history, visible
   facts and the lengths of the result bytes it does not write). *)
Ltac parentHeader_direct_slot_bridge Hmeaning :=
  (* the premise stays folded until the end: a large context slows every
     proof-mode step *)
  parentHeader_exit_open;
  parentHeader_exit_close ParentHeaderDirect;
  rewrite ?zesu_word_little_endian_extracts -?app_assoc;
  hnf in Hmeaning; unfold parentHeaderResultMeaning in Hmeaning;
  eapply Hmeaning;
  (* the premises restate the saved registers as their reloaded bytes *)
  parentHeader_saved_words;
  first [eassumption | split; eassumption].

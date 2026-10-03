Require Import ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import ZesuSsz.Automation.InteriorByteSlice.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
From iris.proofmode Require Import environments.

Lemma zesu_u64s_of_bytes_length count (bytes : list (bv 8)) :
  length (u64s_of_bytes count bytes) = count.
Proof. rewrite /u64s_of_bytes length_fmap length_reshape length_replicate. done. Qed.
#[export] Hint Rewrite zesu_u64s_of_bytes_length
  : lithium_rewrite isla_coq_rewrite zesu_indices.

Lemma zesu_byte_array_lend_words `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) (start count : nat)
    (Hbounds : (start + count * 8 <= length bytes)%nat) :
  base ↦ₘ∗ bytes -∗
  (base + Z.of_nat start) ↦ₘ∗
    u64s_of_bytes count (take (count * 8) (drop start bytes)) ∗
  ((base + Z.of_nat start) ↦ₘ∗
    u64s_of_bytes count (take (count * 8) (drop start bytes)) -∗
    base ↦ₘ∗ bytes).
Proof.
  iIntros "Hbytes".
  iDestruct (zesu_byte_array_word_region base (DfracOwn 1) bytes start count
    Hbounds with "Hbytes") as "(Hprefix & Hwords & Hsuffix)".
  have Hlength : length (take (count * 8) (drop start bytes)) = (count * 8)%nat.
  { rewrite length_take length_drop. lia. }
  have Hwords : bytes_of_u64s
      (u64s_of_bytes count (take (count * 8) (drop start bytes))) =
      take (count * 8) (drop start bytes).
  { apply bytes_of_u64s_of_bytes. exact Hlength. }
  iFrame "Hwords". iIntros "Hwords".
  iDestruct (mem_mapsto_u64_array_to_bytes with "Hwords") as "Hslice".
  iEval (rewrite Hwords) in "Hslice".
  have Hstride : Z.of_N (8 / 8) = 1%Z by vm_compute.
  iPoseProof (mem_mapsto_array_app_combine_at 8%N base (DfracOwn 1)
    (take start bytes) (take (count * 8) (drop start bytes)) start
    with "Hprefix [Hslice]") as "Hfirst".
  { rewrite length_take. lia. }
  { rewrite Hstride Z.mul_1_l. iExact "Hslice". }
  iPoseProof (mem_mapsto_array_app_combine_at 8%N base (DfracOwn 1)
    (take start bytes ++ take (count * 8) (drop start bytes))
    (drop (start + count * 8) bytes) (start + count * 8)
    with "Hfirst [Hsuffix]") as "Hwhole".
  { rewrite length_app !length_take length_drop. lia. }
  { rewrite Hstride Z.mul_1_l. iExact "Hsuffix". }
  rewrite -drop_drop -app_assoc take_drop take_drop.
  iExact "Hwhole".
Qed.

Lemma subsume_byte_array_word_region `{!islaG Sigma} A
    (base address : Z) (bytes : list (bv 8)) (start count : nat)
    (wanted : A -> list (bv 64)) (G : A -> iProp Sigma) :
  (⌜address = (base + Z.of_nat start)%Z⌝ ∗
   ⌜(start + count * 8 <= length bytes)%nat⌝ ∗
   ∃ x : A, ⌜wanted x = u64s_of_bytes count (take (count * 8) (drop start bytes))⌝ ∗
     ((address ↦ₘ∗ wanted x -∗ base ↦ₘ∗ bytes) -∗ G x))%I ⊢
  subsume (base ↦ₘ∗ bytes) (fun x => address ↦ₘ∗ wanted x) G.
Proof.
  iIntros "(%Haddress & %Hbounds & %x & %Hwords & Hnext) Hbytes".
  iDestruct (zesu_byte_array_lend_words base bytes start count Hbounds
    with "Hbytes") as "[Hwords Hrestore]".
  rewrite Haddress Hwords.
  iExists x. rewrite Hwords. iFrame "Hwords".
  iApply "Hnext". iExact "Hrestore".
Qed.


Ltac zesu_lend_byte_words :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (subsume (?base ↦ₘ∗ ?bytes) ?wanted ?G) =>
      lazymatch type of bytes with list (bv 8) => idtac end;
      let A := lazymatch type of wanted with ?A -> _ => A end in
      let witness := zesu_tuple_witness A in
      let target := eval cbv beta iota delta [li_fst] in (wanted witness) in
      lazymatch target with (?address ↦ₘ∗ ?words)%I =>
        lazymatch type of words with list (bv 64) => idtac end;
        has_evar words;
        let start := lazymatch address with
          | (base + ?offset)%Z => eval vm_compute in (Z.to_nat offset)
          | base => constr:(0%nat)
          end in
        let size := match goal with Hlength : length bytes = ?size |- _ => size end in
        let count := eval vm_compute in ((size - start) / 8)%nat in
        let packed := constr:(u64s_of_bytes count (take (count * 8) (drop start bytes))) in
        unify words packed;
        iApply (subsume_byte_array_word_region A base address bytes start count);
        iSplit; first (iPureIntro; lia);
        iSplit; first (iPureIntro; lia);
        iExists witness; iSplit; first done;
        let Hrestore := iFresh in iIntros Hrestore;
        let borrowed := fresh "borrowed_words" in
        set (borrowed := packed) in *;
        let Hpacked := fresh "Hborrowed_words" in
        assert (Hpacked : borrowed = packed) by reflexivity;
        let Hlength := fresh "Hborrowed_length" in
        assert (Hlength : length borrowed = count) by
          (unfold borrowed; apply zesu_u64s_of_bytes_length);
        clearbody borrowed;
        zesu_expose_environment_alias;
        let Hpacking := iFresh in
        iAssert (⌜borrowed = packed⌝%I) as Hpacking;
        [iPureIntro; exact Hpacked | clear Hpacked]
      end
  end.



Class ZesuStepByteWordSlice : Prop := zesu_step_byte_word_slice : True.
Ltac zesu_lend_byte_words_if_enabled :=
  let _ := constr:(_ : ZesuStepByteWordSlice) in zesu_lend_byte_words.

Ltac zesu_open_byte_word_seal :=
  let _ := constr:(_ : ZesuStepByteWordSlice) in
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T ?body) =>
    constr_eq T (li_prod (list (bv 64)) unit);
    let witness := constr:((@nil (bv 64), tt)ₗ) in
    let opened := eval cbv beta iota delta [li_fst] in (body witness) in
    lazymatch opened with ((?address ↦ₘ∗ ?words) ∗ _)%I =>
      lazymatch type of words with list (bv 64) => idtac end;
      assert_fails (has_evar address);
      zesu_open_declared_byte_slice address 8%nat
    end
  end.

Ltac zesu_lend_byte_word_existential :=
  let _ := constr:(_ : ZesuStepByteWordSlice) in
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?A ?body) =>
    let witness := zesu_tuple_witness A in
    let opened := eval cbv beta iota delta [li_fst] in (body witness) in
    lazymatch opened with ((?address ↦ₘ∗ ?words) ∗ _)%I =>
      lazymatch type of words with list (bv 64) => idtac end;
      has_evar words;
      iMatchHyp ltac:(fun Hbytes resource =>
        lazymatch resource with (?base ↦ₘ∗ ?bytes)%I =>
          lazymatch type of bytes with list (bv 8) => idtac end;
          let start := lazymatch address with
            | (base + ?offset)%Z => eval vm_compute in (Z.to_nat offset)
            | base => constr:(0%nat)
            end in
          let size := match goal with Hlength : length bytes = ?size |- _ => size end in
          let Hcover := fresh "HwordCoverage" in
          assert (Hcover : (start + 8 <= length bytes)%nat) by lia;
          clear Hcover;
          let count := eval vm_compute in ((size - start) / 8)%nat in
          let packed := constr:(u64s_of_bytes count (take (count * 8) (drop start bytes))) in
          unify words packed;
          iExists witness;
          let borrowed := fresh "borrowed_words" in
          set (borrowed := packed) in *;
          let Hpacked := fresh "Hborrowed_words" in
          assert (Hpacked : borrowed = packed) by reflexivity;
          let Hlength := fresh "Hborrowed_length" in
          assert (Hlength : length borrowed = count) by
            (unfold borrowed; apply zesu_u64s_of_bytes_length);
          let Hbounds := fresh "HwordBounds" in
          assert (Hbounds : (start + count * 8 <= length bytes)%nat) by lia;
          iDestruct (zesu_byte_array_lend_words base bytes start count Hbounds with Hbytes) as "[Hwords Hrestore]";
          clear Hbounds;
          iEval (fold borrowed) in "Hwords Hrestore";
          iEval (cbn [Z.of_nat]) in "Hwords Hrestore";
          clearbody borrowed;
          let Hpacking := iFresh in
          iAssert (⌜borrowed = packed⌝%I) as Hpacking;
          [iPureIntro; exact Hpacked | clear Hpacked];
          cbn [li_fst];
          iFrame "Hwords"
        end)
    end
  end.

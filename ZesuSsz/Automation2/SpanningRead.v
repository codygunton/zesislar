Require Import isla.riscv64.riscv64.
From stdpp Require Import bitvector.definitions list.
From Coq Require Import ZArith.ZArith NArith.NArith Lia Lists.List.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation2.ByteArrays.
Require Import ZesuSsz.Automation2.LiaHook.
Require ZesuSsz.Automation2.WrappedWord.
Require ZesuSsz.Automation2.MemoryAddress.
Require ZesuSsz.Automation2.StoreMemoryLookup.
Require ZesuSsz.Automation2.ResourceGroups.
Require Import iris.proofmode.environments.
Local Open Scope Z_scope.

(* A read of 2, 4 or 8 bytes whose first byte lies in a held byte array and
   whose last bytes lie in the uninitialised region right after it (a 16-byte
   struct copied with two 8-byte loads, where the struct is held as a word and
   a flag byte followed by seven padding bytes: the second load reads the flag
   and the padding). No single resource owns the read. The region is owned
   memory of unknown content: the read is of the array followed by some bytes
   `values` of the region's size, and both pieces are given back as they
   were. *)
Section spanning_read.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma zesu_read_mem_span len n kind (a : bv 64) (vread : bv n) tag ann es
      (B B2 off N m : Z) (l : list (bv 8)) :
    n = (8 * len)%N → len ≠ 0%N → n ≠ 8%N → zesu_byte_access_size len = true →
    bv_unsigned a = B + off → 0 ≤ off → Z.of_nat (length l) = N → B2 = B + N → 0 < m →
    off + Z.of_N len ≤ N + m →
    B ↦ₘ∗ l -∗ B2 ↦ₘ? m -∗
    (∀ values : list (bv 8), ⌜Z.of_nat (length values) = m⌝ -∗
       ⌜vread = Z_to_bv n (little_endian_to_bv 8
          (take (N.to_nat len) (drop (Z.to_nat off) (l ++ values))))⌝ -∗
       B ↦ₘ∗ l -∗ B2 ↦ₘ? m -∗ WPasm es) -∗
    WPasm (ReadMem (RVal_Bits (@bv_to_bvn n vread)) kind
      (RVal_Bits (@bv_to_bvn 64 a)) len tag ann :t: es).
  Proof.
    intros Hn Hlen Hn8 Hsize Ha Hoff Hl -> Hm Hend.
    iIntros "Hl Hu HK".
    iDestruct (mem_mapsto_uninit_to_byte_array with "Hu") as (values Hv) "Hv".
    iDestruct (mem_mapsto_array_app_combine_at 8 B _ l values (length l) eq_refl
      with "Hl [Hv]") as "Hlv".
    { change (Z.of_N (8 `div` 8)) with 1%Z. rewrite Z.mul_1_l Hl. iExact "Hv". }
    iApply li_wp_read_mem_zesu. iSplit; [done|]. iSplit; [done|].
    rewrite /find_in_context /=.
    iExists (MKArray 8%N B (l ++ values)). rewrite /mem_mapsto_kind_prop /=. iFrame "Hlv".
    have Hq : (8 =? n)%N = false by apply N.eqb_neq; congruence.
    change (match n with 0%N => false | N.pos q => (8 =? q)%positive end) with (8 =? n)%N.
    rewrite Hq; try rewrite Hsize.
    iSplit; [done|]. iExists (Z.to_nat off).
    iSplit; [iPureIntro; lia|]. iSplit.
    { iPureIntro. rewrite length_app. lia. }
    iIntros (vmem Hvmem Hvread) "Hlv".
    iDestruct (mem_mapsto_array_app with "Hlv") as "[Hl Hv]".
    iDestruct (mem_mapsto_byte_array_to_mapsto_len (length values) with "Hv") as "Hw";
      first reflexivity.
    iDestruct (mem_mapsto_mapsto_to_uninit with "Hw") as "Hu".
    have Hval : vread = Z_to_bv n (little_endian_to_bv 8
      (take (N.to_nat len) (drop (Z.to_nat off) (l ++ values)))) by rewrite Hvread Hvmem.
    iApply ("HK" $! values with "[//] [//] Hl [Hu]").
    iEval (change (Z.of_N (8 `div` 8)) with 1%Z; rewrite Z.mul_1_l Hl) in "Hu".
    iEval (rewrite N.mul_comm N.div_mul //) in "Hu". rewrite -Hv -nat_N_Z. iExact "Hu".
  Qed.
End spanning_read.

(* The address of a read is often a local definition of the block (a `LET`
   binder of the trace, possibly over other `LET` binders, under which the
   stack root lies): its root is unfolded until it is no local definition. *)
Ltac zesu_span_unfold_root A :=
  let r := ZesuSsz.Automation2.WrappedWord.zesu_term_root A in
  match goal with
  | [ x := _ |- _ ] =>
      match r with
      | context [x] =>
          let A' := eval cbv delta [x] in A in
          zesu_span_unfold_root A'
      end
  | _ => A
  end.

(* The numeral length [N] of a held byte list [l] (its spine, or a length
   fact), passed to [k] with the fact `Z.of_nat (length l) = N`. *)
Ltac zesu_span_array_length l k :=
  let Hl := fresh "HspanLength" in
  first
  [ let c := ZesuSsz.Automation2.StoreMemoryLookup.zesu_spine_length l in
    let N := eval vm_compute in (Z.of_nat c) in
    assert (Hl : Z.of_nat (length l) = N) by reflexivity
  | match goal with
    | Hlen : length l = ?c |- _ =>
        let N := eval vm_compute in (Z.of_nat c) in
        assert (Hl : Z.of_nat (length l) = N) by (rewrite Hlen; reflexivity)
    end ];
  lazymatch type of Hl with _ = ?N => k N Hl end.

(* The step: on a read of [len] bytes (2, 4 or 8) at address [a], a held byte
   array at [B] (on the same root as [a]) of numeral length [N] in which the
   read starts and past whose end it goes, and the uninitialised region right
   after the array, of closed size covering the rest of the read. The offset
   is aimed at by evaluation at a sample root and then proved. *)
Ltac zesu_read_span :=
  lazymatch goal with
  | |- environments.envs_entails _ (WPasm (ReadMem (RVal_Bits (@bv_to_bvn ?n ?vread)) ?kind
        (RVal_Bits (@bv_to_bvn 64 ?a)) ?len ?tag ?ann :t: ?es)) =>
      lazymatch eval vm_compute in (zesu_byte_access_size len && negb (len =? 1)%N) with
      | true => idtac end;
      let lz := eval vm_compute in (Z.of_N len) in
      let A := zesu_span_unfold_root constr:(bv_unsigned a) in
      let ra := ZesuSsz.Automation2.WrappedWord.zesu_term_root A in
      try ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
      iMatchHyp ltac:(fun H res =>
        lazymatch res with
        | (?B ↦ₘ∗ ?l)%I =>
            lazymatch type of l with list (bv 8) => idtac end;
            let rb := ZesuSsz.Automation2.WrappedWord.zesu_term_root B in
            constr_eq ra rb;
            let off := ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root ra constr:((A - B)%Z) in
            lazymatch off with Z0 => idtac | Zpos _ => idtac end;
            zesu_span_array_length l ltac:(fun N Hl =>
              lazymatch eval vm_compute in (Z.ltb off N && Z.ltb N (off + lz)) with
              | true => idtac end;
              iMatchHyp ltac:(fun H2 res2 =>
                lazymatch res2 with
                | (?B2 ↦ₘ? ?m0)%I =>
                    ZesuSsz.Automation2.StoreMemoryLookup.zesu_root_offset_is ra B B2 N;
                    let m := ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root ra m0 in
                    lazymatch m with Zpos _ => idtac end;
                    lazymatch eval vm_compute in (Z.leb (off + lz) (N + m)) with
                    | true => idtac end;
                    let Hm := fresh "HspanRegion" in
                    assert (Hm : m0 = m) by (clear; ZesuSsz.Automation2.WrappedWord.zesu_plain_lia);
                    let Hb := fresh "HspanAdjacent" in
                    assert (Hb : B2 = (B + N)%Z) by (clear; ZesuSsz.Automation2.WrappedWord.zesu_plain_lia);
                    let Ha := fresh "HspanAddress" in
                    assert (Ha : A = (B + off)%Z) by ZesuSsz.Automation2.MemoryAddress.zesu_stack_arithmetic;
                    iRename H into "HspanArray"; iRename H2 into "HspanRegion";
                    iApply (zesu_read_mem_span len n kind a vread tag ann es B B2 off N m0 l
                      eq_refl ltac:(discriminate) ltac:(discriminate) eq_refl
                      Ha ltac:(clear; zesu_lia) Hl Hb ltac:(clear - Hm; zesu_lia)
                      ltac:(clear - Hm; zesu_lia) with "HspanArray HspanRegion");
                    clear Hm Hb Ha Hl
                end))
        end)
  end.

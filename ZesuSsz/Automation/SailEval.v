From Coq Require Import Bool List String ZArith Lia Logic.Eqdep_dec.
Require Import SailStdpp.MachineWord SailStdpp.Values SailStdpp.Prompt_monad.
Require Import SailStdpp.Prompt SailStdpp.Operators_mwords SailStdpp.Instances.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types EvmSailRlp.evm_rlp.
Require Import ZesuSsz.Compliance.SailRun.
Import ListNotations.
Open Scope Z_scope.

Create HintDb zesu_sail.

Lemma sail_run_bind {A B} (action : M A) (next : A -> M B) rs allow :
  runPrompt (SailStdpp.Prompt_monad.bind action next) rs allow =
  match runPrompt action rs allow with
  | (Success value, nextState) => runPrompt (next value) nextState allow
  | (Reject error, nextState) => (Reject error, nextState)
  | (UnsupportedOrInternalFailure message, nextState) =>
      (UnsupportedOrInternalFailure message, nextState)
  end.
Proof.
  revert rs. induction action; intros rs; cbn; try reflexivity.
  - apply H.
  - apply IHaction.
  - destruct (andb allow (String.eqb s "exit")); reflexivity.
Qed.

Lemma sail_run_bind_assoc {A B C} (action : M A)
    (next : A -> M B) (last : B -> M C) rs allow :
  runPrompt (SailStdpp.Prompt_monad.bind
    (SailStdpp.Prompt_monad.bind action next) last) rs allow =
  runPrompt (SailStdpp.Prompt_monad.bind action
    (fun value => SailStdpp.Prompt_monad.bind (next value) last)) rs allow.
Proof.
  rewrite !sail_run_bind.
  destruct (runPrompt action rs allow) as [[value|error|message] nextState];
    cbn; [symmetry; apply sail_run_bind | reflexivity | reflexivity].
Qed.

Lemma sail_uint_unsigned width (value : mword width) :
  uint value = bv_unsigned value.
Proof.
  unfold uint, MachineWord.word_to_N, SailStdpp.Values.get_word.
  rewrite Z2N.id; first reflexivity.
  exact (proj1 (bv_unsigned_in_range _ value)).
Qed.

#[export] Hint Rewrite sail_uint_unsigned : zesu_sail.
#[export] Hint Rewrite Z_to_bv_unsigned : zesu_sail.
#[export] Hint Rewrite register_lookup_set : zesu_sail.
#[export] Hint Rewrite irrelevant_register_set
  using (first [assumption | reflexivity]) : zesu_sail.

Ltac sail_guard_solver :=
  unbool_comparisons; unbool_comparisons_goal; lia.

Ltac sail_guard :=
  first
    [ match goal with |- context [Z.ltb ?x ?y] =>
        first [rewrite (proj2 (Z.ltb_lt x y) ltac:(sail_guard_solver))
              |rewrite (proj2 (Z.ltb_ge x y) ltac:(sail_guard_solver))
              |let Hguard := fresh "HsailGuard" in destruct (Z.ltb x y) eqn:Hguard]
      end
    | match goal with |- context [Z.leb ?x ?y] =>
        first [rewrite (proj2 (Z.leb_le x y) ltac:(sail_guard_solver))
              |rewrite (proj2 (Z.leb_gt x y) ltac:(sail_guard_solver))
              |let Hguard := fresh "HsailGuard" in destruct (Z.leb x y) eqn:Hguard]
      end
    | match goal with |- context [Z.eqb ?x ?y] =>
        first [rewrite (proj2 (Z.eqb_eq x y) ltac:(sail_guard_solver))
              |rewrite (proj2 (Z.eqb_neq x y) ltac:(sail_guard_solver))
              |let Hguard := fresh "HsailGuard" in destruct (Z.eqb x y) eqn:Hguard]
      end ].

Ltac sail_context_rewrite := match goal with H : ?lhs = ?rhs |- context [ ?lhs ] => tryif is_var lhs then (fail 0) else (progress (rewrite H)) end.

Create HintDb zesu_sail_rec.
Ltac sail_rec_step :=
  multimatch goal with
  | |- context [?recursive ?access] =>
    lazymatch type of access with
    | Acc (Zwf 0) ?fuel =>
      tryif is_closed_term fuel then
        (let Hbound := fresh "HsailRecBound" in
         assert (Hbound : 0 <= fuel <= 8) by lia;
         progress (autounfold_one with zesu_sail_rec))
      else
        (let Hcases := fresh "HsailRecCases" in
         assert (Hcases : fuel = 0 \/ fuel = 1 \/ fuel = 2 \/ fuel = 3 \/
           fuel = 4 \/ fuel = 5 \/ fuel = 6 \/ fuel = 7 \/ fuel = 8) by lia;
         repeat lazymatch type of Hcases with _ \/ _ => destruct Hcases as [Hcases|Hcases] end;
         progress (rewrite Hcases in *))
    end
  end.

Ltac sail_eval_base :=
  intros;
  repeat first
    [ reflexivity
    | progress (cbn [List.length] in *)
    | sail_context_rewrite
    | progress (autorewrite with zesu_sail)
    | progress (cbn [SailStdpp.Prompt_monad.bind0
        SailStdpp.Prompt_monad.bind SailStdpp.Prompt_monad.returnm
        SailStdpp.Prompt_monad.read_reg SailStdpp.Prompt.and_boolM
        assert_exp' runPrompt List.length andb
        EvmSailRlp.evm_rlp.shim_byte_at
        stateless_input_length_value StatelessInputSliceFields_len])
    | progress (autounfold_one with sail)
    | sail_guard
    | sail_rec_step ];
  try reflexivity.


Lemma sail_run_shim_byte_nat bytes index value rs allow :
  nth_error bytes index = Some value ->
  runPrompt (EvmSailRlp.evm_rlp.shim_byte_at bytes (Z.of_nat index)) rs allow =
    (Success value, rs).
Proof.
  revert index value. induction bytes as [|head tail IH];
    intros [|index] value Hlookup; simpl in Hlookup; try discriminate.
  - inversion Hlookup; subst. reflexivity.
  - cbn [EvmSailRlp.evm_rlp.shim_byte_at].
    replace (Z.of_nat (S index) - 1) with (Z.of_nat index) by lia.
    apply IH. exact Hlookup.
Qed.

Lemma sail_run_shim_byte bytes offset value rs allow :
  0 <= offset -> nth_error bytes (Z.to_nat offset) = Some value ->
  runPrompt (EvmSailRlp.evm_rlp.shim_byte_at bytes offset) rs allow =
    (Success value, rs).
Proof.
  intros Hoffset Hlookup.
  replace offset with (Z.of_nat (Z.to_nat offset)) at 1 by (rewrite Z2Nat.id; lia).
  apply sail_run_shim_byte_nat. exact Hlookup.
Qed.
Ltac sail_positive_literal term :=
  lazymatch term with
  | xH => idtac
  | xO ?tail => sail_positive_literal tail
  | xI ?tail => sail_positive_literal tail
  end.
Ltac sail_nat_literal term :=
  lazymatch term with O => idtac | S ?tail => sail_nat_literal tail end.
Ltac sail_reduce_closed term :=
  tryif has_evar term then (fail 0) else idtac;
  is_closed_term term;
  let reduced := eval cbv in term in
  lazymatch reduced with
  | true => idtac
  | false => idtac
  | Z0 => idtac
  | Zpos ?p => sail_positive_literal p
  | Zneg ?p => sail_positive_literal p
  | O => idtac
  | S ?n => sail_nat_literal n
  end;
  progress (change term with reduced).

Ltac sail_closed_arith :=
  multimatch goal with
  | |- context [bv_wrap ?width ?value] => sail_reduce_closed (bv_wrap width value)
  | |- context [Z.sub ?x ?y] => sail_reduce_closed (Z.sub x y)
  | |- context [Z.add ?x ?y] => sail_reduce_closed (Z.add x y)
  | |- context [Z.eqb ?x ?y] => sail_reduce_closed (Z.eqb x y)
  | |- context [Z.geb ?x ?y] => sail_reduce_closed (Z.geb x y)
  | |- context [Z.leb ?x ?y] => sail_reduce_closed (Z.leb x y)
  | |- context [Z.ltb ?x ?y] => sail_reduce_closed (Z.ltb x y)
  | |- context [Z.to_nat ?x] => sail_reduce_closed (Z.to_nat x)
  end.
Ltac sail_list_step :=
  multimatch goal with |- context [?xs] =>
    lazymatch type of xs with list ?T =>
      is_var xs;
      let Hnonempty := fresh "HsailNonempty" in
      assert (Hnonempty : (0 < length xs)%nat) by lia;
      destruct xs; [cbn [length] in Hnonempty; lia|]
    end
  end.
#[export] Hint Rewrite @sail_run_bind @firstn_O : zesu_sail.
#[export] Hint Rewrite sail_run_shim_byte
  using (first [assumption | reflexivity | lia]) : zesu_sail.
Ltac sail_eval_next :=
  intros;
  repeat first
    [ reflexivity
    | progress (cbn [List.length] in *)
    | progress (cbn [SailStdpp.Prompt_monad.bind0
        SailStdpp.Prompt_monad.bind SailStdpp.Prompt_monad.returnm
        SailStdpp.Prompt_monad.read_reg SailStdpp.Prompt.and_boolM
        assert_exp' runPrompt List.length andb List.firstn List.fold_left
        EvmSailRlp.evm_rlp.shim_byte_at
        stateless_input_length_value StatelessInputSliceFields_len])
    | sail_closed_arith
    | sail_context_rewrite
    | progress (autorewrite with zesu_sail)
    | progress (autounfold_one with sail)
    | sail_guard
    | sail_list_step ];
  try solve [repeat first [reflexivity | lia | f_equal]].

Ltac sail_eval :=
  sail_eval_base;
  cbn [Zwf_guarded pos_guard_wf _limit_reduces_bool _limit_reduces Acc_inv];
  sail_eval_next.


(* The library Z_idx_eq_dep uses EqdepTheory.eq_dep_eq.
   These transport helpers use decidable equality to avoid eq_rect_eq. *)
Lemma sail_Z_idx_eq_dep (T : N -> Type) m n
    (x : T (MachineWord.Z_idx m)) (y : T (MachineWord.Z_idx n)) :
  m > 0 -> n > 0 -> EqdepFacts.eq_dep N T _ x _ y ->
  EqdepFacts.eq_dep Z (fun size => T (MachineWord.Z_idx size)) _ x _ y.
Proof.
  intros Hm Hn Hdep.
  assert (m = n) as Heq.
  { inversion Hdep. apply Z2Nat.inj; auto with zarith. }
  subst n.
  apply (Eqdep_dec.eq_dep_eq_dec N.eq_dec) in Hdep.
  subst y. constructor.
Qed.
Print Assumptions sail_Z_idx_eq_dep.

Lemma sail_to_word_to_word_nat n (w : MachineWord.word (MachineWord.Z_idx n)) :
  n > 0 -> to_word w = TypeCasts.autocast (to_word_idx w).
Proof.
  intros Hn. apply (Eqdep_dec.eq_dep_eq_dec Z.eq_dec).
  eapply EqdepFacts.eq_dep_trans.
  2: apply TypeCasts.autocast_eq_dep.
  2: (apply MachineWord.idx_Z_idx; lia).
  unfold to_word_idx, to_word, mword.
  apply sail_Z_idx_eq_dep; [assumption|rewrite MachineWord.idx_Z_idx; lia|].
  apply cast_idx_eq_dep. constructor.
Qed.
Print Assumptions sail_to_word_to_word_nat.

Lemma sail_get_slice_int (width value offset : Z) :
  0 < width -> 0 <= offset ->
  get_slice_int width value offset =
    Z_to_bv (Z.to_N width) (Z.shiftr value offset).
Proof.
  intros Hwidth Hoffset. rewrite get_slice_int_eta. unfold get_slice_int'.
  rewrite (proj2 (Z.geb_ge width 0) ltac:(lia)). cbn.
  unfold subrange_vec_dec.
  replace (offset + width - 1 - offset + 1) with width by lia.
  rewrite TypeCasts.autocast_refl.
  rewrite <- sail_to_word_to_word_nat by lia.
  unfold to_word, MachineWord.slice, get_word, mword_of_int,
    MachineWord.Z_to_word, MachineWord.Z_idx.
  apply bv_eq. rewrite bv_extract_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. rewrite !Z2N.id by lia.
  replace (offset + width - 1 + 1) with (offset + width) by lia.
  apply Z.bits_inj. intro index.
  destruct (Z_lt_ge_dec index 0) as [Hnegative|Hnonnegative].
  { rewrite !Z.testbit_neg_r by lia. reflexivity. }
  destruct (Z_lt_ge_dec index width) as [Hlow|Hhigh].
  { rewrite !Z.mod_pow2_bits_low by lia.
    rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity. }
  rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Print Assumptions sail_get_slice_int.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Ltac2 rec sail_last_ident (xs : ident list) :=
  match xs with
  | [] => Control.zero (Tactic_failure None)
  | x :: tail => match tail with [] => x | _ => sail_last_ident tail end
  end.
Ltac2 sail_generated_head_check (head : constr) :=
  match Constr.Unsafe.kind head with
  | Constr.Unsafe.Constant c _ =>
      let name := Ident.to_string (sail_last_ident (Env.path (Std.ConstRef c))) in
      if Int.lt (String.length name) 5 then Control.zero (Tactic_failure None)
      else
        if Bool.and (Char.equal (String.get name 0) (Char.of_int 95))
          (Bool.and (Char.equal (String.get name 1) (Char.of_int 114))
          (Bool.and (Char.equal (String.get name 2) (Char.of_int 101))
          (Bool.and (Char.equal (String.get name 3) (Char.of_int 99))
                    (Char.equal (String.get name 4) (Char.of_int 95)))))
        then () else Control.zero (Tactic_failure None)
  | _ => Control.zero (Tactic_failure None)
  end.
Ltac sail_generated_head head :=
  let check := ltac2:(head |- sail_generated_head_check (Option.get (Ltac1.to_constr head))) in
  check head.
Ltac sail_generated_step :=
  match goal with
  | |- context [runPrompt (?fn ?fuel ?access) ?rs ?allow] =>
    let head := get_head fn in
    sail_generated_head head;
    lazymatch type of access with Acc (Zwf 0) fuel => idtac end;
    lazymatch fuel with
    | Z.pos _ => idtac
    | Z.succ _ => idtac
    end;
    unfold head at 1; cbn [Zwf_guarded]; fold head
  end.
Ltac sail_eval_generated_budget budget :=
  sail_eval;
  first [reflexivity |
    lazymatch budget with
    | S ?remaining => sail_generated_step; sail_eval_generated_budget remaining
    end].
Ltac sail_eval_generated := sail_eval_generated_budget 8%nat.


Lemma sail_run_indexed_loop {State A : Type}
    (loop : nat -> State -> M A)
    (advance : nat -> State -> M State)
    (invariant : nat -> State -> Prop) (result : A) rs allow :
  (forall state, invariant O state ->
    runPrompt (loop O state) rs allow = (Success result, rs)) ->
  (forall remaining state, invariant (S remaining) state ->
    runPrompt (loop (S remaining) state) rs allow =
    runPrompt (SailStdpp.Prompt_monad.bind
      (advance remaining state) (loop remaining)) rs allow) ->
  (forall remaining state, invariant (S remaining) state ->
    exists next, runPrompt (advance remaining state) rs allow =
      (Success next, rs) /\ invariant remaining next) ->
  forall remaining state, invariant remaining state ->
    runPrompt (loop remaining state) rs allow = (Success result, rs).
Proof.
  intros Hzero Hstep Hadvance remaining.
  induction remaining as [|remaining IH]; intros state Hinvariant.
  - exact (Hzero state Hinvariant).
  - destruct (Hadvance remaining state Hinvariant) as [next [Hrun Hnext]].
    rewrite (Hstep remaining state Hinvariant).
    rewrite sail_run_bind. rewrite Hrun. exact (IH next Hnext).
Qed.
Print Assumptions sail_run_indexed_loop.

Definition sail_load_state : Type :=
  ({ fuel : Z & Acc (Zwf 0) fuel } * (Z * Z))%type.
Definition sail_shim_loop {sourceOff sourceLen}
    (slice : StatelessInputSliceFields sourceOff sourceLen)
    (remaining : nat) (state : sail_load_state) : M Z :=
  let '(existT fuel access, (off, value)) := state in
  EvmSailRlp.evm_rlp._rec_shim_load_n slice off
    (Z.of_nat remaining) value fuel access.
Definition sail_shim_advance {sourceOff sourceLen}
    (slice : StatelessInputSliceFields sourceOff sourceLen)
    (state : sail_load_state) : M sail_load_state :=
  let '(existT fuel access, (off, value)) := state in
  assert_exp' (Z.geb fuel 0) "recursion limit reached" >>= fun H =>
  (if Z.ltb off sourceLen then
    read_reg shim_input_bytes >>= fun bytes =>
    EvmSailRlp.evm_rlp.shim_byte_at bytes (Z.add sourceOff off) >>= fun byte =>
    returnM (uint byte)
   else returnM 0) >>= fun next =>
  returnM (existT (Z.sub fuel 1) (_limit_reduces_bool access H),
    (Z.add off 1, Z.add (Z.mul value 256) next)).
Lemma sail_shim_loop_step sourceOff sourceLen
    (slice : StatelessInputSliceFields sourceOff sourceLen)
    remaining state rs allow :
  runPrompt (sail_shim_loop slice (S remaining) state) rs allow =
  runPrompt (SailStdpp.Prompt_monad.bind
    (sail_shim_advance slice state) (sail_shim_loop slice remaining)) rs allow.
Proof.
  destruct state as [[fuel access] [off value]]. destruct access.
  cbn [sail_shim_loop sail_shim_advance EvmSailRlp.evm_rlp._rec_shim_load_n].
  fold (@EvmSailRlp.evm_rlp._rec_shim_load_n).
  replace (Z.sub (Z.of_nat (S remaining)) 1) with (Z.of_nat remaining) by lia.
  repeat rewrite sail_run_bind_assoc.
  assert (Hzero : (Z.of_nat (S remaining) =? 0) = false) by (apply Z.eqb_neq; lia). rewrite Hzero. clear Hzero.
  repeat rewrite sail_run_bind.
  destruct (runPrompt (assert_exp' (Z.geb fuel 0) "recursion limit reached") rs allow) as [[guard|error|message] state] eqn:Hguard; cbv beta iota zeta; try reflexivity.
  rewrite sail_run_bind_assoc. repeat rewrite sail_run_bind.
  match goal with |- context [runPrompt ?action state allow] => destruct (runPrompt action state allow) as [[next|error2|message2] nextState] eqn:Hread end; cbv beta iota zeta; try reflexivity.
  all: match goal with Hread : runPrompt ?action ?registers ?permission = _ |- context [runPrompt ?other ?registers ?permission] => replace other with action by reflexivity; rewrite Hread end.
  all: cbn [sail_shim_loop SailStdpp.Prompt_monad.bind returnM]; reflexivity.
Qed.
Print Assumptions sail_shim_loop_step.

Definition sail_load_invariant sourceOff sourceLen (input : list byte)
    (expected : Z) (remaining : nat) (state : sail_load_state) : Prop :=
  let '(existT fuel access, (off, value)) := state in
  0 <= off /\ Z.of_nat remaining <= Z.sub sourceLen off /\
  Z.of_nat remaining <= fuel /\
  expected = fold_left (fun accumulator (item : byte) =>
    Z.add (Z.mul accumulator 256) (@uint 8 item))
    (firstn remaining (skipn (Z.to_nat (Z.add sourceOff off)) input)) value.
Lemma sail_firstn_skipn_read {T} (input : list T) index value count :
  nth_error input index = Some value ->
  firstn (S count) (skipn index input) =
  value :: firstn count (skipn (S index) input).
Proof.
  revert index value. induction input as [|head tail IH];
    intros [|index] value Hlookup; cbn in Hlookup; try discriminate.
  - inversion Hlookup; subst. reflexivity.
  - cbn. apply IH. exact Hlookup.
Qed.
Print Assumptions sail_firstn_skipn_read.
Lemma sail_shim_loop_base sourceOff sourceLen
    (slice : StatelessInputSliceFields sourceOff sourceLen)
    input expected state rs allow :
  sail_load_invariant sourceOff sourceLen input expected O state ->
  runPrompt (sail_shim_loop slice O state) rs allow = (Success expected, rs).
Proof.
  intros Hinvariant. destruct state as [[fuel access] [off value]]. cbn [sail_load_invariant] in Hinvariant. destruct Hinvariant as [Hoff [Hslice [Hfuel Hresult]]].
  rewrite firstn_O in Hresult. cbn [List.fold_left] in Hresult. subst expected. destruct access.
  cbn [sail_shim_loop EvmSailRlp.evm_rlp._rec_shim_load_n]. replace (Z.of_nat O =? 0) with true by reflexivity. cbv beta iota zeta.
  assert (Hguard : Z.geb fuel 0 = true) by (apply Z.geb_ge; lia). rewrite Hguard.
  reflexivity.
Qed.
Print Assumptions sail_shim_loop_base.
Lemma sail_run_assert_true condition message (Htrue : condition = true) rs allow :
  runPrompt (assert_exp' condition message) rs allow = (Success Htrue, rs).
Proof.
  subst condition.
  first [reflexivity |
    match goal with H : true = true |- _ =>
      replace H with (eq_refl true) by
        (apply (@Eqdep_dec.UIP_dec bool Coq.Bool.Bool.bool_dec));
      reflexivity
    end].
Qed.
Print Assumptions sail_run_assert_true.
Lemma sail_shim_advance_invariant sourceOff sourceLen
    (slice : StatelessInputSliceFields sourceOff sourceLen)
    (input : list byte) expected remaining state rs allow :
  0 <= sourceOff ->
  Z.add sourceOff sourceLen <= Z.of_nat (length input) ->
  register_lookup shim_input_bytes rs = input ->
  sail_load_invariant sourceOff sourceLen input expected (S remaining) state ->
  exists next, runPrompt (sail_shim_advance slice state) rs allow =
    (Success next, rs) /\
    sail_load_invariant sourceOff sourceLen input expected remaining next.
Proof.
  intros Hsource Hbound Hinput Hinvariant. destruct state as [[fuel access] [off value]]. cbn [sail_load_invariant] in Hinvariant. destruct Hinvariant as [Hoff [Hslice [Hfuel Hresult]]].
  assert (Hguard : Z.geb fuel 0 = true) by (apply Z.geb_ge; lia). assert (Hinside : Z.ltb off sourceLen = true) by (apply Z.ltb_lt; lia).
  assert (Hindex : (Z.to_nat (Z.add sourceOff off) < length input)%nat) by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; lia).
  assert (Hsome : exists item, nth_error input (Z.to_nat (Z.add sourceOff off)) = Some item) by (assert (Hnotnone : nth_error input (Z.to_nat (Z.add sourceOff off)) <> None) by (apply nth_error_Some; exact Hindex); destruct (nth_error input (Z.to_nat (Z.add sourceOff off))) as [item|] eqn:Hlookup; [eauto|contradiction]). destruct Hsome as [item Hlookup].
  unfold sail_shim_advance. rewrite sail_run_bind. rewrite (sail_run_assert_true _ _ Hguard). cbv beta iota zeta. rewrite Hinside.
  repeat rewrite sail_run_bind_assoc. repeat rewrite sail_run_bind.
  change (runPrompt (read_reg shim_input_bytes) rs allow) with (Success (register_lookup shim_input_bytes rs), rs). rewrite Hinput. cbv beta iota zeta.
  repeat rewrite sail_run_bind_assoc. repeat rewrite sail_run_bind. rewrite (sail_run_shim_byte input (Z.add sourceOff off) item rs allow) by (first [assumption|lia]). cbv beta iota zeta.
  eexists. split; [reflexivity |].
  cbn [sail_load_invariant]. repeat split; try lia.
  assert (HnextIndex : Z.to_nat (Z.add sourceOff (Z.add off 1)) = S (Z.to_nat (Z.add sourceOff off))) by (replace (Z.add sourceOff (Z.add off 1)) with (Z.succ (Z.add sourceOff off)) by lia; rewrite Z2Nat.inj_succ by lia; reflexivity). rewrite HnextIndex.
  rewrite (sail_firstn_skipn_read input (Z.to_nat (Z.add sourceOff off)) item remaining Hlookup) in Hresult. cbn [List.fold_left] in Hresult. exact Hresult.
Qed.
Print Assumptions sail_shim_advance_invariant.

Lemma sail_run_shim_load_fold sourceOff sourceLen
    (slice : StatelessInputSliceFields sourceOff sourceLen)
    (input : list byte) remaining off value fuel access rs allow :
  0 <= sourceOff ->
  Z.add sourceOff sourceLen <= Z.of_nat (length input) ->
  register_lookup shim_input_bytes rs = input ->
  0 <= off -> Z.of_nat remaining <= Z.sub sourceLen off ->
  Z.of_nat remaining <= fuel ->
  runPrompt (EvmSailRlp.evm_rlp._rec_shim_load_n slice off
    (Z.of_nat remaining) value fuel access) rs allow =
  (Success (fold_left (fun accumulator (item : byte) =>
      Z.add (Z.mul accumulator 256) (@uint 8 item))
      (firstn remaining (skipn (Z.to_nat (Z.add sourceOff off)) input)) value), rs).
Proof.
  intros Hsource Hbound Hinput Hoff Hslice Hfuel.
  set (expected := fold_left (fun accumulator (item : byte) =>
    Z.add (Z.mul accumulator 256) (@uint 8 item))
    (firstn remaining (skipn (Z.to_nat (Z.add sourceOff off)) input)) value).
  change (runPrompt (sail_shim_loop slice remaining
    (existT fuel access, (off, value))) rs allow = (Success expected, rs)).
  eapply sail_run_indexed_loop with
    (advance := fun _ => sail_shim_advance slice)
    (invariant := sail_load_invariant sourceOff sourceLen input expected).
  - intros current Hinvariant.
    exact (@sail_shim_loop_base sourceOff sourceLen slice input expected
      current rs allow Hinvariant).
  - intros count current Hinvariant.
    exact (@sail_shim_loop_step sourceOff sourceLen slice count current rs allow).
  - intros count current Hinvariant.
    eapply sail_shim_advance_invariant; eauto.
  - cbn [sail_load_invariant]. repeat split; try assumption.
Qed.
Print Assumptions sail_run_shim_load_fold.

Lemma sail_run_shim_load_Z sourceOff sourceLen
    (slice : StatelessInputSliceFields sourceOff sourceLen)
    (input : list byte) remaining off value fuel access rs allow :
  0 <= sourceOff ->
  Z.add sourceOff sourceLen <= Z.of_nat (length input) ->
  register_lookup shim_input_bytes rs = input ->
  0 <= off -> 0 <= remaining -> remaining <= Z.sub sourceLen off ->
  remaining <= fuel ->
  runPrompt (EvmSailRlp.evm_rlp._rec_shim_load_n slice off
    remaining value fuel access) rs allow =
  (Success (fold_left (fun accumulator (item : byte) =>
      Z.add (Z.mul accumulator 256) (@uint 8 item))
      (firstn (Z.to_nat remaining) (skipn (Z.to_nat (Z.add sourceOff off)) input)) value), rs).
Proof.
  intros Hsource Hbound Hinput Hoff Hremaining Hslice Hfuel.
  pose proof (@sail_run_shim_load_fold sourceOff sourceLen slice input
    (Z.to_nat remaining) off value fuel access rs allow) as Hrun.
  rewrite Z2Nat.id in Hrun by assumption.
  apply Hrun; assumption.
Qed.
Print Assumptions sail_run_shim_load_Z.

Ltac sail_load_summary :=
  match goal with
  | |- context [runPrompt (@EvmSailRlp.evm_rlp._rec_shim_load_n
        ?sourceLen ?sourceOff ?slice ?off ?remaining ?value ?fuel ?access) ?rs ?allow] =>
    rewrite (@sail_run_shim_load_Z sourceOff sourceLen slice
      (register_lookup shim_input_bytes rs) remaining off value fuel access rs allow)
      by (first [reflexivity |
        repeat sail_context_rewrite;
        cbn [List.length word_byte_count_value] in *; lia])
  end.

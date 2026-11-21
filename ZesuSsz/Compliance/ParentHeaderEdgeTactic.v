(* Step 2.4 M1: the one proof of decodeParentHeader's edge obligations.
   Owner: compliance proof (hand-written, once). The generator declares, per
   edge into an error join, `fp_edge<src>_<join>_CandidateError`
   (Generated/DecodeParentHeader/FP301/EdgeObligations.v): from the source
   block's history, its visible facts and the edge's own guards, the candidate
   rejects the input. `ph_edge_error T` proves such a declaration with the
   failing field's terminal `T` (ParentHeaderCandidateFacts.v): open the
   history, read the guards as unsigned facts, apply `T`, then walk the
   registers back to the outer call through the named equations and the call
   records of the history (the fixed chain of the M1 lane). Pure lemmas and
   pure tactics only. *)
From Coq Require Import List ZArith Lia.
From stdpp Require Import base list numbers bitvector.definitions bitvector.tactics.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Require Import ZesuSsz.Contracts.NamedEquation.
Require Import ZesuSsz.Contracts.NextUint64CallData.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Interfaces.NextUint64.
Require Import ZesuSsz.Contracts.ParentHeaderCandidateWalk.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Compliance.ParentHeaderCandidateFacts.
Require Import ZesuSsz.Automation2.Hist.

Open Scope Z_scope.

(* The guards of an edge, as the code tests them, read as unsigned facts. *)
Lemma phGuardZeroExtendNe {n} (x : bv n) :
  (n <= 64)%N -> bv_zero_extend 64 x <> BV 64 0 -> bv_unsigned x <> 0.
Proof.
  intros Hn Hx Hu. apply Hx, bv_eq. rewrite bv_zero_extend_unsigned; [|lia]. rewrite Hu. done.
Qed.

Lemma phGuardZeroExtendEq {n} (x : bv n) :
  (n <= 64)%N -> bv_zero_extend 64 x = BV 64 0 -> bv_unsigned x = 0.
Proof.
  intros Hn Hx. apply (f_equal bv_unsigned) in Hx. rewrite bv_zero_extend_unsigned in Hx; [|lia]. exact Hx.
Qed.

Lemma phGuardNe (x : bv 64) : x <> BV 64 0 -> bv_unsigned x <> 0.
Proof. intros Hx Hu. apply Hx, bv_eq. rewrite Hu. done. Qed.

Lemma phGuardEq (x : bv 64) : x = BV 64 0 -> bv_unsigned x = 0.
Proof. intros ->. done. Qed.

Lemma phGuardSignedAbove (w : bv 64) :
  bv_signed (BV 128 8) < bv_signed (bv_zero_extend 128 w) -> 8 < bv_unsigned w.
Proof.
  rewrite zesu_signed_zero_extend_64_128. intros H. exact H.
Qed.

Ltac ph_edge_guard H :=
  first [ apply phGuardZeroExtendNe in H; [|vm_compute; congruence]
        | apply phGuardZeroExtendEq in H; [|vm_compute; congruence]
        | apply phGuardSignedAbove in H
        | apply phGuardNe in H
        | apply phGuardEq in H
        | idtac ].

(* Binders, the history (unfolded once), then the visible facts and guards. *)
Ltac ph_edge_intro :=
  hnf;
  let rec go :=
    lazymatch goal with
    | |- forall _ : ?T, _ =>
        lazymatch type of T with
        | Prop => let Hh := fresh "Hh" in intro Hh; hnf in Hh; intros
        | _ => intro; go
        end
    end in
  go.

Ltac ph_edge_open :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : ex _ |- _ => destruct H
  | H : zesu_join_history _ |- _ => unfold zesu_join_history in H
  | H : bool_decide _ = true |- _ => apply bool_decide_eq_true_1 in H; ph_edge_guard H
  | H : negb (bool_decide _) = true |- _ => apply negb_true_iff, bool_decide_eq_false_1 in H; ph_edge_guard H
  end.

(* A register passed on unchanged (a named equation to an earlier word). *)
Lemma phNamedNonzeroRename (l l' : bv 64) :
  zesu_named_eq l l' -> bv_unsigned l' <> 0 -> bv_unsigned l <> 0.
Proof. intros [->] Hl. exact Hl. Qed.

(* A register passed on as an earlier call's record field (the named
   equation states the field term, the history names the word by an equation
   `word = field`: 059c -> 0270). *)
Lemma phRegsFieldP args k (w t l : bv 64) :
  w = t -> phRegs args k w l -> phRegs args k t l.
Proof. intros -> H. exact H. Qed.

Lemma phRegsFieldL args k (p w t : bv 64) :
  w = t -> phRegs args k p w -> phRegs args k p t.
Proof. intros -> H. exact H. Qed.

Lemma phNamedNonzeroField (l w t : bv 64) :
  zesu_named_eq l t -> w = t -> bv_unsigned w <> 0 -> bv_unsigned l <> 0.
Proof. intros [->] -> Hl. exact Hl. Qed.

Ltac ph_edge_nonzero :=
  first [ assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption
        | eapply phNamedNonzeroRename; [eassumption|assumption]
        | eapply phNamedNonzeroField; [eassumption|eassumption|assumption] ].

Ltac ph_edge_side :=
  first [ eassumption | left; eassumption | right; eassumption | reflexivity
        | eapply parentHeaderCallC1B; eassumption | eassumption
        | left; reflexivity | right; ph_edge_nonzero | ph_edge_nonzero ].

Ltac ph_edge_chain :=
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; ph_edge_nonzero]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|ph_edge_nonzero|]
    | eapply phRegsFieldP; [eassumption|] | eapply phRegsFieldL; [eassumption|]].

(* The terminal is typed after the binders are introduced (it names them). *)
Tactic Notation "ph_edge_error" uconstr(T) :=
  ph_edge_intro; ph_edge_open;
  eapply T; [ph_edge_side ..|first [ph_edge_side | ph_edge_chain]].

(* `ph_edge_tag` proves an `ErrorTag` declaration (edges into 0x0270): the
   join's x10 is the edge's value, the constant 3 (block 0x026c) or
   nextUint64's result tag, which the edge's guard says is nonzero: then the
   tag is 3 (nextUint64RootStatusTag). *)
Ltac ph_edge_tag :=
  ph_edge_intro; ph_edge_open;
  match goal with H : ?x = _ |- bv_unsigned ?x = _ => rewrite H end;
  first [ reflexivity
        | rewrite bv_zero_extend_unsigned by lia; eapply nextUint64RootStatusTag;
          [eapply parentHeaderNextUint64Root; eassumption | assumption] ].

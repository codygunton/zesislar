Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

Lemma payload_call_witness_owned `{!islaG Sigma} `{!threadG}
    (address : Z) (bytes : list (bv 8)) (tail : spec) :
  address ↦ₘ∗ bytes ∗ mmio_range 0 16 ∗ spec_trace tail -∗
  ∃ witnesses : spec *ₗ list (bv 8) *ₗ unit,
    address ↦ₘ∗ witnesses.2ₗ ∗ mmio_range 0 16 ∗
    spec_trace witnesses.1ₗ ∗ True.
Proof.
  iIntros "(Hbytes & Hmmio & Htrace)".
  zesu_match_payload_witness. iFrame.
Qed.
Print Assumptions payload_call_witness_owned.

Lemma payload_call_witness_missing_resources `{!islaG Sigma} `{!threadG}
    (address : Z) (bytes : list (bv 8)) (tail : spec) :
  mmio_range 0 16 ∗ spec_trace tail -∗
  (∃ witnesses : spec *ₗ list (bv 8) *ₗ unit,
    address ↦ₘ∗ witnesses.2ₗ ∗ mmio_range 0 16 ∗
    spec_trace witnesses.1ₗ ∗ True) ∨ True.
Proof.
  iIntros "(Hmmio & Htrace)".
  assert_fails (iLeft; zesu_match_payload_witness).
  iRight. done.
Qed.

Lemma payload_call_witness_requires_complete_trace `{!islaG Sigma} `{!threadG}
    (address : Z) (bytes : list (bv 8)) (tail : spec) :
  address ↦ₘ∗ bytes ∗ mmio_range 0 16 ∗
  spec_trace (scons (SWriteMem (BV 64 0) (bv_to_bvn (BV 64 1))) tail) -∗
  (∃ witnesses : spec *ₗ list (bv 8) *ₗ unit,
    address ↦ₘ∗ witnesses.2ₗ ∗ mmio_range 0 16 ∗
    spec_trace witnesses.1ₗ ∗ True) ∨ True.
Proof.
  iIntros "(Hbytes & Hmmio & Htrace)".
  assert_fails (iLeft; zesu_match_payload_witness).
  iRight. done.
Qed.

Lemma payload_call_witness_spec_owned `{!islaG Sigma} `{!threadG}
    (tail : spec) :
  mmio_range 0 16 ∗ spec_trace tail -∗
  ∃ witnesses : spec *ₗ unit, mmio_range 0 16 ∗ spec_trace witnesses.1ₗ ∗ True.
Proof.
  iIntros "(Hmmio & Htrace)". zesu_match_payload_witness. iFrame.
Qed.

Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
#[local] Hint Rewrite app_nil_r : zesu_payloads.

Lemma payload_call_witness_equal_payload `{!islaG Sigma} `{!threadG}
    (address size : bv 64) (bytes : list (bv 8)) (tail : spec) :
  mmio_range 0 16 ∗ spec_trace (writeOutputEvents address size (bytes ++ []) tail) -∗
  ∃ witnesses : spec *ₗ unit, mmio_range 0 16 ∗
    spec_trace (writeOutputEvents address size bytes witnesses.1ₗ) ∗ True.
Proof.
  iIntros "(Hmmio & Htrace)". zesu_match_payload_witness. iFrame.
Qed.
Print Assumptions payload_call_witness_equal_payload.

Lemma payload_call_witness_address_trace `{!islaG Sigma} `{!threadG}
    (address size : bv 64) (bytes : list (bv 8)) (tail : spec) :
  bv_unsigned address ↦ₘ∗ bytes ∗
  spec_trace (writeOutputEventsAny address size tail) -∗
  ∃ witnesses : spec *ₗ list (bv 8) *ₗ unit,
    bv_unsigned address ↦ₘ∗ witnesses.2ₗ ∗
    spec_trace (writeOutputEvents address size witnesses.2ₗ witnesses.1ₗ) ∗ True.
Proof.
  iIntros "(Hbytes & Htrace)". zesu_match_payload_witness. iFrame.
Qed.
Print Assumptions payload_call_witness_address_trace.

Lemma payload_call_witness_rejects_other_exact_payload `{!islaG Sigma} `{!threadG}
    (address size : bv 64) (bytes : list (bv 8)) (tail : spec) :
  bv_unsigned address ↦ₘ∗ bytes ∗
  spec_trace (writeOutputEvents address size [] tail) -∗
  (∃ witnesses : spec *ₗ list (bv 8) *ₗ unit,
    bv_unsigned address ↦ₘ∗ witnesses.2ₗ ∗
    spec_trace (writeOutputEvents address size witnesses.2ₗ witnesses.1ₗ) ∗ True) ∨ True.
Proof.
  iIntros "(Hbytes & Htrace)".
  assert_fails (iLeft; zesu_match_payload_witness).
  iRight. done.
Qed.

Lemma payload_call_witness_list_first `{!islaG Sigma} `{!threadG}
    (address size : bv 64) (bytes : list (bv 8)) (tail : spec) :
  bv_unsigned address ↦ₘ∗ bytes ∗
  spec_trace (writeOutputEventsAny address size tail) -∗
  ∃ witnesses : list (bv 8) *ₗ spec *ₗ unit,
    bv_unsigned address ↦ₘ∗ witnesses.1ₗ ∗
    spec_trace (writeOutputEvents address size witnesses.1ₗ witnesses.2ₗ) ∗ True.
Proof.
  iIntros "(Hbytes & Htrace)". zesu_match_payload_witness. iFrame.
Qed.
Print Assumptions payload_call_witness_list_first.

Lemma payload_call_tail_inference `{!islaG Sigma} `{!threadG}
    (address size : bv 64) (bytes : list (bv 8)) (tail : spec) :
  bv_unsigned address ↦ₘ∗ bytes ∗
  spec_trace (writeOutputEventsAny address size (scons (SWriteMem 0%bv (bv_to_bvn (1%bv : bv 64))) tail)) -∗
  ∃ witnesses : spec *ₗ list (bv 8) *ₗ unit,
    bv_unsigned address ↦ₘ∗ witnesses.2ₗ ∗
    spec_trace (writeOutputEvents address size witnesses.2ₗ witnesses.1ₗ) ∗ True.
Proof.
  iIntros "(Hbytes & Htrace)". zesu_infer_owned_payload_tail. iFrame.
Qed.
Print Assumptions payload_call_tail_inference.

Lemma payload_call_tail_rejects_incompatible_trace `{!islaG Sigma} `{!threadG}
    (address : Z) (bytes : list (bv 8)) (tail : spec) :
  address ↦ₘ∗ bytes ∗ spec_trace (scons (SWriteMem 0%bv (bv_to_bvn (1%bv : bv 64))) tail) -∗
  (∃ witnesses : spec *ₗ list (bv 8) *ₗ unit,
    address ↦ₘ∗ witnesses.2ₗ ∗
    spec_trace (scons (SWriteMem 0%bv (bv_to_bvn (2%bv : bv 64))) witnesses.1ₗ) ∗ True) ∨ True.
Proof.
  iIntros "(Hbytes & Htrace)".
  assert_fails (iLeft; zesu_infer_owned_payload_tail).
  iRight. done.
Qed.

Lemma payload_call_owned_word_pair `{!islaG Sigma} `{!threadG}
    (address : Z) (low high : bv 64) (tail : spec) :
  address ↦ₘ low ∗ (address + 8) ↦ₘ high ∗ spec_trace tail -∗
  ∃ witnesses : spec *ₗ list (bv 8) *ₗ unit,
    address ↦ₘ∗ witnesses.2ₗ ∗ spec_trace witnesses.1ₗ ∗ True.
Proof.
  iIntros "(Hlow & Hhigh & Htrace)".
  zesu_expose_owned_pair_at_call. zesu_infer_owned_payload_tail. iFrame.
Qed.
Print Assumptions payload_call_owned_word_pair.

Lemma payload_call_word_pair_requires_second_word `{!islaG Sigma} `{!threadG}
    (address : Z) (low : bv 64) (tail : spec) :
  address ↦ₘ low ∗ spec_trace tail -∗
  (∃ witnesses : spec *ₗ list (bv 8) *ₗ unit,
    address ↦ₘ∗ witnesses.2ₗ ∗ spec_trace witnesses.1ₗ ∗ True) ∨ True.
Proof.
  iIntros "(Hlow & Htrace)".
  assert_fails (iLeft; zesu_expose_owned_pair_at_call).
  iRight. done.
Qed.

Lemma payload_call_owned_saved_list `{!islaG Sigma} `{!threadG}
    (saved : list (bv 64)) :
  ⌜length saved = 1%nat⌝ ∗
  reg_col (match saved with
    | [] => [] | value :: _ => [(KindReg "x8", ExactShape (RVal_Bits value))] end) -∗
  ∃ value : bv 64, reg_col [(KindReg "x8", ExactShape (RVal_Bits value))].
Proof.
  iIntros "(%Hlength & Hregisters)".
  zesu_expose_owned_saved_list.
  iExists savedValue. iFrame.
Qed.
Print Assumptions payload_call_owned_saved_list.

Lemma payload_call_saved_list_requires_registers `{!islaG Sigma} `{!threadG}
    (saved : list (bv 64)) :
  ⌜length saved = 1%nat⌝ -∗ (True : iProp Sigma).
Proof.
  iIntros "%Hlength".
  assert_fails (idtac; zesu_expose_owned_saved_list).
  done.
Qed.

Lemma payload_call_exact_register_witness `{!islaG Sigma} `{!threadG}
    (value : bv 64) :
  reg_col [(KindReg "x8", ExactShape (RVal_Bits value))] -∗
  ∃ witness : valu *ₗ unit, "x8" ↦ᵣ witness.1ₗ ∗ True.
Proof.
  iIntros "Howned". zesu_match_register_witness. zesu_block.
Qed.
Print Assumptions payload_call_exact_register_witness.

Lemma payload_call_register_witness_requires_ownership `{!islaG Sigma} `{!threadG} :
  (True : iProp Sigma) -∗
  (∃ witness : valu *ₗ unit, "x8" ↦ᵣ witness.1ₗ ∗ True) ∨ True.
Proof.
  iIntros "_".
  assert_fails (iLeft; zesu_match_register_witness).
  iRight. done.
Qed.

Lemma payload_call_register_witness_rejects_wrong_value `{!islaG Sigma} `{!threadG} :
  reg_col [(KindReg "x8", ExactShape (RVal_Bits (1%bv : bv 64)))] -∗
  (∃ witness : valu *ₗ unit, "x8" ↦ᵣ witness.1ₗ ∗
    ⌜witness.1ₗ = RVal_Bits (2%bv : bv 64)⌝) ∨ True.
Proof.
  iIntros "Howned".
  assert_fails (iLeft; zesu_match_register_witness; solve [zesu_block]).
  iRight. done.
Qed.

Lemma payload_call_owned_tuple `{!islaG Sigma} `{!threadG} (word : bv 64) (tail : spec) :
  "x8" ↦ᵣ RVal_Bits word -∗ spec_trace tail -∗
  ∃ witness : bv 64 *ₗ (spec *ₗ unit),
    "x8" ↦ᵣ RVal_Bits witness.1ₗ ∗ spec_trace witness.2ₗ ∗ True.
Proof.
  iIntros "Hword Htrace". zesu_match_owned_tuple. iFrame.
Qed.

Lemma payload_call_owned_tuple_rejects_missing_register `{!islaG Sigma} `{!threadG} (tail : spec) :
  spec_trace tail -∗
  (∃ witness : bv 64 *ₗ (spec *ₗ unit),
    "x8" ↦ᵣ RVal_Bits witness.1ₗ ∗ spec_trace witness.2ₗ ∗ True) ∨ True.
Proof.
  iIntros "Htrace". assert_fails (iLeft; zesu_match_owned_tuple).
  iRight. done.
Qed.

Lemma payload_call_owned_tuple_rejects_type_only `{!islaG Sigma} `{!threadG} (word : bv 64) :
  (True : iProp Sigma) -∗
  (∃ witness : bv 64 *ₗ unit, "x8" ↦ᵣ RVal_Bits witness.1ₗ ∗ True) ∨ True.
Proof.
  iIntros "Htrue". assert_fails (iLeft; zesu_match_owned_tuple).
  iRight. done.
Qed.

Lemma payload_call_owned_tuple_rejects_wrong_value `{!islaG Sigma} `{!threadG} :
  "x8" ↦ᵣ RVal_Bits (1%bv : bv 64) -∗
  (∃ witness : bv 64 *ₗ unit, "x8" ↦ᵣ RVal_Bits witness.1ₗ ∗
    ⌜witness.1ₗ = (2%bv : bv 64)⌝ ∗ True) ∨ True.
Proof.
  iIntros "Hword".
  assert_fails (iLeft; zesu_match_owned_tuple; solve [zesu_block]).
  iRight. done.
Qed.

Lemma payload_call_array_tail `{!islaG Sigma} `{!threadG}
    (base : Z) (bytes : list (bv 8)) (start : nat)
    (Hbound : (start <= length bytes)%nat) :
  base ↦ₘ∗ bytes -∗
  ∃ witness : list (bv 8) *ₗ unit,
    ⌜witness.1ₗ = take (length witness.1ₗ) (drop start bytes)⌝ ∗ base ↦ₘ∗ bytes.
Proof.
  iIntros "Howned". zesu_choose_array_tail. iFrame.
  iPureIntro. rewrite take_ge; done.
Qed.
Print Assumptions payload_call_array_tail.

Lemma payload_call_array_tail_rejects_out_of_bounds `{!islaG Sigma} `{!threadG}
    (base : Z) :
  base ↦ₘ∗ [(0%bv : bv 8)] -∗
  (∃ witness : list (bv 8) *ₗ unit,
    ⌜witness.1ₗ = take (length witness.1ₗ) (drop 2 [(0%bv : bv 8)])⌝ ∗ True) ∨ True.
Proof.
  iIntros "Howned".
  assert_fails (iLeft; zesu_choose_array_tail).
  iRight. done.
Qed.

Lemma payload_call_array_tail_rejects_unresolved_index `{!islaG Sigma} `{!threadG}
    (base : Z) (bytes : list (bv 8)) :
  base ↦ₘ∗ bytes -∗ (True : iProp Sigma).
Proof.
  iIntros "Howned".
  unshelve (let index := open_constr:(_ : nat) in
    iAssert ((∃ witness : list (bv 8) *ₗ unit,
      ⌜witness.1ₗ = take (length witness.1ₗ) (drop index bytes)⌝ ∗ True) ∨ True)%I
      with "[]" as "Hcheck";
    [assert_fails (iLeft; zesu_choose_array_tail); iRight; done
    | iClear "Hcheck"; done]).
  all: exact 0%nat.
Qed.

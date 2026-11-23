From Coq Require Import Bool List ZArith.
Require Import SailStdpp.Values.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.SailRun ZesuSsz.Compliance.SailRunAccessList.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListBugTriggers.
Require Import ZesuSsz.Contracts.TxAccessListMeaning.
Require Import ZesuSsz.Compliance.TxAccessListCandidateTable.
Require Import ZesuSsz.Compliance.TxAccessListSailAgreementStatements.

Import ListNotations.
Open Scope Z_scope.

(* Plan B6, sanity by computation of TxAccessListSailAgreementStatements.v on
   the inputs of tools/oblig/exec/inputs/txAccessList.json and the four Sail
   probes of TxAccessListCandidateTable.v. For each input, by vm_compute:
   - the boolean domain alTopDomainb holds;
   - the top statement's two sides: alSailAgreesb (txAccessListSailAgrees,
     decided on the actual Sail run) or a proposed trigger;
   - layer W: the actual Sail run (txAccessListSail) has the counts of the
     pure Sail model alSailTop, and its span is the first item's payload;
   - layer P: alSailTop equals the candidate model alCandTop, or a reached
     call hits a trigger, and the per-call hits are the three triggers. *)

Definition alPairEqb (left right : Z * Z) : bool :=
  (fst left =? fst right) && (snd left =? snd right).

Definition alOptionPairEqb (left right : option (Z * Z)) : bool :=
  match left, right with
  | Some l, Some r => alPairEqb l r
  | None, None => true
  | _, _ => false
  end.

(* txAccessListSailAgrees, decided. *)
Definition alSailAgreesb (input : list byte) : bool :=
  match candidateDecodeItem input with
  | candidateError => true
  | candidateSuccess _ h p =>
      match candidateAccessList input, txAccessListSail input with
      | accessListAccepted entries _, Some (Success ref) =>
          alOptionPairEqb (accessListCounts (Success ref))
            (Some (Z.of_nat (List.length entries), accessListKeyCount entries)) &&
          alPairEqb (accessListEncodedSpan ref) (h, p)
      | accessListRejected _, Some (Reject RlpDecode) => true
      | _, _ => false
      end
  end.

(* The actual Sail run against the pure Sail model (layer W). *)
Definition alRunMatchesModelb (input : list byte) : bool :=
  match candidateDecodeItem input with
  | candidateError => true
  | candidateSuccess _ h p =>
      match txAccessListSail input, alSailTop input with
      | Some (Success ref), Some counts =>
          alOptionPairEqb (accessListCounts (Success ref)) (Some counts) &&
          alPairEqb (accessListEncodedSpan ref) (h, p)
      | Some (Reject RlpDecode), None => true
      | _, _ => false
      end
  end.

Definition alSanityb (input : list byte) : bool :=
  alTopDomainb input &&
  (alSailAgreesb input || existsb (fun triggered => triggered) (accessListProposedTriggers input)) &&
  alRunMatchesModelb input &&
  (alOptionPairEqb (alSailTop input) (alCandTop input) ||
   existsb alHitb (accessListCalls input)) &&
  Bool.eqb (existsb alHitb (accessListCalls input))
    (existsb (fun triggered => triggered) (accessListProposedTriggers input)).

Definition alSanityInputs : list (list byte) :=
  [accessListInput_empty; accessListInput_one_entry_0_keys; accessListInput_one_entry_1_key;
   accessListInput_one_entry_3_keys; accessListInput_two_entries_0_0_keys;
   accessListInput_two_entries_0_1_keys; accessListInput_two_entries_1_3_keys;
   accessListInput_two_entries_3_3_keys; accessListInput_three_entries_0_keys;
   accessListInput_three_entries_1_keys; accessListInput_not_a_list;
   accessListInput_address_19_bytes; accessListInput_key_31_bytes;
   accessListInput_truncated_entry; accessListInput_trailing_byte;
   accessListInput_entry_trailing_item_ignored; accessListInput_probe_address_21_bytes;
   accessListInput_probe_key_noncanonical_long; accessListInput_probe_key_empty;
   accessListInput_probe_address_noncanonical_long].

Example alSanityAll : forallb alSanityb alSanityInputs = true.
Proof. vm_compute. reflexivity. Qed.

(* The top statement's left side, per input, in the order above: Sail
   disagrees exactly on the five inputs that hit D1 (address_19_bytes,
   probe_address_21_bytes), D2 (key_31_bytes, probe_key_empty) or D3
   (entry_trailing_item_ignored). *)
Example alSailAgreesTable :
  map alSailAgreesb alSanityInputs =
    [true; true; true; true; true; true; true; true; true; true; true;
     false; false; true; true; false; false; true; false; true].
Proof. vm_compute. reflexivity. Qed.

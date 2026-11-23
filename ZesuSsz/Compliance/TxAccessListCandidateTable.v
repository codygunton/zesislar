From Coq Require Import List String ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Values SailStdpp.MachineWord.
Require Import EvmSailRlp.evm_rlp_types.
Require EvmSailTransactions.evm_decode_access_list_tx_types.
Require Import ZesuSsz.Compliance.SailRun ZesuSsz.Compliance.SailRunAccessList.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListMeaning.
Require Import ZesuSsz.Contracts.TxAccessListBugTriggers.

Import ListNotations.
Open Scope Z_scope.

(* Review table of packet b1-tx, checked by vm_compute. Inputs: the `hex`
   of tools/oblig/exec/inputs/txAccessList.json (branch aa/tools), each the
   encoded access list followed by one byte 07 of the next field, plus four
   probes for the Sail comparison (run with the same tool from
   _build/agents/aa/txAccessList/b1-exec/probes.json). Expected machine outcomes: the Unicorn
   runs of tools/oblig/exec/run.py (default remap, --remap never and
   --alloc-fail 1..3 without allocation failure agree): error code 3 or
   success with the listed entries, and the `rest` advance. The machine runs
   are test evidence only; no statement cites them.

   accessListTableRow: (accepted?, rest advance or -1 when `rest` is
   unchanged, entries as (address bytes, key bytes)).
   accessListSailRow: (1 success | 2 reject RlpDecode | 3 other,
   Sail (address count, slot count), Sail encoded span (offset, length)). *)

Definition accessListBytes (values : list Z) : list byte :=
  map (fun value => mword_of_int (len:=8) value) values.

Definition accessListEntryRow (entry : AccessListEntryValue)
    : list Z * list (list Z) :=
  (map bv_unsigned (entryAddress entry),
   map (map bv_unsigned) (entryKeys entry)).

Definition accessListTableRow (candidate : AccessListCandidate)
    : bool * Z * list (list Z * list (list Z)) :=
  match candidate with
  | accessListRejected consumed =>
      (false, match consumed with Some n => n | None => -1 end, [])
  | accessListAccepted entries consumed =>
      (true, consumed, map accessListEntryRow entries)
  end.

Definition accessListSailRow
    (outcome : option (SailOutcome
       EvmSailTransactions.evm_decode_access_list_tx_types.AccessListRef))
    : Z * option (Z * Z) * (Z * Z) :=
  match outcome with
  | Some (Success ref) =>
      (1, accessListCounts (Success ref), accessListEncodedSpan ref)
  | Some (Reject _) => (2, None, (0, 0))
  | Some (UnsupportedOrInternalFailure _) => (3, None, (0, 0))
  | None => (0, None, (0, 0))
  end.


Definition accessListInput_empty : list byte :=
  accessListBytes [192; 7].

Example accessListMachine_empty :
  accessListTableRow (candidateAccessList accessListInput_empty) =
    (true, 1, []).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_empty :
  accessListSailRow (txAccessListSail accessListInput_empty) = (1, Some (0, 0), (1, 0)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_empty :
  accessListHeadersFitb accessListInput_empty = true /\
  accessListProposedTriggers accessListInput_empty = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_one_entry_0_keys : list byte :=
  accessListBytes [215; 214; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 192; 7].

Example accessListMachine_one_entry_0_keys :
  accessListTableRow (candidateAccessList accessListInput_one_entry_0_keys) =
    (true, 24, [([16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16], [])]).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_one_entry_0_keys :
  accessListSailRow (txAccessListSail accessListInput_one_entry_0_keys) = (1, Some (1, 0), (1, 23)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_one_entry_0_keys :
  accessListHeadersFitb accessListInput_one_entry_0_keys = true /\
  accessListProposedTriggers accessListInput_one_entry_0_keys = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_one_entry_1_key : list byte :=
  accessListBytes [248; 56; 247; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 225; 160; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 7].

Example accessListMachine_one_entry_1_key :
  accessListTableRow (candidateAccessList accessListInput_one_entry_1_key) =
    (true, 58, [([16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16], [[64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64]])]).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_one_entry_1_key :
  accessListSailRow (txAccessListSail accessListInput_one_entry_1_key) = (1, Some (1, 1), (2, 56)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_one_entry_1_key :
  accessListHeadersFitb accessListInput_one_entry_1_key = true /\
  accessListProposedTriggers accessListInput_one_entry_1_key = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_one_entry_3_keys : list byte :=
  accessListBytes [248; 124; 248; 122; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 248; 99; 160; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 160; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 160; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 7].

Example accessListMachine_one_entry_3_keys :
  accessListTableRow (candidateAccessList accessListInput_one_entry_3_keys) =
    (true, 126, [([16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16], [[64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64]; [65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65]; [66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66]])]).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_one_entry_3_keys :
  accessListSailRow (txAccessListSail accessListInput_one_entry_3_keys) = (1, Some (1, 3), (2, 124)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_one_entry_3_keys :
  accessListHeadersFitb accessListInput_one_entry_3_keys = true /\
  accessListProposedTriggers accessListInput_one_entry_3_keys = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_two_entries_0_0_keys : list byte :=
  accessListBytes [238; 214; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 192; 214; 148; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 192; 7].

Example accessListMachine_two_entries_0_0_keys :
  accessListTableRow (candidateAccessList accessListInput_two_entries_0_0_keys) =
    (true, 47, [([16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16], []); ([17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17], [])]).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_two_entries_0_0_keys :
  accessListSailRow (txAccessListSail accessListInput_two_entries_0_0_keys) = (1, Some (2, 0), (1, 46)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_two_entries_0_0_keys :
  accessListHeadersFitb accessListInput_two_entries_0_0_keys = true /\
  accessListProposedTriggers accessListInput_two_entries_0_0_keys = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_two_entries_0_1_keys : list byte :=
  accessListBytes [248; 79; 214; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 192; 247; 148; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 225; 160; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 7].

Example accessListMachine_two_entries_0_1_keys :
  accessListTableRow (candidateAccessList accessListInput_two_entries_0_1_keys) =
    (true, 81, [([16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16], []); ([17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17], [[74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74]])]).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_two_entries_0_1_keys :
  accessListSailRow (txAccessListSail accessListInput_two_entries_0_1_keys) = (1, Some (2, 1), (2, 79)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_two_entries_0_1_keys :
  accessListHeadersFitb accessListInput_two_entries_0_1_keys = true /\
  accessListProposedTriggers accessListInput_two_entries_0_1_keys = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_two_entries_1_3_keys : list byte :=
  accessListBytes [248; 180; 247; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 225; 160; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 248; 122; 148; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 248; 99; 160; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 160; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 160; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 7].

Example accessListMachine_two_entries_1_3_keys :
  accessListTableRow (candidateAccessList accessListInput_two_entries_1_3_keys) =
    (true, 182, [([16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16], [[64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64]]); ([17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17], [[74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74]; [75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75]; [76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76]])]).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_two_entries_1_3_keys :
  accessListSailRow (txAccessListSail accessListInput_two_entries_1_3_keys) = (1, Some (2, 4), (2, 180)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_two_entries_1_3_keys :
  accessListHeadersFitb accessListInput_two_entries_1_3_keys = true /\
  accessListProposedTriggers accessListInput_two_entries_1_3_keys = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_two_entries_3_3_keys : list byte :=
  accessListBytes [248; 248; 248; 122; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 248; 99; 160; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 160; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 160; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 248; 122; 148; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 248; 99; 160; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 160; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 160; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 7].

Example accessListMachine_two_entries_3_3_keys :
  accessListTableRow (candidateAccessList accessListInput_two_entries_3_3_keys) =
    (true, 250, [([16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16], [[64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64]; [65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65; 65]; [66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66; 66]]); ([17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17], [[74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74]; [75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75; 75]; [76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76; 76]])]).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_two_entries_3_3_keys :
  accessListSailRow (txAccessListSail accessListInput_two_entries_3_3_keys) = (1, Some (2, 6), (2, 248)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_two_entries_3_3_keys :
  accessListHeadersFitb accessListInput_two_entries_3_3_keys = true /\
  accessListProposedTriggers accessListInput_two_entries_3_3_keys = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_three_entries_0_keys : list byte :=
  accessListBytes [248; 69; 214; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 192; 214; 148; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 192; 214; 148; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 192; 7].

Example accessListMachine_three_entries_0_keys :
  accessListTableRow (candidateAccessList accessListInput_three_entries_0_keys) =
    (true, 71, [([16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16], []); ([17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17], []); ([18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18], [])]).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_three_entries_0_keys :
  accessListSailRow (txAccessListSail accessListInput_three_entries_0_keys) = (1, Some (3, 0), (2, 69)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_three_entries_0_keys :
  accessListHeadersFitb accessListInput_three_entries_0_keys = true /\
  accessListProposedTriggers accessListInput_three_entries_0_keys = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_three_entries_1_keys : list byte :=
  accessListBytes [248; 168; 247; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 225; 160; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 247; 148; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 225; 160; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 247; 148; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 225; 160; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 7].

Example accessListMachine_three_entries_1_keys :
  accessListTableRow (candidateAccessList accessListInput_three_entries_1_keys) =
    (true, 170, [([16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16], [[64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64]]); ([17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17; 17], [[74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74; 74]]); ([18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18; 18], [[84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84; 84]])]).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_three_entries_1_keys :
  accessListSailRow (txAccessListSail accessListInput_three_entries_1_keys) = (1, Some (3, 3), (2, 168)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_three_entries_1_keys :
  accessListHeadersFitb accessListInput_three_entries_1_keys = true /\
  accessListProposedTriggers accessListInput_three_entries_1_keys = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_not_a_list : list byte :=
  accessListBytes [148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 7].

Example accessListMachine_not_a_list :
  accessListTableRow (candidateAccessList accessListInput_not_a_list) =
    (false, -1, []).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_not_a_list :
  accessListSailRow (txAccessListSail accessListInput_not_a_list) = (2, None, (0, 0)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_not_a_list :
  accessListHeadersFitb accessListInput_not_a_list = true /\
  accessListProposedTriggers accessListInput_not_a_list = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_address_19_bytes : list byte :=
  accessListBytes [247; 246; 147; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 225; 160; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 7].

Example accessListMachine_address_19_bytes :
  accessListTableRow (candidateAccessList accessListInput_address_19_bytes) =
    (false, 56, []).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_address_19_bytes :
  accessListSailRow (txAccessListSail accessListInput_address_19_bytes) = (1, Some (1, 1), (1, 55)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_address_19_bytes :
  accessListHeadersFitb accessListInput_address_19_bytes = true /\
  accessListProposedTriggers accessListInput_address_19_bytes = [true; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_key_31_bytes : list byte :=
  accessListBytes [247; 246; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 224; 159; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 7].

Example accessListMachine_key_31_bytes :
  accessListTableRow (candidateAccessList accessListInput_key_31_bytes) =
    (false, 56, []).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_key_31_bytes :
  accessListSailRow (txAccessListSail accessListInput_key_31_bytes) = (1, Some (1, 1), (1, 55)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_key_31_bytes :
  accessListHeadersFitb accessListInput_key_31_bytes = true /\
  accessListProposedTriggers accessListInput_key_31_bytes = [false; true; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_truncated_entry : list byte :=
  accessListBytes [248; 58; 248; 96; 247; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 225; 160; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 7].

Example accessListMachine_truncated_entry :
  accessListTableRow (candidateAccessList accessListInput_truncated_entry) =
    (false, 60, []).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_truncated_entry :
  accessListSailRow (txAccessListSail accessListInput_truncated_entry) = (2, None, (0, 0)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_truncated_entry :
  accessListHeadersFitb accessListInput_truncated_entry = true /\
  accessListProposedTriggers accessListInput_truncated_entry = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_trailing_byte : list byte :=
  accessListBytes [248; 57; 247; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 225; 160; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 1; 7].

Example accessListMachine_trailing_byte :
  accessListTableRow (candidateAccessList accessListInput_trailing_byte) =
    (false, 59, []).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_trailing_byte :
  accessListSailRow (txAccessListSail accessListInput_trailing_byte) = (2, None, (0, 0)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_trailing_byte :
  accessListHeadersFitb accessListInput_trailing_byte = true /\
  accessListProposedTriggers accessListInput_trailing_byte = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_entry_trailing_item_ignored : list byte :=
  accessListBytes [248; 61; 248; 59; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 225; 160; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 131; 1; 1; 1; 7].

Example accessListMachine_entry_trailing_item_ignored :
  accessListTableRow (candidateAccessList accessListInput_entry_trailing_item_ignored) =
    (true, 63, [([16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16], [[64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64]])]).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_entry_trailing_item_ignored :
  accessListSailRow (txAccessListSail accessListInput_entry_trailing_item_ignored) = (2, None, (0, 0)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_entry_trailing_item_ignored :
  accessListHeadersFitb accessListInput_entry_trailing_item_ignored = true /\
  accessListProposedTriggers accessListInput_entry_trailing_item_ignored = [false; false; true].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_probe_address_21_bytes : list byte :=
  accessListBytes [248; 58; 248; 56; 149; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 225; 160; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 7].

Example accessListMachine_probe_address_21_bytes :
  accessListTableRow (candidateAccessList accessListInput_probe_address_21_bytes) =
    (false, 60, []).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_probe_address_21_bytes :
  accessListSailRow (txAccessListSail accessListInput_probe_address_21_bytes) = (1, Some (1, 1), (2, 58)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_probe_address_21_bytes :
  accessListHeadersFitb accessListInput_probe_address_21_bytes = true /\
  accessListProposedTriggers accessListInput_probe_address_21_bytes = [true; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_probe_key_noncanonical_long : list byte :=
  accessListBytes [248; 58; 248; 56; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 226; 184; 32; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 7].

Example accessListMachine_probe_key_noncanonical_long :
  accessListTableRow (candidateAccessList accessListInput_probe_key_noncanonical_long) =
    (true, 60, [([16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16], [[64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64; 64]])]).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_probe_key_noncanonical_long :
  accessListSailRow (txAccessListSail accessListInput_probe_key_noncanonical_long) = (1, Some (1, 1), (2, 58)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_probe_key_noncanonical_long :
  accessListHeadersFitb accessListInput_probe_key_noncanonical_long = true /\
  accessListProposedTriggers accessListInput_probe_key_noncanonical_long = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_probe_key_empty : list byte :=
  accessListBytes [216; 215; 148; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 193; 128; 7].

Example accessListMachine_probe_key_empty :
  accessListTableRow (candidateAccessList accessListInput_probe_key_empty) =
    (false, 25, []).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_probe_key_empty :
  accessListSailRow (txAccessListSail accessListInput_probe_key_empty) = (1, Some (1, 1), (1, 24)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_probe_key_empty :
  accessListHeadersFitb accessListInput_probe_key_empty = true /\
  accessListProposedTriggers accessListInput_probe_key_empty = [false; true; false].
Proof. vm_compute. split; reflexivity. Qed.

Definition accessListInput_probe_address_noncanonical_long : list byte :=
  accessListBytes [216; 215; 184; 20; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 192; 7].

Example accessListMachine_probe_address_noncanonical_long :
  accessListTableRow (candidateAccessList accessListInput_probe_address_noncanonical_long) =
    (true, 25, [([16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16; 16], [])]).
Proof. vm_compute. reflexivity. Qed.

Example accessListSail_probe_address_noncanonical_long :
  accessListSailRow (txAccessListSail accessListInput_probe_address_noncanonical_long) = (1, Some (1, 0), (1, 24)).
Proof. vm_compute. reflexivity. Qed.

Example accessListTriggers_probe_address_noncanonical_long :
  accessListHeadersFitb accessListInput_probe_address_noncanonical_long = true /\
  accessListProposedTriggers accessListInput_probe_address_noncanonical_long = [false; false; false].
Proof. vm_compute. split; reflexivity. Qed.

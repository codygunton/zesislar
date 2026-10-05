From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Import ListNotations.
Open Scope Z_scope.

Definition decodeItemVectorBytes (values : list Z) : list byte :=
  map (Z_to_bv 8) values.

(* Tags: 0 Success, 1 Reject(RlpDecode), 2 unsupported, 3 other Reject. *)
Definition decodeItemSailSummary (values : list Z) : list Z :=
  let bytes := decodeItemVectorBytes values in
  let len := Z.of_nat (length bytes) in
  match runRlpDecodeItem bytes (@Build_StatelessInputSliceFields 0 len 0 len) with
  | Success (existT fullLen (existT contentLen field)) =>
      [0; if RlpFieldRef_is_list field then 1 else 0; fullLen; contentLen;
       StatelessInputSliceFields_bytes (RlpFieldRef_source field);
       StatelessInputSliceFields_len (RlpFieldRef_source field)]
  | Reject RlpDecode => [1]
  | Reject _ => [3]
  | UnsupportedOrInternalFailure _ => [2]
  end.

(* This is a contract candidate. It is not selected-ELF execution. *)
Definition decodeItemCandidateSummary (values : list Z) : list Z :=
  match candidateDecodeItem (decodeItemVectorBytes values) with
  | candidateError => [1]
  | candidateSuccess isList headerLen payloadLen =>
      [0; if isList then 1 else 0; headerLen; payloadLen]
  end.

(* These fixtures check the approved readable ranges and byte-addressed output. *)
Example decodeItemLayout_input_region :
  decodeItemEntryLayout 0x40001000 1 0xa0002000 0xa0001000 0x4000 0x100000000.
Proof. vm_compute. intuition discriminate. Qed.
Example decodeItemLayout_ram_input :
  decodeItemEntryLayout 0xa0003000 1 0xa0002000 0xa0001000 0x4000 0x100000000.
Proof. vm_compute. intuition discriminate. Qed.
Example decodeItemLayout_byte_output :
  decodeItemEntryLayout 0x40001000 1 0xa0002001 0xa0001000 0x4000 0x100000000.
Proof. vm_compute. intuition discriminate. Qed.
Example decodeItemLayout_output_below_ram :
  ~ decodeItemEntryLayout 0x40001000 1 0x9fffffff 0xa0001000 0x4000 0x100000000.
Proof. vm_compute. intuition discriminate. Qed.
Example decodeItemLayout_output_crosses_end :
  ~ decodeItemEntryLayout 0x40001000 1 0xbfffffd9 0xa0001000 0x4000 0x100000000.
Proof. vm_compute. intuition discriminate. Qed.
Example decodeItemLayout_unreadable_input :
  ~ decodeItemEntryLayout 0x80001000 1 0xa0002000 0xa0001000 0x4000 0x100000000.
Proof. vm_compute. intuition discriminate. Qed.
Example decodeItemLayout_input_crosses_end :
  ~ decodeItemEntryLayout 0x7fffffff 2 0xa0002000 0xa0001000 0x4000 0x100000000.
Proof. vm_compute. intuition discriminate. Qed.
Example decodeItemLayout_ram_input_crosses_end :
  ~ decodeItemEntryLayout 0xbfffffff 2 0xa0002000 0xa0001000 0x4000 0x100000000.
Proof. vm_compute. intuition discriminate. Qed.
Example decodeItemLayout_input_end :
  decodeItemEntryLayout 0x7fffffff 1 0xa0002000 0xa0001000 0x4000 0x100000000.
Proof. vm_compute. intuition discriminate. Qed.
Example decodeItemLayout_output_end :
  decodeItemEntryLayout 0x40001000 1 0xbfffffd8 0xa0001000 0x4000 0x100000000.
Proof. vm_compute. intuition discriminate. Qed.

Example decodeItemLayout_input_end_short :
  ~ decodeItemEntryLayout 0x40001000 1 0xa0002000 0xa0001000 0x4000 0x40001000.
Proof. vm_compute. intuition discriminate. Qed.
Example decodeItemLayout_input_end_negative :
  ~ decodeItemEntryLayout 0x40001000 1 0xa0002000 0xa0001000 0x4000 (-1).
Proof. vm_compute. intuition discriminate. Qed.
Example decodeItemLayout_input_end_wrap :
  ~ decodeItemEntryLayout 0x40001000 1 0xa0002000 0xa0001000 0x4000 word64Modulus.
Proof. vm_compute. intuition discriminate. Qed.
Example decodeItemLayout_input_end_exact :
  decodeItemEntryLayout 0x40001000 1 0xa0002000 0xa0001000 0x4000 0x40001001.
Proof. vm_compute. intuition discriminate. Qed.

Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Export.Snapshots.

Import ListNotations.
Open Scope Z_scope.

Fixpoint zesuOutputPayloadsOfTrace
    (labels : list seq_label) : option (list ByteString) :=
  match labels with
  | [] => Some []
  | label :: rest =>
      match label, rest with
      | SWriteMem address data _,
          SWriteMem sizeAddress size snapshot :: remaining =>
          if decide (address = BV 64 (machineOutputAddress defaultMap) /\
                     sizeAddress = BV 64 (machineOutputSizeAddress defaultMap)) then
            match read_mem_list snapshot.(snap_mem) (bvn_unsigned data)
                    (Z.to_N (bvn_unsigned size)),
                  zesuOutputPayloadsOfTrace remaining with
            | Some bytes, Some payloads =>
                Some (List.map bv_unsigned bytes :: payloads)
            | _, _ => None
            end
          else zesuOutputPayloadsOfTrace rest
      | _, _ => zesuOutputPayloadsOfTrace rest
      end
  end.

Definition zesuOutputBytesOfTrace (labels : list seq_label) : option ByteString :=
  (@List.concat Z) <$> zesuOutputPayloadsOfTrace labels.

Lemma zesuOutputPayloadsOfTrace_write data size firstSnapshot writeSnapshot
    labels payload payloads :
  read_mem_list writeSnapshot.(snap_mem) (bvn_unsigned data)
    (Z.to_N (bvn_unsigned size)) = Some payload ->
  zesuOutputPayloadsOfTrace labels = Some payloads ->
  zesuOutputPayloadsOfTrace
    (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
     SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot ::
     labels) = Some (List.map bv_unsigned payload :: payloads).
Proof.
  intros Hread Hrest. simpl.
  rewrite Hread Hrest. reflexivity.
Qed.

Lemma zesuOutputBytesOfTrace_write data size firstSnapshot writeSnapshot
    labels payload :
  read_mem_list writeSnapshot.(snap_mem) (bvn_unsigned data)
    (Z.to_N (bvn_unsigned size)) = Some payload ->
  zesuOutputPayloadsOfTrace labels = Some [] ->
  zesuOutputBytesOfTrace
    (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
     SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot ::
     labels) = Some (List.map bv_unsigned payload).
Proof.
  intros Hread Hrest. unfold zesuOutputBytesOfTrace.
  rewrite (zesuOutputPayloadsOfTrace_write _ _ _ _ _ _ _ Hread Hrest).
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma zesuOutputBytesOfTrace_write_events data size payload tail
    firstSnapshot writeSnapshot labels :
  writeOutputEvents data size payload tail
    (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
     SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot ::
     labels) ->
  zesuOutputPayloadsOfTrace labels = Some [] ->
  zesuOutputBytesOfTrace
    (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data firstSnapshot ::
     SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size writeSnapshot ::
     labels) = Some (List.map bv_unsigned payload).
Proof.
  intros Hspec Hrest.
  apply zesuOutputBytesOfTrace_write; last exact Hrest.
  eapply write_output_events_payload. exact Hspec.
Qed.


From Coq Require Import List ZArith.
From stdpp Require Import list list_numbers tactics bitvector.definitions.
From iris.proofmode Require Import tactics environments.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ByteArrayAssembly.

Ltac zesu_byte_array_closed_counts bytes :=
  lazymatch bytes with
  | @app _ ?left ?right =>
      zesu_byte_array_closed_counts left;
      zesu_byte_array_closed_counts right
  | bv_to_little_endian ?count _ _ => is_closed_term count
  | _ => idtac
  end.

Ltac zesu_byte_array_codec_view :=
  lazymatch goal with
  | |- envs_entails ?environment
      (@mem_mapsto_array ?sigma ?heap 8 ?address ?fraction ?bytes) =>
      zesu_byte_array_closed_counts bytes;
      let expanded := eval cbv beta iota zeta delta [bv_to_little_endian Z_to_little_endian
        Z.iter Pos.iter Pos.of_succ_nat Pos.succ fmap list_fmap List.map app Z.of_N Z.of_nat] in bytes in
      change (envs_entails environment
        (@mem_mapsto_array sigma heap 8 address fraction expanded))
  end.

Ltac zesu_byte_array_assemble_codec :=
  first [ByteArrayAssembly.zesu_byte_array_assemble |
    solve [zesu_byte_array_codec_view;
      ByteArrayAssembly.zesu_byte_array_assemble]].

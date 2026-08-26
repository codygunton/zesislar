Require Import isla.isla_lang.
Require Export IslaTraces.entrypoints.a10140.
Require Export IslaTraces.entrypoints.a101c4.
Require Export IslaTraces.entrypoints.a12168.
Require Export IslaTraces.entrypoints.a14ccc.
Require Export IslaTraces.entrypoints.a14d30.
Require Export IslaTraces.entrypoints.a161c0.

Definition instr_map := [
  (0x10140%Z, a10140 (* auipc t0,0x2000a *));
  (0x101c4%Z, a101c4 (* auipc t0,0x2400a *));
  (0x12168%Z, a12168 (* addi sp,sp,-2032 *));
  (0x14ccc%Z, a14ccc (* auipc a0,0x24005 *));
  (0x14d30%Z, a14d30 (* addi sp,sp,-2000 *));
  (0x161c0%Z, a161c0 (* auipc a0,0x1 *))
].

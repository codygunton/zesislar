Require Import isla.isla_lang.
Require Export IslaTraces.write_failure.a161c0.
Require Export IslaTraces.write_failure.a161c4.
Require Export IslaTraces.write_failure.a161c8.
Require Export IslaTraces.write_failure.a161cc.
Require Export IslaTraces.write_failure.a161d0.
Require Export IslaTraces.write_failure.a10190.
Require Export IslaTraces.write_failure.a10194.
Require Export IslaTraces.write_failure.a10198.
Require Export IslaTraces.write_failure.a1019c.
Require Export IslaTraces.write_failure.a101a0.

Definition instr_map := [
  (0x161c0%Z, a161c0 (* auipc a0,0x1 *));
  (0x161c4%Z, a161c4 (* addi a0,a0,1544 *));
  (0x161c8%Z, a161c8 (* li a1,6 *));
  (0x161cc%Z, a161cc (* auipc t1,0xffffa *));
  (0x161d0%Z, a161d0 (* jr -60(t1) *));
  (0x10190%Z, a10190 (* auipc t0,0x2400a *));
  (0x10194%Z, a10194 (* addi t0,t0,-216 *));
  (0x10198%Z, a10198 (* sd a0,8(t0) *));
  (0x1019c%Z, a1019c (* sd a1,16(t0) *));
  (0x101a0%Z, a101a0 (* ret *))
].

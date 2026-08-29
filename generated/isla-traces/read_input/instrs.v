Require Import isla.isla_lang.
Require Export IslaTraces.read_input.a10140.
Require Export IslaTraces.read_input.a10144.
Require Export IslaTraces.read_input.a10148.
Require Export IslaTraces.read_input.a1014c.
Require Export IslaTraces.read_input.a10150.
Require Export IslaTraces.read_input.a10154.
Require Export IslaTraces.read_input.a10158.
Require Export IslaTraces.read_input.a1015c.

Definition instr_map := [
  (0x10140%Z, a10140 (* auipc t0,0x2000a *));
  (0x10144%Z, a10144 (* addi t0,t0,-320 *));
  (0x10148%Z, a10148 (* sd t0,0(a0) *));
  (0x1014c%Z, a1014c (* auipc t0,0x2400a *));
  (0x10150%Z, a10150 (* addi t0,t0,-148 *));
  (0x10154%Z, a10154 (* ld t1,0(t0) *));
  (0x10158%Z, a10158 (* sd t1,0(a1) *));
  (0x1015c%Z, a1015c (* ret *))
].

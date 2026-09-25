Require Import isla.isla_lang.
Require Export IslaTraces.startup.a10120.
Require Export IslaTraces.startup.a10124.
Require Export IslaTraces.startup.a10128.

Definition instr_map := [
  (0x10120%Z, a10120 (* auipc gp,0x9 *));
  (0x10124%Z, a10124 (* addi gp,gp,1760 # 19800 <__global_pointer$> *));
  (0x10128%Z, a10128 (* jal 14cb0 <main> *))
].

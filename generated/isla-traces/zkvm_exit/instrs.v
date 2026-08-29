Require Import isla.isla_lang.
Require Export IslaTraces.zkvm_exit.a101c4.
Require Export IslaTraces.zkvm_exit.a101c8.
Require Export IslaTraces.zkvm_exit.a101cc.

Definition instr_map := [
  (0x101c4%Z, a101c4 (* auipc t0,0x2400a *));
  (0x101c8%Z, a101c8 (* addi t0,t0,-268 *));
  (0x101cc%Z, a101cc (* sd a0,24(t0) *))
].

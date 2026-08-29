Require Import isla.isla_lang.
Require Export IslaTraces.allocator_get.a14ccc.
Require Export IslaTraces.allocator_get.a14cd0.
Require Export IslaTraces.allocator_get.a14cd4.
Require Export IslaTraces.allocator_get.a14cd8.
Require Export IslaTraces.allocator_get.a14cdc.
Require Export IslaTraces.allocator_get.a14ce0.
Require Export IslaTraces.allocator_get.a14ce4.
Require Export IslaTraces.allocator_get.a14ce8.

Definition instr_map := [
  (0x14ccc%Z, a14ccc (* auipc a0,0x24005 *));
  (0x14cd0%Z, a14cd0 (* auipc a1,0x3 *));
  (0x14cd4%Z, a14cd4 (* ld a3,8(sp) *));
  (0x14cd8%Z, a14cd8 (* ld a2,0(sp) *));
  (0x14cdc%Z, a14cdc (* addi a0,a0,996 *));
  (0x14ce0%Z, a14ce0 (* addi a1,a1,-1320 *));
  (0x14ce4%Z, a14ce4 (* sd a0,16(sp) *));
  (0x14ce8%Z, a14ce8 (* sd a1,24(sp) *))
].

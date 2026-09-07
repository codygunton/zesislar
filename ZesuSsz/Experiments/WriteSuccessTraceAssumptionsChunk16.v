From Coq Require Import Lists.List.
Require Import isla.opsem.

Import ListNotations.

Definition writeSuccessTraceAssumptionsChunk16 : list isla_trace := [
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x2" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0xe0%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x2" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0xe8%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x2" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0xf0%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x2" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0xf8%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x5" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x10%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x5" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x8%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x2d0%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x2d8%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x2e0%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x2e8%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x2f0%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x2f8%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x300%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x308%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x310%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x318%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x320%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x328%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x330%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x338%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x340%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x8" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x348%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 3%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t: tnil;
  AssumeReg "cur_privilege" [] (RegVal_Base (Val_Enum "Machine")) Mk_annot :t: tnil;
  AssumeReg "misa" [Field "bits"] (RegVal_Base (Val_Bits (BV 64%N 0x8000000000001100%Z))) Mk_annot :t: tnil;
  AssumeReg "mtvec" [Field "bits"] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t: tnil;
  AssumeReg "rv_clint_base" [] (RegVal_Base (Val_Bits (BV 64%N 0x2000000%Z))) Mk_annot :t: tnil;
  AssumeReg "rv_clint_size" [] (RegVal_Base (Val_Bits (BV 64%N 0xc0000%Z))) Mk_annot :t: tnil;
  AssumeReg "rv_enable_misaligned_access" [] (RegVal_Base (Val_Bool false)) Mk_annot :t: tnil;
  AssumeReg "rv_enable_pmp" [] (RegVal_Base (Val_Bool false)) Mk_annot :t: tnil;
  AssumeReg "rv_htif_tohost" [] (RegVal_Base (Val_Bits (BV 64%N 0x40001000%Z))) Mk_annot :t: tnil;
  AssumeReg "rv_ram_base" [] (RegVal_Base (Val_Bits (BV 64%N 0x20000000%Z))) Mk_annot :t: tnil;
  AssumeReg "rv_ram_size" [] (RegVal_Base (Val_Bits (BV 64%N 0x20000000%Z))) Mk_annot :t: tnil;
  AssumeReg "rv_rom_base" [] (RegVal_Base (Val_Bits (BV 64%N 0x1000%Z))) Mk_annot :t: tnil;
  AssumeReg "rv_rom_size" [] (RegVal_Base (Val_Bits (BV 64%N 0x100%Z))) Mk_annot :t: tnil
].

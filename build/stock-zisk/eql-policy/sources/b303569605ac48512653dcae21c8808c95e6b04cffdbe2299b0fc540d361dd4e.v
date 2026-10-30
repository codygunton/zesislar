From isla Require Import opsem.

Definition a8009c440 : isla_trace :=
  AssumeReg "rv_enable_pmp" [] (RegVal_Base (Val_Bool false)) Mk_annot :t:
  AssumeReg "rv_enable_misaligned_access" [] (RegVal_Base (Val_Bool true)) Mk_annot :t:
  AssumeReg "cur_privilege" [] (RegVal_Base (Val_Enum "Machine")) Mk_annot :t:
  Smt (DeclareConst 4%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x20000%Z)) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 5%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Manyop And [AExp_Binop ((Bvcomp Bvsge)) (AExp_Unop (ZeroExtend 64%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x2" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 128%N 0xa0000000%Z)) Mk_annot) Mk_annot; AExp_Binop ((Bvcomp Bvsle)) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Unop (ZeroExtend 64%N) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x2" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot) Mk_annot; AExp_Val (AVal_Bits (BV 128%N 0x8%Z)) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits (BV 128%N 0xc0000000%Z)) Mk_annot) Mk_annot] Mk_annot) Mk_annot :t:
  Smt (DeclareConst 6%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 6%Z)) Mk_annot :t:
  Smt (DefineConst 7%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 6%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  ReadReg "x2" [] (RegVal_Base (Val_Symbolic 5%Z)) Mk_annot :t:
  Smt (DefineConst 8%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 5%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  ReadReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 4%Z))]) Mk_annot :t:
  Smt (DeclareConst 15%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "satp" [] (RegVal_Base (Val_Symbolic 15%Z)) Mk_annot :t:
  Smt (DeclareConst 27%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadMem (RegVal_Base (Val_Symbolic 27%Z)) (RegVal_Poison) (RegVal_Base (Val_Symbolic 8%Z)) 8%N None Mk_annot :t:
  Smt (DefineConst 28%Z (Unop (SignExtend 0%N) (Val (Val_Symbolic 27%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "x8" [] (RegVal_Base (Val_Symbolic 28%Z)) Mk_annot :t:
  WriteReg "PC" [] (RegVal_Base (Val_Symbolic 7%Z)) Mk_annot :t:
  tnil
.

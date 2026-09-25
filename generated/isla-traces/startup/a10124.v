From isla Require Import opsem.

Definition a10124 : isla_trace :=
  Smt (DeclareConst 2%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x20000%Z)) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 3%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
  Smt (DefineConst 4%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 3%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 5%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "x3" [] (RegVal_Base (Val_Symbolic 5%Z)) Mk_annot :t:
  Smt (DefineConst 6%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 5%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x6e0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "x3" [] (RegVal_Base (Val_Symbolic 6%Z)) Mk_annot :t:
  WriteReg "PC" [] (RegVal_Base (Val_Symbolic 4%Z)) Mk_annot :t:
  tnil
.

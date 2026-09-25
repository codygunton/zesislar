From isla Require Import opsem.

Definition a10128 : isla_trace :=
  AssumeReg "cur_privilege" [] (RegVal_Base (Val_Enum "Machine")) Mk_annot :t:
  AssumeReg "misa" [Field "bits"] (RegVal_Base (Val_Bits (BV 64%N 0x8000000000001100%Z))) Mk_annot :t:
  AssumeReg "mtvec" [Field "bits"] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
  Smt (DeclareConst 2%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x20000%Z)) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 3%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
  Smt (DefineConst 4%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 3%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 5%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 3%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4b88%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 6%Z (Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 5%Z) Mk_annot) (Val (Val_Bits (BV 64%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 8%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 6%Z) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  tcases [
    Smt (Assert (Val (Val_Symbolic 8%Z) Mk_annot)) Mk_annot :t:
    WriteReg "x1" [] (RegVal_Base (Val_Symbolic 4%Z)) Mk_annot :t:
    WriteReg "PC" [] (RegVal_Base (Val_Symbolic 5%Z)) Mk_annot :t:
    tnil;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 8%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DeclareConst 11%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "medeleg" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 11%Z))]) Mk_annot :t:
    Smt (DefineConst 13%Z (Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Unop (Extract 63%N 0%N) (Val (Val_Symbolic 11%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 15%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 13%Z) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
    tcases [
      Smt (Assert (Val (Val_Symbolic 15%Z) Mk_annot)) Mk_annot :t:
      Smt (DeclareConst 18%Z (Ty_BitVec 64%N)) Mk_annot :t:
      ReadReg "mcause" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 18%Z))]) Mk_annot :t:
      Smt (DefineConst 19%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 18%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "mcause" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 19%Z))]) Mk_annot :t:
      ReadReg "mcause" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 19%Z))]) Mk_annot :t:
      Smt (DefineConst 20%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 19%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x8000000000000000%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "mcause" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 20%Z))]) Mk_annot :t:
      ReadReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 2%Z))]) Mk_annot :t:
      Smt (DefineConst 22%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 2%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xffffffffffffff7f%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 63%N) (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 2%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x7%Z)) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 22%Z))]) Mk_annot :t:
      ReadReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 22%Z))]) Mk_annot :t:
      Smt (DefineConst 23%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 22%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffffffffff7%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 23%Z))]) Mk_annot :t:
      ReadReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 23%Z))]) Mk_annot :t:
      Smt (DefineConst 24%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 23%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xffffffffffffe7ff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x1800%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 24%Z))]) Mk_annot :t:
      WriteReg "mtval" [] (RegVal_Base (Val_Symbolic 5%Z)) Mk_annot :t:
      WriteReg "mepc" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
      WriteReg "cur_privilege" [] (RegVal_Base (Val_Enum "Machine")) Mk_annot :t:
      ReadReg "mcause" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 20%Z))]) Mk_annot :t:
      WriteReg "PC" [] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
      tnil;
      Smt (Assert (Unop (Not) (Val (Val_Symbolic 15%Z) Mk_annot) Mk_annot)) Mk_annot :t:
      Smt (DeclareConst 25%Z (Ty_BitVec 64%N)) Mk_annot :t:
      ReadReg "mcause" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 25%Z))]) Mk_annot :t:
      Smt (DefineConst 26%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 25%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x7fffffffffffffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "mcause" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 26%Z))]) Mk_annot :t:
      ReadReg "mcause" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 26%Z))]) Mk_annot :t:
      Smt (DefineConst 27%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 26%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x8000000000000000%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "mcause" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 27%Z))]) Mk_annot :t:
      ReadReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 2%Z))]) Mk_annot :t:
      Smt (DefineConst 29%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 2%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xffffffffffffff7f%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 63%N) (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 2%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x7%Z)) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 29%Z))]) Mk_annot :t:
      ReadReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 29%Z))]) Mk_annot :t:
      Smt (DefineConst 30%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffffffffff7%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 30%Z))]) Mk_annot :t:
      ReadReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 30%Z))]) Mk_annot :t:
      Smt (DefineConst 31%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 30%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xffffffffffffe7ff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x1800%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 31%Z))]) Mk_annot :t:
      WriteReg "mtval" [] (RegVal_Base (Val_Symbolic 5%Z)) Mk_annot :t:
      WriteReg "mepc" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
      WriteReg "cur_privilege" [] (RegVal_Base (Val_Enum "Machine")) Mk_annot :t:
      ReadReg "mcause" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 27%Z))]) Mk_annot :t:
      WriteReg "PC" [] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
      tnil
    ]
  ]
.

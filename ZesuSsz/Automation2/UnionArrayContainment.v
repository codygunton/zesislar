Require Import isla.riscv64.riscv64.
#[export] Hint Extern 8
  (FindHypEqual (FICMemMapstoSemantic _)
    (mem_mapsto_array _ _ _) (mem_mapsto_kind_prop _ _) _) =>
  (apply isla.automation.tac_mem_mapsto_array_eq; left; assumption)
  : typeclass_instances.

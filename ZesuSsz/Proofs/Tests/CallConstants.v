Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.

Lemma call_constant_memory `{!islaG Sigma} (address : Z) :
  address ↦ₘ (Z_to_bv 64 85200 + BV 64 12288 +
    BV 64 18446744073709550296)%bv -∗ address ↦ₘ BV 64 96168.
Proof. iStartProof. iIntros "Hmemory". zesu_run. Qed.
Print Assumptions call_constant_memory.

Lemma call_constant_memory_frame `{!islaG Sigma}
    (address : Z) (P : iProp Sigma) :
  address ↦ₘ (Z_to_bv 64 85200 + BV 64 12288 +
    BV 64 18446744073709550296)%bv ∗ P -∗
  address ↦ₘ BV 64 96168 ∗ P.
Proof. iStartProof. iIntros "Hmemory". zesu_run. Qed.
Print Assumptions call_constant_memory_frame.

Lemma call_ram_memory `{!islaG Sigma} (pointer value : bv 64) :
  (mapRamBase defaultMap) <= bv_unsigned pointer ->
  bv_unsigned pointer + 24 < (machineRamEnd defaultMap) ->
  bv_unsigned (pointer + BV 64 24)%bv ↦ₘ value -∗
  (bv_unsigned pointer + 24) ↦ₘ value.
Proof.
  intros Hlower Hupper. iStartProof. iIntros "Hmemory". zesu_run.
Qed.
Print Assumptions call_ram_memory.

Lemma call_heap_instance `{!islaG Sigma} : heapG Sigma.
Proof. zesu_run. Qed.
Print Assumptions call_heap_instance.

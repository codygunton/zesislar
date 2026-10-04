(* Observable output events of the machine map output device, moved
   from the writeSuccess proof tree. *)
Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.

Definition writeOutputEventsAny (data size : bv 64) (tail : spec) : spec :=
  scons (SWriteMem (BV 64 (machineOutputAddress defaultMap)) data)
    (scons (SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) size) tail).

From Coq Require Import Strings.String.
Require Import isla.isla.

(** A coarse contract names a reviewed function boundary.  It leaves the
    machine entry, exit, and frame relations for later proof work. *)
Record CoarseContract : Type := {
  contractName : string;
  contractEntry : Prop;
  contractExit : Prop;
  contractFrame : Prop;
  contractImplements : Prop
}.

Definition coarseContractSpec `{!islaG Sigma} `{!threadG}
    (contract : CoarseContract) : iProp Sigma :=
  (⌜contractEntry contract⌝ -∗
   ⌜contractFrame contract⌝ -∗
   ⌜contractImplements contract⌝ -∗
   ⌜contractExit contract⌝)%I.

Definition namedContract (name : string)
    (entry exit frame implements : Prop) : CoarseContract :=
  {| contractName := name;
     contractEntry := entry;
     contractExit := exit;
     contractFrame := frame;
     contractImplements := implements |}.

Definition readInputContract := namedContract "readInput".
Definition allocatorGetContract := namedContract "allocatorGet".
Definition sszDecodeContract := namedContract "sszDecode".
Definition writeSuccessContract := namedContract "writeSuccess".
Definition writeFailureContract := namedContract "writeFailure".
Definition zkvmExitContract := namedContract "zkvmExit".

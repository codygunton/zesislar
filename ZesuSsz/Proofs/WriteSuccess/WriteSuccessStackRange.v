Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.ZArith.

Open Scope Z_scope.

Definition writeSuccessHelperStackDepth : Z := 80.

Definition writeSuccessCalleeStackLow (sp : Z) : Z :=
  sp - 2000 - writeSuccessHelperStackDepth.

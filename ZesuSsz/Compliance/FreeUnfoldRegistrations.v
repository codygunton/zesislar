Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.AltFlFreeContract.
Require Import ZesuSsz.Contracts.AltFlFreeBlockEntries.

(* Function-specific unfolding markers. These declarations add no generic rule. *)
Global Typeclasses Opaque freeEntryResources.
Global Instance : LithiumUnfold (@freeEntryResources) := I.
Global Typeclasses Opaque freeExitRegisterResources.
Global Instance : LithiumUnfold (@freeExitRegisterResources) := I.
Global Typeclasses Opaque freeExitResources.
Global Instance : LithiumUnfold (@freeExitResources) := I.
Global Typeclasses Opaque freeCaller.
Global Instance : LithiumUnfold (@freeCaller) := I.
Global Typeclasses Opaque freeBlockCore.
Global Instance : LithiumUnfold (@freeBlockCore) := I.
Global Typeclasses Opaque freeEntryAt80041f38.
Global Instance : LithiumUnfold (@freeEntryAt80041f38) := I.
Global Typeclasses Opaque freeEntryAt80041f58.
Global Instance : LithiumUnfold (@freeEntryAt80041f58) := I.
Global Typeclasses Opaque freeEntryAt80041f60.
Global Instance : LithiumUnfold (@freeEntryAt80041f60) := I.
Global Typeclasses Opaque freeEntryAt80041f68.
Global Instance : LithiumUnfold (@freeEntryAt80041f68) := I.
Global Typeclasses Opaque freeEntryAt80041f7c.
Global Instance : LithiumUnfold (@freeEntryAt80041f7c) := I.
Global Typeclasses Opaque freeEntryAt80041f80.
Global Instance : LithiumUnfold (@freeEntryAt80041f80) := I.
Global Typeclasses Opaque freeEntryAt80041f8c.
Global Instance : LithiumUnfold (@freeEntryAt80041f8c) := I.
Global Typeclasses Opaque freeEntryAt80041f98.
Global Instance : LithiumUnfold (@freeEntryAt80041f98) := I.
Global Typeclasses Opaque freeEntryAt80041fa4.
Global Instance : LithiumUnfold (@freeEntryAt80041fa4) := I.
Global Typeclasses Opaque freeEntryAt80041fb4.
Global Instance : LithiumUnfold (@freeEntryAt80041fb4) := I.
Global Typeclasses Opaque freeEntryAt80041fb8.
Global Instance : LithiumUnfold (@freeEntryAt80041fb8) := I.
Global Typeclasses Opaque freeEntryAt80041fc0.
Global Instance : LithiumUnfold (@freeEntryAt80041fc0) := I.
Global Typeclasses Opaque freeEntryAt80041fc8.
Global Instance : LithiumUnfold (@freeEntryAt80041fc8) := I.
Global Typeclasses Opaque freeEntryAt80041fd8.
Global Instance : LithiumUnfold (@freeEntryAt80041fd8) := I.
Global Typeclasses Opaque freeEntryAt80041fdc.
Global Instance : LithiumUnfold (@freeEntryAt80041fdc) := I.
Global Typeclasses Opaque freeEntryAt80041fe8.
Global Instance : LithiumUnfold (@freeEntryAt80041fe8) := I.
Global Typeclasses Opaque freeEntryAt80041ff4.
Global Instance : LithiumUnfold (@freeEntryAt80041ff4) := I.
Global Typeclasses Opaque freeEntryAt80042010.
Global Instance : LithiumUnfold (@freeEntryAt80042010) := I.
Global Typeclasses Opaque freeEntryAt80042014.
Global Instance : LithiumUnfold (@freeEntryAt80042014) := I.
Global Typeclasses Opaque freeEntryAt80042028.
Global Instance : LithiumUnfold (@freeEntryAt80042028) := I.
Global Typeclasses Opaque freeEntryAt8004202c.
Global Instance : LithiumUnfold (@freeEntryAt8004202c) := I.
Global Typeclasses Opaque freeEntryAt80042038.
Global Instance : LithiumUnfold (@freeEntryAt80042038) := I.
Global Typeclasses Opaque freeEntryAt80042054.
Global Instance : LithiumUnfold (@freeEntryAt80042054) := I.
Global Typeclasses Opaque freeEntryAt80042058.
Global Instance : LithiumUnfold (@freeEntryAt80042058) := I.
Global Typeclasses Opaque freeEntryAt80042070.
Global Instance : LithiumUnfold (@freeEntryAt80042070) := I.
Global Typeclasses Opaque freeEntryAt80042074.
Global Instance : LithiumUnfold (@freeEntryAt80042074) := I.
Global Typeclasses Opaque freeEntryAt80042080.
Global Instance : LithiumUnfold (@freeEntryAt80042080) := I.
Global Typeclasses Opaque freeEntryAt80042090.
Global Instance : LithiumUnfold (@freeEntryAt80042090) := I.
Global Typeclasses Opaque freeEntryAt80042094.
Global Instance : LithiumUnfold (@freeEntryAt80042094) := I.
Global Typeclasses Opaque freeEntryAt800420b0.
Global Instance : LithiumUnfold (@freeEntryAt800420b0) := I.
Global Typeclasses Opaque freeEntryAt800420b4.
Global Instance : LithiumUnfold (@freeEntryAt800420b4) := I.
Global Typeclasses Opaque freeEntryAt800420cc.
Global Instance : LithiumUnfold (@freeEntryAt800420cc) := I.
Global Typeclasses Opaque freeEntryAt800420d0.
Global Instance : LithiumUnfold (@freeEntryAt800420d0) := I.
Global Typeclasses Opaque freeEntryAt800420ec.
Global Instance : LithiumUnfold (@freeEntryAt800420ec) := I.
Global Typeclasses Opaque freeEntryAt800420f0.
Global Instance : LithiumUnfold (@freeEntryAt800420f0) := I.
Global Typeclasses Opaque freeEntryAt8004210c.
Global Instance : LithiumUnfold (@freeEntryAt8004210c) := I.
Global Typeclasses Opaque freeEntryAt80042110.
Global Instance : LithiumUnfold (@freeEntryAt80042110) := I.
Global Typeclasses Opaque freeEntryAt80042130.
Global Instance : LithiumUnfold (@freeEntryAt80042130) := I.
Global Typeclasses Opaque freeEntryAt80042134.
Global Instance : LithiumUnfold (@freeEntryAt80042134) := I.
Global Typeclasses Opaque freeEntryAt8004213c.
Global Instance : LithiumUnfold (@freeEntryAt8004213c) := I.
Global Typeclasses Opaque freeEntryAt80042144.
Global Instance : LithiumUnfold (@freeEntryAt80042144) := I.
Global Typeclasses Opaque freeEntryAt80042154.
Global Instance : LithiumUnfold (@freeEntryAt80042154) := I.
Global Typeclasses Opaque freeEntryAt80042160.
Global Instance : LithiumUnfold (@freeEntryAt80042160) := I.

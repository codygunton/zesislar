The pass closes six native block boundaries. No Level 1 contract closes.

Root: `34086606bd7f9b72321bfb25ef36f976dc90f391`. Workers: 3.

Pet stack, shelf, and given_up groups remain unavailable. All active goal lists are available.

| Block | Outcome | Residual class | Active | CPU s | Compiler wall s | Peak KiB | Limit |
|---|---|---|---:|---:|---:|---:|---|
| 0x800d6960 | native-residual | entry-or-handoff,witness | 9 | 86.414 | 86.876 | 2022980 | none |
| 0x800d6974 | native-residual | memory-selection,register-selection,execution,entry-or-handoff,witness | 8 | 621.086 | 624.357 | 2375288 | none |
| 0x800d697c | native-residual | resource-selection,execution,entry-or-handoff,witness | 3 | 285.514 | 286.973 | 2295472 | none |
| 0x800d698c | native-residual | resource-selection,execution,entry-or-handoff,witness | 6 | 519.312 | 522.029 | 2346200 | none |
| 0x800d69a4 | native-residual | entry-or-handoff | 4 | 13.925 | 14.018 | 1101208 | none |
| 0x800d69b0 | native-residual | resource-selection,execution,entry-or-handoff,witness | 3 | 309.602 | 311.276 | 2291184 | none |
| 0x800d69d8 | native-boundary-closed | kernel-Qed-boundary | 0 | 28.075 | 28.290 | 1252856 | none |
| 0x800d69e0 | native-residual | entry-or-handoff | 3 | 43.943 | 44.232 | 1407944 | none |
| 0x800d69e8 | native-residual | resource-selection,execution,entry-or-handoff,witness | 3 | 376.062 | 377.875 | 2358972 | none |
| 0x800d6a00 | native-boundary-closed | kernel-Qed-boundary | 0 | 42.590 | 42.848 | 1492716 | none |
| 0x800d6a08 | native-residual | entry-or-handoff | 5 | 34.187 | 34.392 | 1359108 | none |
| 0x800d6a14 | native-boundary-closed | kernel-Qed-boundary | 0 | 7.298 | 7.344 | 1113708 | none |
| 0x800d6a24 | native-residual | entry-or-handoff | 15 | 1949.431 | 1958.647 | 3280616 | none |
| 0x800d6a38 | native-residual | entry-or-handoff | 1 | 44.546 | 44.731 | 1399888 | none |
| 0x800d6a40 | native-residual | resource-selection,execution,entry-or-handoff,witness | 3 | 404.373 | 406.315 | 2301480 | none |
| 0x800d6a64 | native-boundary-closed | kernel-Qed-boundary | 0 | 45.228 | 45.467 | 1486372 | none |
| 0x800d6a6c | native-boundary-closed | kernel-Qed-boundary | 0 | 48.101 | 48.362 | 1506840 | none |
| 0x800d6a78 | native-residual | resource-selection,execution,entry-or-handoff,witness | 3 | 546.298 | 549.643 | 2381488 | none |
| 0x800d6aa8 | native-residual | entry-or-handoff | 5 | 38.963 | 39.176 | 1346904 | none |
| 0x800d6ab4 | native-boundary-closed | kernel-Qed-boundary | 0 | 9.023 | 9.090 | 1107856 | none |
| 0x800d6ac4 | native-residual | entry-or-handoff | 15 | 1813.817 | 1821.672 | 3341928 | none |
| 0x800d6ad8 | native-residual | entry-or-handoff | 2 | 74.011 | 74.301 | 1676668 | none |
| 0x800d6ae0 | native-residual | resource-selection,execution,entry-or-handoff,witness | 3 | 180.085 | 180.844 | 2246364 | none |
| 0x800d6b08 | native-residual | resource-selection,execution,entry-or-handoff,witness | 3 | 317.778 | 318.808 | 2362728 | none |

The 69d8, 6a00, 6a14, 6a64, 6a6c, and 6ab4 certificates use actual successor entries.
Each certificate has kernel Qed, an exact compiled object, empty assumptions, and empty inherited debts.
The report preserves all exact sources, logs, objects, inputs, and setup failures in the content archive.

The 6a6c boundary adds three verified instructions versus rootfc. The other five boundaries were previously verified.
All 18 residuals retain active goals. No compiler reaches a limit. Pet stack, shelf, and given_up remain unavailable.

M1 verified 6a6c historically. This pass adds its closure versus the frozen rootfc pass.

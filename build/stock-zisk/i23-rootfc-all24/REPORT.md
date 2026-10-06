The pass closes five native block boundaries. No Level 1 contract closes.

Root: `fc54828a64c6a3912550281690aa412856ea3852`. Workers: 3.

Pet stack, shelf, and given_up groups remain unavailable. All four limit failures have unavailable final groups.

| Block | Outcome | Residual class | Active | CPU s | Compiler wall s | Peak KiB | Limit |
|---|---|---|---:|---:|---:|---:|---|
| 0x800d6960 | native-residual | entry-or-handoff,witness | 10 | 120.287 | 121.092 | 2092336 | none |
| 0x800d6974 | native-residual | memory-selection,register-selection,execution,entry-or-handoff,witness | 8 | 632.550 | 635.866 | 2375304 | none |
| 0x800d697c | native-residual | resource-selection,execution,entry-or-handoff,witness | 6 | 1171.165 | 1176.331 | 3071480 | none |
| 0x800d698c | automation-search-failure | memory-limit | unavailable | 984.809 | 989.473 | 12583192 | memory |
| 0x800d69a4 | native-residual | entry-or-handoff | 4 | 14.692 | 14.807 | 1097028 | none |
| 0x800d69b0 | native-residual | resource-selection,execution,entry-or-handoff,witness | 6 | 1193.800 | 1199.524 | 2964988 | none |
| 0x800d69d8 | native-boundary-closed | kernel-Qed-boundary | 0 | 30.988 | 31.202 | 1248652 | none |
| 0x800d69e0 | native-residual | entry-or-handoff | 3 | 47.829 | 48.121 | 1406284 | none |
| 0x800d69e8 | automation-search-failure | cpu-limit | unavailable | 1199.931 | 1205.613 | 2950776 | cpu |
| 0x800d6a00 | native-boundary-closed | kernel-Qed-boundary | 0 | 45.263 | 45.511 | 1494360 | none |
| 0x800d6a08 | native-residual | entry-or-handoff | 7 | 42.947 | 43.191 | 1398096 | none |
| 0x800d6a14 | native-boundary-closed | kernel-Qed-boundary | 0 | 8.465 | 8.537 | 1109748 | none |
| 0x800d6a24 | native-residual | entry-or-handoff | 15 | 1480.533 | 1484.807 | 3319580 | none |
| 0x800d6a38 | native-residual | entry-or-handoff | 2 | 53.217 | 53.493 | 1406180 | none |
| 0x800d6a40 | automation-search-failure | cpu-limit | unavailable | 1199.875 | 1206.388 | 2852296 | cpu |
| 0x800d6a64 | native-boundary-closed | kernel-Qed-boundary | 0 | 42.746 | 42.975 | 1485916 | none |
| 0x800d6a6c | native-residual | entry-or-handoff | 1 | 38.801 | 38.996 | 1428828 | none |
| 0x800d6a78 | automation-search-failure | cpu-limit | unavailable | 1199.835 | 1206.145 | 2899572 | cpu |
| 0x800d6aa8 | native-residual | entry-or-handoff | 7 | 35.484 | 35.672 | 1383660 | none |
| 0x800d6ab4 | native-boundary-closed | kernel-Qed-boundary | 0 | 7.737 | 7.787 | 1109812 | none |
| 0x800d6ac4 | native-residual | entry-or-handoff | 15 | 1922.599 | 1931.462 | 3218988 | none |
| 0x800d6ad8 | native-residual | entry-or-handoff | 2 | 77.042 | 77.357 | 1666424 | none |
| 0x800d6ae0 | native-residual | resource-selection,execution,entry-or-handoff,witness | 6 | 838.999 | 841.746 | 3067092 | none |
| 0x800d6b08 | native-residual | resource-selection,execution,entry-or-handoff,witness | 6 | 1038.021 | 1041.477 | 3182936 | none |

The 69d8, 6a00, 6a14, 6a64, and 6ab4 certificates use actual successor entries.
Each certificate has kernel Qed, an exact compiled object, empty assumptions, and empty inherited debts.
The report preserves all exact sources, logs, objects, inputs, and setup failures in the content archive.

The 6a14 and 6ab4 boundaries are new versus root052. The other three boundaries were previously verified.

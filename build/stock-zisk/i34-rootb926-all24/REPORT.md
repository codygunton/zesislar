The pass closes six native block boundaries. No Level 1 contract closes.

Root: `b9263d3b8cb806fc9ba2e4e7eef1dfcab0b3a97c`. Workers: 2.

Pet stack, shelf, and given_up groups remain unavailable. The CPU-limited block has unavailable final groups.

| Block | Outcome | Residual class | Active | CPU s | Compiler wall s | Peak KiB | Limit |
|---|---|---|---:|---:|---:|---:|---|
| 0x800d6960 | native-residual | entry-or-handoff,witness | 9 | 42.067 | 42.222 | 1588116 | none |
| 0x800d6974 | native-residual | memory-selection,register-selection,execution,entry-or-handoff,witness | 8 | 383.549 | 384.700 | 2355956 | none |
| 0x800d697c | native-residual | resource-selection,execution,entry-or-handoff,witness | 3 | 56.563 | 56.770 | 1641068 | none |
| 0x800d698c | automation-search-failure | cpu-limit | unavailable | 1199.900 | 1203.737 | 2207216 | cpu |
| 0x800d69a4 | native-residual | entry-or-handoff | 4 | 8.813 | 8.867 | 1103048 | none |
| 0x800d69b0 | native-residual | resource-selection,execution,entry-or-handoff,witness | 3 | 53.093 | 53.260 | 1612956 | none |
| 0x800d69d8 | native-boundary-closed | kernel-Qed-boundary | 0 | 16.093 | 16.161 | 1176796 | none |
| 0x800d69e0 | native-residual | entry-or-handoff | 3 | 25.596 | 25.700 | 1334228 | none |
| 0x800d69e8 | native-residual | resource-selection,execution,entry-or-handoff,witness | 3 | 59.971 | 60.162 | 1682596 | none |
| 0x800d6a00 | native-boundary-closed | kernel-Qed-boundary | 0 | 25.494 | 25.595 | 1404372 | none |
| 0x800d6a08 | native-residual | entry-or-handoff | 5 | 20.260 | 20.343 | 1237892 | none |
| 0x800d6a14 | native-boundary-closed | kernel-Qed-boundary | 0 | 5.799 | 5.839 | 1113680 | none |
| 0x800d6a24 | native-residual | entry-or-handoff | 15 | 1433.595 | 1438.009 | 3263844 | none |
| 0x800d6a38 | native-residual | entry-or-handoff | 1 | 30.531 | 30.649 | 1213136 | none |
| 0x800d6a40 | native-residual | resource-selection,execution,entry-or-handoff,witness | 3 | 72.378 | 72.629 | 1721488 | none |
| 0x800d6a64 | native-boundary-closed | kernel-Qed-boundary | 0 | 25.858 | 25.947 | 1412608 | none |
| 0x800d6a6c | native-boundary-closed | kernel-Qed-boundary | 0 | 26.534 | 26.663 | 1389888 | none |
| 0x800d6a78 | native-residual | resource-selection,execution,entry-or-handoff,witness | 3 | 61.888 | 62.143 | 1708064 | none |
| 0x800d6aa8 | native-residual | entry-or-handoff | 5 | 27.737 | 28.523 | 1242084 | none |
| 0x800d6ab4 | native-boundary-closed | kernel-Qed-boundary | 0 | 7.999 | 8.047 | 1109572 | none |
| 0x800d6ac4 | native-residual | entry-or-handoff | 15 | 1613.317 | 1620.343 | 3249596 | none |
| 0x800d6ad8 | native-residual | entry-or-handoff | 2 | 84.448 | 84.967 | 1469328 | none |
| 0x800d6ae0 | native-residual | resource-selection,execution,entry-or-handoff,witness | 3 | 65.740 | 66.033 | 1606736 | none |
| 0x800d6b08 | native-residual | resource-selection,execution,entry-or-handoff,witness | 3 | 98.276 | 98.834 | 1754208 | none |

The 69d8, 6a00, 6a14, 6a64, 6a6c, and 6ab4 certificates use actual successor entries.
Each certificate has kernel Qed, an exact compiled object, empty assumptions, and empty inherited debts.
The report preserves all exact sources, logs, objects, inputs, and setup failures in the content archive.

The same six boundaries verified on root340. This pass adds no newly closed boundary.
The 698c run reaches CPU1200. Root340 returned six residuals at CPU519.312s.
Rule29, other approved source changes, hints, and worker counts differ. These measurements do not isolate a sole-rule effect.

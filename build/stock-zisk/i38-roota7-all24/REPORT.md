The pass proves six native boundaries. No Level 1 contract closes.

Root: `a7b5f0606dc697fb7b8816157ac02090ee7bb1c5`. Workers: 2.

The native sources enable 22 additions and 13 historical switches through Sets.call.
The pass does not use an approved-only switch scope.
The scope fixtures pass MCP checks, compilation, and statement verification with assumptions `[]`.

| Boundary | Closed | Active | CPU s | Compiler wall s | Peak KiB | Limit |
|---|---|---:|---:|---:|---:|---|
| 0x800d6960 | False | 9 | 49.799 | 50.025 | 1547500 | none |
| 0x800d6974 | False | 8 | 542.924 | 545.352 | 2418152 | none |
| 0x800d697c | False | 5 | 1179.982 | 1184.761 | 3351980 | none |
| 0x800d698c | False | 6 | 872.899 | 876.181 | 3014520 | none |
| 0x800d69a4 | False | 3 | 9.339 | 9.395 | 1102928 | none |
| 0x800d69b0 | False | 9 | 681.059 | 683.703 | 4554276 | none |
| 0x800d69d8 | True | 0 | 16.671 | 16.750 | 1174888 | none |
| 0x800d69e0 | False | 1 | 27.562 | 27.692 | 1319992 | none |
| 0x800d69e8 | False | unavailable | 1199.765 | 1204.851 | 3620116 | cpu |
| 0x800d6a00 | True | 0 | 32.398 | 32.581 | 1402484 | none |
| 0x800d6a08 | False | 5 | 24.018 | 24.147 | 1226080 | none |
| 0x800d6a14 | True | 0 | 7.177 | 7.225 | 1119428 | none |
| 0x800d6a24 | False | 15 | 1667.428 | 1674.249 | 3284552 | none |
| 0x800d6a38 | False | 1 | 31.628 | 31.790 | 1213712 | none |
| 0x800d6a40 | False | 9 | 916.114 | 919.582 | 4576700 | none |
| 0x800d6a64 | True | 0 | 27.945 | 28.064 | 1400380 | none |
| 0x800d6a6c | True | 0 | 27.280 | 27.409 | 1389948 | none |
| 0x800d6a78 | False | unavailable | 1199.769 | 1204.830 | 4638132 | cpu |
| 0x800d6aa8 | False | 5 | 21.008 | 21.107 | 1234300 | none |
| 0x800d6ab4 | True | 0 | 6.435 | 6.468 | 1123500 | none |
| 0x800d6ac4 | False | 15 | 1698.837 | 1705.900 | 3282108 | none |
| 0x800d6ad8 | False | 1 | 63.305 | 63.563 | 1461444 | none |
| 0x800d6ae0 | False | unavailable | 1089.465 | 1093.798 | 6294536 | memory |
| 0x800d6b08 | False | 9 | 1056.242 | 1060.253 | 4691032 | none |

The closed boundaries are 69d8, 6a00, 6a14, 6a64, 6a6c, and 6ab4.
Those boundaries cover 17 instructions. The same six boundaries closed on rootb926.
Each closure has an exact checked object, assumptions `[]`, and empty inherited debts.
All 24 regenerated sources and statements match the frozen inputs.
All 897 native inputs and 6,182 adapter inputs match their seals.
Fifteen boundaries retain residual goals. Three boundaries reach resource limits.
The 69e8 and 6a78 attempts reach CPU limits. The 6ae0 attempt reaches its memory limit.
The report preserves complete captures, sources, objects, failures, and input seals in the archive.
Stack, shelf, and given_up remain unavailable.
The wrapper returned zero. That status does not establish closure.
The two pass intervals overlap. Their elapsed times must remain separate.
The roots and hint modules differ. These measurements do not isolate one rule.

The child check-fast gate passes with six workers. The watcher takes 64 seconds.
The gate source has no production changes. Both input seals remain valid after the gate.

# Corrected designed-entry discovery

The gated source is `3df3e1ea`.
The run covers all 24 blocks and all 38 successor probes.
The primary proof bodies match the before-fix bodies byte-for-byte.
The selected ELF and code bytes remain unchanged.

The primary classes are nine search timeouts, three unavailable interactive entries, and twelve abstract reaches.
No instruction or contract block closed.
The corrected x14 block at `0x800d69a4` reached both abstract successors.
The before-fix x14 ownership gap no longer occurs.

| Block | Primary class | Secondary failed step |
|---|---|---|
| 0x800d6960 | automation-search-timeout | 256,256 |
| 0x800d6974 | primary-unavailable | none |
| 0x800d697c | automation-search-timeout | 178 |
| 0x800d698c | automation-search-timeout | 190 |
| 0x800d69a4 | reached | none |
| 0x800d69b0 | automation-search-timeout | 182 |
| 0x800d69d8 | reached | none |
| 0x800d69e0 | reached | none |
| 0x800d69e8 | automation-search-timeout | 254 |
| 0x800d6a00 | reached | none |
| 0x800d6a08 | reached | none |
| 0x800d6a14 | reached | none |
| 0x800d6a24 | primary-unavailable | none |
| 0x800d6a38 | reached | none |
| 0x800d6a40 | automation-search-timeout | 180 |
| 0x800d6a64 | reached | none |
| 0x800d6a6c | reached | none |
| 0x800d6a78 | automation-search-timeout | 257 |
| 0x800d6aa8 | reached | none |
| 0x800d6ab4 | reached | none |
| 0x800d6ac4 | primary-unavailable | none |
| 0x800d6ad8 | reached | none |
| 0x800d6ae0 | automation-search-timeout | 252 |
| 0x800d6b08 | automation-search-timeout | 180 |

The primary outer timeout is 300 seconds.
The unchanged tactic returned `Coq: Timeout!` before that outer limit.
The captures do not identify which internal tactic timeout fired.
The primary failed transaction preserves its last valid state.
That state does not establish execution progress.

All ten secondary passes stopped at two focused goals.
The exact error is `Coq: Expected a single focused goal but 2 goals are focused.`
The last successful state contains a `WPasm` assertion with RAM bounds.
The secondary pass never changes a primary class.
The archive binds every step, its elapsed time, and its reported goal size.
MCP truncates goal text at 8000 characters.
The returned suffix gives the complete character count.
The archive retains the exact returned text and truncation marker.
The full hidden goal text is unavailable.

All six automatic shell LOADs passed for the three unavailable blocks.
Their compiler times range from 1.185 to 1.262 seconds.
Their maximum RSS is 950848 KiB.
LOAD supplies no Pet state, and no fresh interactive start followed LOAD.
The earlier shell LOAD report also records six successful loads.
Its representative wrapper took 1255.714 seconds; its compiler took 1.058 seconds.
Admission wait occurred, but its exact duration was not measured.

The discovery wall time is 365.143 seconds with six workers.
The maximum measured primary worker RSS is 3306.0625 MiB.
The maximum reported primary Pet RSS is 3164 MiB.
The maximum reported secondary Pet RSS is 1558 MiB.
The module memory limit remains 6 GiB.
The machine has 64 CPUs.
Aggregate CPU activity was 10.363 percent during discovery.
Available memory changed from 118177072 to 112139600 KiB.
Swap-free memory remained 18392 KiB.

The archive contains complete captures and frozen inputs under `/home/cody/zesislar-archive/sha256`.
The archive index binds every retained object by hash.
The fragment awaits binding into the parent manifest.
The application validator accepted all 24 ordered applications through the kernel.
JSON binders are local universal variables, rather than Definition parameter names.
The kernel checks arguments against the declared parameter types.
Historical setup failures remain archived and do not classify a proof.
Q13 remains held.

The kernel rejected the deliberately swapped ROOT application at `Check`, as expected.
The negative test passed; the production validator correctly returned exit 1.

Ninety focused tests passed.
The admitted check-fast gate passed with six workers.
Its watcher wall time was 156 seconds, and its Dune time was 90.222 seconds.
The first gate failed during admission because a peer held the check-iris lock.
The archive preserves that admission failure separately from proof outcomes.
No exact guard-wait duration was measured.

The maximum individual native-step RPC time was 0.196106 seconds.
The largest reported complete goal size was 27704 characters.
The report separates native steps from import and initialization RPCs.

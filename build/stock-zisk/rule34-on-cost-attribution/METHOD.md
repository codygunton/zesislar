The diagnostics preserve root `9d4ecda138584fac3744e44234ccf2a3f0df9aeb` and candidate tree `a1a861399ead593f1b4ba246b35ebcc458e76cb3`.

The counter records completed handler callbacks and phase admissions. The diagnostic observes every attempted inner rule. An END marker records successful completion. An attempted rule can fail without an END marker. Inner observations do not increment the counter. `liShow` runs outside the counter.

The full recorder prints each callback state. The light observer prints markers and selected states. Both modes print complete initial and final raw captures. The bound 128 comparison preserves the exact ordered printed records and explicit trace bodies. Generic MCP checks preserve complete goal exports and shared evars.

The profiler resets and starts after completed counter 1280. It stops after completed counter 1296. It profiles 16 completed callbacks and private bookkeeping. The controls run outside production tactics. The pinned profiler uses `Unix.times` user plus system CPU. Its call counts approximate Ltac execution. Its inclusive and local percentages use rounded output.

The event parser records the last received counter marker. The profiler controls print before the new counter marker. Thus, the profiler start marker carries counter 1279 in the event file. The stop marker carries counter 1295. The sealed helper applies the controls at actual counters 1280 and 1296.

The terminal observation uses bound 2048 without profiling. It exhausts that bound. It records no finishing-phase BEGIN or END markers. The checked helper then skips all finishing phases because their admission checks fail. It completes uncounted `liShow` and attempts its named `Qed`.

The original comparison checks every ordered printed binder type, local body, and conclusion. It permits one consistent local alpha-renaming map. It preserves qualified names and string literals. It removes whitespace and one complete outer parenthesis pair. The goal counts differ: 12 original obligations and 49 terminal raw goals. Equivalence therefore fails.

The report does not infer hidden term identity or unavailable native goal groups. It does not treat execution output as a proof premise. It makes no native closure claim. It does not attribute the original slowdown to diagnostic observers. It does not extrapolate the profiling window across the original primary.

The archive preserves the setup failures, successful MCP calls, native attempts, raw captures, recipes, and sealed sources. The frozen proof worktree retains its inherited staged production files. The evidence worktree changes only this report package.

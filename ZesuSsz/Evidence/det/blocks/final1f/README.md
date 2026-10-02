# Preliminary variant A rerun

Automation revision: `1f72e43c`. The table contains 102 rows: 69 measured rows and 33 carried rows.
The run applies modern callee contracts and local LithiumUnfold instances.
Measured return-point entries and header/root successors use BitsShape 64 for x1, x5, x10, and x11.
The copied no-call successor states still require a return-precision audit.

The six header proofs stall on the writeOutput precondition because their memory packages remain folded.
This table does not establish that those previously closed proofs remain closed with the modern contract.
The 0x15754 memory result is carried; the run does not compile that large state.

The guard log contains 31 HOLD lines in the complete job window, which includes dependency waiting.
Nine lines concern a held gate. The other 22 lines concern machine-wide compiler or reservation limits.
The raw reason counts are in guard_holds.json. This window differs from the earlier 60-second utilization sample.

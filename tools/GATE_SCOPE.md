# Frozen Automation

`ZesuSsz/Automation/` stays equal to tree `5ad85b171275969348499d69a580d740b44f60e2`.
The comparison does not depend on branch ancestry.
The hygiene check rejects committed changes, local changes, deletions, and new source files in this directory.
New automation belongs in `ZesuSsz/Automation2/`.

An emergency requires explicit user approval before the engineer changes frozen Automation.
The engineer records that approval and its reason in the review.
The engineer sets `ZESU_AUTOMATION_EMERGENCY_OVERRIDE` to that reason for each required gate.
The checker prints the reason.
The override permits only the freeze comparison.
All other hygiene checks and proof gates still apply.
The engineer must not update the frozen revision to hide an unapproved change.

# Tool suites

The gates compare the current `tools/` digest with the latest authenticated green gate.
The digest includes tracked files, untracked source files, and executable modes.
The gates run the tool suites when the digest changes.
The gates also run the suites when evidence is absent, incomplete, or invalid.
The gates authenticate the request, result, release, closed actors, and guard identity before they omit suites.
Legacy green results lack a tools digest and cannot omit suites.
The gates still run source checks and Evidence tests on every invocation.
Dune uses its shared cache for unchanged proof targets.
A cache hit does not replace a required source check.

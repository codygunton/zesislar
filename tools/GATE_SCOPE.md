# Frozen Automation

`ZesuSsz/Automation/` stays equal to revision `4e9f33bfeee005ee7e7f16186f9d933ecac18197`.
The hygiene check rejects committed changes, local changes, deletions, and new source files in this directory.
New automation belongs in `ZesuSsz/Automation2/`.

An emergency requires explicit user approval before the engineer changes frozen Automation.
The engineer records that approval and its reason in the review.
The engineer sets `ZESU_AUTOMATION_EMERGENCY_OVERRIDE` to that reason for each required gate.
The checker prints the reason.
The override permits only the freeze comparison.
All other hygiene checks and proof gates still apply.
The engineer must not update the frozen revision to hide an unapproved change.

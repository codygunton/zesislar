# Captured integer successors

Root: `f15b0e67`.

The six integer probes reach their abstract successors after removal of the legacy successor continuations from their entry states.
The generated successor states use `BitsShape` for anonymous register values.
The generated successor states keep memory open.
Each corresponding concrete block proof compiles and reports `Closed under the global context`.
The proofs cover blocks `150fc`, `15148`, `151c4`, `153c0`, `15574`, and `15620`.
These staged block proofs do not establish the complete Level 1 contract.

The generator uses explicit `supplied_successors`, `post_state`, and `seal_memory` metadata.
The successor records come from the printed post-states at the abstract diagnostic stops.
The generator retains exact values when an entry parameter or a memory resource refers to the value.

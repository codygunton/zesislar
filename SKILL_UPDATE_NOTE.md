# Islaris skill update reminder

The simplified `read_input` proof passes `make check`.

The proof confirmed these points:

- State each memory resource with the same symbolic address form that the generated trace uses.
- Repeated `liAStep` works when it stops at `WPasm tnil`.
- Close the shelved conditions after `Unshelve` with the standard side-condition tactics.
- Do not add a custom `FindMemMapsTo` tactic to normalize address expressions.

Update the skill to explain that a `FindMemMapsTo` residual can indicate an address-expression
shape mismatch. The skill currently emphasizes a missing or incorrect memory resource. Add the
upstream `Max2` pattern as the small reference example.

Also explain one additional failure mode. An unbounded `repeat liAStep` can enter the final resource
entailment after `WPasm tnil`. This search was very slow for `read_input`. Stop at `WPasm tnil`, run
`liShow`, and prove the final resource entailment with ordinary Iris tactics.

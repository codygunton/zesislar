# Proof starting point

Begin with `Contracts/Level1.v`.
Instantiate `Level1MachineModel` with the concrete Islaris state predicates.
Do not introduce a deeper contract hierarchy before a failed direct proof requires it.
Keep the `DecoderModel` binding as a visible conditional assumption.

Use the generated entry traces to test each function boundary first.
Then generate complete trace chunks for one Level 1 contract at a time.

The intended proof order is:

1. Prove each Level 1 contract implementation statement.
2. Construct `Level1ContractAssumptions` from the six results.
3. Prove `MainComplianceStatement` for the fixed bug list.
4. Derive `MainExactComplianceStatement` for selected safe inputs.

Do not use measured evidence as a premise.
Do not add a bug constructor during proof work without a separate review.

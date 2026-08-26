# Proof starting point

Begin with the six definitions in `Contracts/Coarse.v`.
Do not introduce a deeper contract hierarchy before a failed direct proof requires it.
Keep the `DecoderModel` binding as a visible conditional assumption.

Use the generated entry traces to test each function boundary first.
Then generate complete trace chunks for one coarse contract at a time.

The intended proof order is:

1. Prove each coarse contract implementation statement.
2. Combine the six statements into `CoarseContractAssumptions`.
3. Prove `ConditionalCompliance` for the fixed bug list.
4. Derive `ConditionalExactCompliance` for selected safe inputs.

Do not use measured evidence as a premise.
Do not add a bug constructor during proof work without a separate review.

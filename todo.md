# todo

- Prove that a dismissed innings is complete at both granularities, so the dispatchers provably never reach the all-out-but-incomplete state that determine_result decides by argument order alone.
- Prove a per-cell rounding bound relating each normalized non-ODI table to the unnormalized published data, so the ratio-preservation gloss becomes a theorem.
- Document the convention that elapsed balls include removed deliveries in the CLI usage text alongside T2_FACED and the track input format.
- Discharge the table monotonicity side conditions throughout the proof corpus via the dls hint database and dls_table_mono, so the tactic layer carries the proofs it was built for.

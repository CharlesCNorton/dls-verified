# todo

1. Correct the G50 share divisor to the resource scale: 1000 in `revised_target_method2` and `par_score`, 10000 in `ball_revised_target` and `ball_par_score`.
2. Restate and reprove the theorems that carry the old constant: the `/100` forms in `revised_target_method2_form`, `revised_target_method2_bounded_by_g50_R2`, `revised_target_universal_upper_bound`, `t1_interruption_target_method2`, and `t1_int_with_t2_full_uses_g50` become `/1000`, and the hypothesis of `g50_strict_inflation` becomes `g50 * (R2 - R1) >= 1000`.
3. Update `target_more_resources` to the regulation value 300.
4. Align the divisor of `revised_target_stern` to 100000 so `stern_equals_standard_below_threshold` again reduces Stern to the corrected standard formula.
5. Transcribe the ECB regulations' worked Team-1-interruption example as a `vm_compute` Example, pinning the method-2 scale to published arithmetic as `target_1992` pins method 1.
6. Compute par against resources actually used by subtracting the Team-2 history's `total_resources_lost` in `compute_par` and its ball-level analogue, with an agreement theorem recovering the current value on empty histories.
7. Relabel the Stern section comment as a synthetic illustrative stand-in for the unpublished Professional Edition adjustment.
8. Bind `DLS_Standard.the_table` to `DLStandardTable` and carry the functor demonstration on a separately named `DLS_Dummy` instance.
9. Unify `exp_decay_approx` and `icc_resource_percentage` into a single rational-decay kernel carrying both boundary lemma sets.
10. Fold `interpolate_full_odi_concave` and `interpolate_resource_full` into a single lemma.
11. Extend `valid_innings` with coherence conditions binding `inn_balls_faced` and `inn_balls_allocated` to their over-level counterparts.
12. Transcribe `dl2002_data` in `N` with a binary-numeral extraction mapping so the extracted table literals shrink from unary chains to logarithmic size.
13. Wrap the extracted calculator in a CLI and a js_of_ocaml build, giving club and league cricket, where the regulations prescribe the Standard Edition, a DLS calculator with a correctness pedigree.
14. Generate certified par-score sheets from the extracted table: for a given first-innings score, the full grid of par and target values over every balls-remaining and wickets combination, closing the sheet-to-human interface where the method historically fails.
15. Build a differential-testing oracle that fuzzes random match states and compares third-party DLS implementations against the extracted reference, each discrepancy carrying a machine-checked witness.
16. Publish the proven target-positivity, R2-monotonicity, and equal-resources score-plus-one theorems as a property-based test suite for other implementations.
17. Replay every rain-affected match of the 1992 and 1996 World Cups under the verified pipeline versus the rules then in force, publishing certified counterfactuals beyond the semi-final already in the file.
18. Drive live ball-by-ball par tracking from `ball_par_score` called per delivery.
19. Run identical match histories through `DLStandardTable`, `RationalDecayTable`, and `ICCStandardTable` and quantify how adjudication depends on model choice, exploiting the first-class `ResourceTable` abstraction.

# dls-verified

A machine-checked formalization of the Duckworth/Lewis Standard Edition
method for resetting targets in rain-interrupted limited-overs cricket,
with the authentic published resource table, in Rocq (Coq). Every proof
ends in `Qed`, the whole development passes `coqchk`, the computational
core is axiom-free, and the calculator extracts to OCaml. Outside the
ICC's proprietary Professional Edition software, this is — to our
knowledge — the first machine-verified implementation of the method
that governs real rain-affected matches.

## What is verified

**The published table, exactly.** `dl2002_data` transcribes the official
ball-by-ball Standard Edition table (ECB Duckworth/Lewis/Stern
Regulations; ICC Playing Handbook): 301 rows (balls remaining 0–300) x
10 columns (wickets lost 0–9) at the printed 0.1% resolution, which is
exact in `nat` at scale x10. The table's laws — monotone in balls
remaining, antitone in wickets lost, zero rows, 100% at a full innings —
are certified by `vm_compute` boolean sweeps over the entire grid and
lifted to unbounded indices by reflection. A checksum over all 3010
cells pins the transcription, and `tools/diff_table.py` diffs every
cell mechanically against the published table extracted from a
regulations PDF (verified against the ICC methodology document:
3010/3010 cells, zero mismatches). The per-over sheet (`DLStandardTable`) is
the over-boundary restriction of the per-ball data
(`DLStandardBallTable`); both are lawful instances of dependently-typed
table records that carry their span and their monotonicity and boundary
laws as fields, so every downstream theorem holds for any lawful table
at any format span; normalized restrictions of the published data
inhabit the records at the T20 and Hundred spans.

**The regulation formulae.** `revised_target` implements clause 5.6 of
the ECB regulations exactly (floor division is the regs' "ignoring any
figures after the decimal point"): scale down by the resource ratio when
Team 2 has fewer resources, inflate by the G50 share of the excess when
it has more, one run added; a `vm_compute` example replays the clause's
arithmetic on published table values. `par_score` and `par_result`
implement clause 5.5 with its accounting (resources lost to Team 2
suspensions are neither used nor available), `determine_result` decides
chases at the clause 2 boundary with the playing-condition exemptions
(the target is the minimum winning score; one short ties; reaching the
target or being dismissed decides the match even below the minimum
overs, with the regulations' example 7.1.1 transcribed), and
`decide_match` dispatches between target and par exactly as the
regulations prescribe for completed versus terminated chases, with
agreement theorems for each regime, the par trichotomy proven, and a
coherence theorem that the par regime cannot rob a chase that had
already reached its target. The ball-level pipeline
(`ball_revised_target`, `ball_target_from_states`,
`ball_par_from_states`, and the dispatcher `ball_decide_match`) works at
the table's 10000-scale, with theorems that it agrees with the
over-level formulae on corresponding inputs. The target is proven to be
the par plus one at both scales (clause 5.5's "without the one run
added"), and a soundness bundle over well-formed match states ties the
calculator to the validity layer: the decision is total, an undecided
sub-minimum match yields no result while dismissal and the target decide
regardless of the minimum, targets are positive, Team 2's used and
available resources partition their allocation, suspension losses fit
inside used resources so the clause 5.5 netting is exact rather than
truncated, a resource-exhausted chase meets its terminal par plus one,
and equal resources give score plus one.

**Fairness properties.** Targets are positive; equal resources give
target S+1; targets and par scores are monotone in Team 2's resources
across both method regimes; interruptions only remove resources;
interruption losses accumulate additively over any partition of the
history. Interruption histories are validated by an event-sequenced
predicate that threads the innings state through the list (at both
granularities), so each interruption carries the wicket count of its own
moment; under it, recorded losses are proven to fit inside the drop from
the history's start to its final position, which is what makes the par
netting exact. A single match history tagged by innings partitions into
the two suspension lists with no loss dropped or double-counted, and
both regulation G50 values (245, and 200 for associates, women's ODIs
and U15) are carried as positivity-certified configurations, either of
which yields a well-formed fresh match.

**A discovered fact about the published table.** The over-by-over sheet
narrowly fails concavity in wickets: between 38 and 39 overs remaining
the w=7 column steps 21.9 → 22.0 while the w=6 column is flat at 34.5 —
a 0.1% rounding artifact, proven as
`dl_standard_not_concave_in_wickets`. Linear interpolation between over
rows therefore cannot reconstruct a lawful ball table from the published
over sheet, which is why the per-ball table is transcribed directly.

**The 1992 World Cup semi-final, replayed.** England 252/6 in 45 overs;
South Africa 231/6 with 13 balls left when rain took 12 of them. The
Most Productive Overs rule demanded 21 off the final ball. The verified
pipeline computes, from the published table: R1 = 95.0%, resources lost
6.5%, R2 = 88.5%, revised target 235 — four to win off the final ball,
matching Duckworth and Lewis's published retrospective. South Africa
finished on 232: `result_1992` proves Team 1 wins.

## Additional models

- `RationalDecayTable`: the exponential-decay model approximated by a
  rational kernel, made lawful by an antitone envelope (the raw curves
  cross at very low overs — proven by example) and normalized to 100%
  at a full innings.
- `ICCStandardTable`: a separable approximation retained as a second
  synthetic instance.
- `TriangularTable`: a linear-in-wickets witness whose proven concavity
  certificate inhabits `BallTableFromInterpolation` — the constructor
  the published table is proven to refute — with examples showing the
  interpolated instance strictly finer than the over-floor projection.
- `T20NormalizedTable` and `HundredNormalizedBallTable`: the published
  data restricted and renormalized to the 20-over and 100-ball spans,
  inhabiting the span-indexed records away from the ODI anchor. No
  regulation fidelity is claimed: T20 practice reads the unnormalized
  table, whose ratios these preserve, and The Hundred runs the
  Professional Edition.
- `PowerplayBoostTable`: a what-if constructor that bakes a capped
  fielding-restriction boost into any lawful table and returns a lawful
  table, with the innings-level powerplay adjustment proven to coincide
  with reading the boosted table. The published tables are fitted to
  real innings and need no such adjustment; target computation never
  applies it.
- `DLS_Real`: the real-valued exponential model over `Reals` with
  symbolic monotonicity proofs, quarantined in its own module (the only
  part of the development that inherits the classical axioms of the
  `Reals` library).
- `DLS_Bridge`: the analytic-computational link, proving that
  `exp_decay_approx` tracks the exponential law Z0 (1 - exp(-b u/1000))
  at its own integer parameters within one unit of floor slack plus an
  exactly stated Taylor remainder, transported to the normalized table
  at zero wickets.

## Building

Requires Rocq 9.0 (opam packages `rocq-core`, `rocq-stdlib`).

```
make            # compile dls.v, regenerate dls_extracted.ml
make validate   # coqchk kernel validation
make extracted  # typecheck the extracted OCaml
make tools      # build the command-line calculator and test suite
make test       # run the property-based tests against the extraction
make js         # compile the calculator to JavaScript (needs js_of_ocaml)
```

CI builds, kernel-validates, typechecks the extraction, and runs the
property tests on `coq_version: 9.0`.

## Using the extracted calculator

`dls_extracted.ml`/`.mli` are generated by the build and committed. The
1992 computation, in OCaml:

```ocaml
open Dls_extracted
let tbl = DLS.coq_DLStandardBallTable
let r2  = DLS.effective_ball_resources tbl
            (DLS.ball_resources_at_start tbl 270) [DLS_Extras.sa_rain_1992]
let t   = DLS.ball_target_from_states tbl DLS_Extras.england_1992
            270 [] [DLS_Extras.sa_rain_1992] 245
(* t = 235 *)
```

`nat` extracts to `int` with native arithmetic (truncated subtraction,
guarded division), matching the Coq semantics on all cricket-scale
inputs; the published table is transcribed in binary `N`, so its 3010
literals stay logarithmic in the extracted module.

## Command-line calculator

`make tools` builds `tools/dls`, a front-end in which every printed
number comes from the extracted verified functions:

- `dls target` and `dls par` — clause 5.6 targets and clause 5.5 pars
  for arbitrary match states, interruptions given as
  `--t1-int`/`--t2-int AT:W:LOST` (balls remaining, wickets, balls
  removed).
- `dls sheet` — the umpires' par sheet: par at the end of every over
  for each wickets-lost column, plain text or `--csv`. Where scorers
  historically misread printed sheets (Durban 2003), this one is
  generated from the certified table.
- `dls track` — live ball-by-ball par from stdin.
- `dls oracle N SEED` — a reproducible differential-testing corpus:
  random match states with reference targets and pars as JSONL, for
  diffing any third-party DLS implementation against the verified
  semantics. The stream is bit-identical between the native build and
  the js_of_ocaml build.
- `dls sensitivity N SEED` — the same reduced matches run through the
  published, rational-decay, and separable tables, quantifying how much
  adjudication depends on model choice.
- `dls replay` — certified counterfactuals for every rain-affected
  match of the 1992 World Cup against the Most Productive Overs rule
  then in force (three results flip: Australia v India and South Africa
  v Pakistan at Brisbane, and India v Zimbabwe at Hamilton), plus the
  1996 finding that no innings was cut mid-match.

`make test` runs `tools/props`, the proven theorems replayed as
property-based tests (target positivity, R2 monotonicity, equal
resources give score plus one, par is the target less one, the scale
agreement, the completed-chase boundary, the table laws, and the
published anchors); rebind its `Impl` module to test another
implementation against the machine-checked semantics. `make js`
compiles the calculator to a single self-contained `tools/dls.js` for
node or a scorer's phone.

## Scope

This is the Standard Edition: the public, printed method that the
regulations themselves fall back to when the Professional Edition
software is unavailable, and the method in force internationally until
October 2003. G50 = 245 for full-member internationals, 200 for
associates, women's ODIs and U15 (regulations clause 1.12). The
Professional Edition's resource tables have never been published; its
match-specific curves live only inside ICC-licensed software, which is
what this repository's open, verified Standard Edition calculator
stands in for.

## Sources

- ECB, *Duckworth/Lewis/Stern Methodology of Re-calculating the Target
  Score in an Interrupted Match* (regulations and the published
  ball-by-ball table).
- Duckworth, F.C. and Lewis, A.J. (1998). A fair method for resetting
  the target in interrupted one-day cricket matches. *JORS* 49(3).
- Stern, S.E. (2016). The Duckworth-Lewis-Stern method. *JORS* 67(12).

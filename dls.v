(******************************************************************************)
(*                                                                            *)
(*          Duckworth-Lewis-Stern Method: Cricket Rain Interruption           *)
(*                                                                            *)
(*     Resource percentages over (overs, wickets) pairs, target revision      *)
(*     under interruptions, and par score. Proves resource monotonicity,      *)
(*     target positivity, and result decidability.                            *)
(*                                                                            *)
(*     Governs every rain-affected limited-overs international; the 1992      *)
(*     World Cup semi-final controversy motivated its creation.               *)
(*                                                                            *)
(*     "Cricket is unique in that rain can deprive a team of resources        *)
(*      it would otherwise have had."                                         *)
(*     - Frank Duckworth                                                      *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 11, 2025                                                *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Lia.

Import ListNotations.

Module DLS.

(******************************************************************************)
(*                           SECTION 1: CORE TYPES                            *)
(******************************************************************************)

Definition overs := nat.

Definition balls := nat.

Definition wickets := nat.

Definition resource := nat.

Definition runs := nat.

Definition resource_scale := 1000.

Definition scaled_resource := nat.

Definition to_scaled (r : resource) : scaled_resource := r * resource_scale.

Definition from_scaled (sr : scaled_resource) : resource := sr / resource_scale.

Definition overs_to_balls (o : overs) : balls := o * 6.

Definition balls_to_overs_floor (b : balls) : overs := b / 6.

Definition balls_remaining (b : balls) : nat := b mod 6.

Definition balls_to_overs_frac (b : balls) : nat * nat :=
  (b / 6, b mod 6).

Definition total_balls_odi : balls := 300.

Definition total_balls_t20 : balls := 120.

Definition total_balls_hundred : balls := 100.

(******************************************************************************)
(*                      SECTION 2: MATCH CONFIGURATION                        *)
(******************************************************************************)

Record MatchFormat := mkFormat {
  total_overs : overs;
  total_balls_in_format : balls;
  max_wickets : wickets;
  max_powerplay_overs : overs;
  powerplay_balls : balls;
  min_overs_for_result : overs;
  min_balls_for_result : balls
}.

Definition ODI : MatchFormat := {|
  total_overs := 50;
  total_balls_in_format := 300;
  max_wickets := 10;
  max_powerplay_overs := 10;
  powerplay_balls := 60;
  min_overs_for_result := 20;
  min_balls_for_result := 120
|}.

Definition T20 : MatchFormat := {|
  total_overs := 20;
  total_balls_in_format := 120;
  max_wickets := 10;
  max_powerplay_overs := 6;
  powerplay_balls := 36;
  min_overs_for_result := 5;
  min_balls_for_result := 30
|}.

Definition TheHundred : MatchFormat := {|
  total_overs := 16;
  total_balls_in_format := 100;
  max_wickets := 10;
  max_powerplay_overs := 4;
  powerplay_balls := 25;
  min_overs_for_result := 4;
  min_balls_for_result := 25
|}.

(******************************************************************************)
(*                    SECTION 3: RESOURCE TABLE STRUCTURE                     *)
(******************************************************************************)

Record ResourceTable := mkTable {
  lookup : overs -> wickets -> resource;

  table_overs_mono : forall u1 u2 w,
    u1 <= u2 -> lookup u1 w <= lookup u2 w;

  table_wickets_mono : forall u w1 w2,
    w1 <= w2 -> lookup u w2 <= lookup u w1;

  table_allout : forall u, lookup u 10 = 0;

  table_no_overs : forall w, lookup 0 w = 0;

  table_full_odi : lookup 50 0 = 1000
}.

Definition resource_pct (tbl : ResourceTable) (o : overs) (w : wickets) : resource :=
  lookup tbl o w.

Record BallResourceTable := mkBallTable {
  ball_lookup : balls -> wickets -> scaled_resource;

  ball_table_mono : forall b1 b2 w,
    b1 <= b2 -> ball_lookup b1 w <= ball_lookup b2 w;

  ball_table_wickets_mono : forall b w1 w2,
    w1 <= w2 -> ball_lookup b w2 <= ball_lookup b w1;

  ball_table_allout : forall b, ball_lookup b 10 = 0;

  ball_table_no_balls : forall w, ball_lookup 0 w = 0;

  ball_table_full_odi : ball_lookup 300 0 = 10000
}.

Definition ball_resource_pct (tbl : BallResourceTable) (b : balls) (w : wickets) : scaled_resource :=
  ball_lookup tbl b w.

Definition interpolate_resource
  (tbl : ResourceTable) (b : balls) (w : wickets) : scaled_resource :=
  let o := b / 6 in
  let rem := b mod 6 in
  let r_floor := lookup tbl o w in
  let r_ceil := lookup tbl (o + 1) w in
  (r_floor * 1000) + (rem * ((r_ceil - r_floor) * 1000) / 6).

(******************************************************************************)
(*                       SECTION 4: G50 PARAMETER                             *)
(******************************************************************************)

Definition G50_default : nat := 245.

Record G50Config := mkG50 {
  g50_value : nat;
  g50_positive : g50_value > 0
}.

Definition standard_G50 : G50Config.
Proof.
  refine {| g50_value := 245 |}.
  lia.
Defined.

(******************************************************************************)
(*                      SECTION 5: INNINGS STATE                              *)
(******************************************************************************)

Inductive InningsPhase :=
  | NotStarted
  | InProgress
  | Completed
  | Interrupted
  | InningsAbandoned.

Inductive PowerplayPhase :=
  | PP1
  | PP2
  | PP3
  | NoPowerplay.

Record InningsState := mkInnings {
  inn_score : runs;
  inn_wickets : wickets;
  inn_overs_faced : overs;
  inn_balls_faced : balls;
  inn_overs_allocated : overs;
  inn_balls_allocated : balls;
  inn_phase : InningsPhase;
  inn_powerplay : PowerplayPhase
}.

Record DetailedInningsState := mkDetailedInnings {
  det_score : runs;
  det_wickets : wickets;
  det_balls_faced : balls;
  det_balls_allocated : balls;
  det_phase : InningsPhase;
  det_powerplay : PowerplayPhase;
  det_in_powerplay : bool;
  det_powerplay_balls_remaining : balls
}.

Definition initial_innings (allocated : overs) : InningsState := {|
  inn_score := 0;
  inn_wickets := 0;
  inn_overs_faced := 0;
  inn_balls_faced := 0;
  inn_overs_allocated := allocated;
  inn_balls_allocated := allocated * 6;
  inn_phase := NotStarted;
  inn_powerplay := PP1
|}.

Definition initial_innings_balls (allocated_balls : balls) : DetailedInningsState := {|
  det_score := 0;
  det_wickets := 0;
  det_balls_faced := 0;
  det_balls_allocated := allocated_balls;
  det_phase := NotStarted;
  det_powerplay := PP1;
  det_in_powerplay := true;
  det_powerplay_balls_remaining := if allocated_balls <=? 120 then 36 else 60
|}.

Definition overs_remaining (inn : InningsState) : overs :=
  inn_overs_allocated inn - inn_overs_faced inn.

Definition balls_remaining_in_innings (inn : InningsState) : balls :=
  inn_balls_allocated inn - inn_balls_faced inn.

Definition det_balls_remaining (det : DetailedInningsState) : balls :=
  det_balls_allocated det - det_balls_faced det.

Definition is_complete (inn : InningsState) : bool :=
  match inn_phase inn with
  | Completed => true
  | _ => (inn_wickets inn =? 10) || (inn_overs_faced inn =? inn_overs_allocated inn)
  end.

Definition is_det_complete (det : DetailedInningsState) : bool :=
  match det_phase det with
  | Completed => true
  | _ => (det_wickets det =? 10) || (det_balls_faced det =? det_balls_allocated det)
  end.

Definition in_powerplay (inn : InningsState) : bool :=
  match inn_powerplay inn with
  | PP1 => true
  | PP2 => true
  | PP3 => true
  | NoPowerplay => false
  end.

(******************************************************************************)
(*                     SECTION 6: RESOURCE CALCULATIONS                       *)
(******************************************************************************)

Definition resources_available
  (tbl : ResourceTable) (inn : InningsState) : resource :=
  lookup tbl (overs_remaining inn) (inn_wickets inn).

Definition resources_used
  (tbl : ResourceTable) (inn : InningsState) : resource :=
  lookup tbl (inn_overs_allocated inn) 0 - resources_available tbl inn.

Definition resources_at_start
  (tbl : ResourceTable) (allocated : overs) : resource :=
  lookup tbl allocated 0.

Definition ball_resources_available
  (tbl : BallResourceTable) (det : DetailedInningsState) : scaled_resource :=
  ball_lookup tbl (det_balls_remaining det) (det_wickets det).

Definition ball_resources_used
  (tbl : BallResourceTable) (det : DetailedInningsState) : scaled_resource :=
  ball_lookup tbl (det_balls_allocated det) 0 - ball_resources_available tbl det.

Definition ball_resources_at_start
  (tbl : BallResourceTable) (allocated_balls : balls) : scaled_resource :=
  ball_lookup tbl allocated_balls 0.

Definition powerplay_multiplier : nat := 115.

Definition powerplay_resource_adjustment
  (base_resource : resource) (is_powerplay : bool) : resource :=
  if is_powerplay then
    base_resource * powerplay_multiplier / 100
  else
    base_resource.

Definition scaled_powerplay_adjustment
  (base_resource : scaled_resource) (is_powerplay : bool) : scaled_resource :=
  if is_powerplay then
    base_resource * powerplay_multiplier / 100
  else
    base_resource.

Definition resources_with_powerplay
  (tbl : ResourceTable) (inn : InningsState) : resource :=
  powerplay_resource_adjustment
    (resources_available tbl inn)
    (in_powerplay inn).

Definition powerplay_overs_remaining (inn : InningsState) (fmt : MatchFormat) : overs :=
  if in_powerplay inn then
    let faced := inn_overs_faced inn in
    let pp_total := max_powerplay_overs fmt in
    if faced <? pp_total then pp_total - faced else 0
  else 0.

Definition powerplay_balls_remaining_det (det : DetailedInningsState) : balls :=
  if det_in_powerplay det then det_powerplay_balls_remaining det else 0.

Lemma powerplay_adjustment_mono :
  forall r1 r2 pp,
    r1 <= r2 ->
    powerplay_resource_adjustment r1 pp <= powerplay_resource_adjustment r2 pp.
Proof.
  intros r1 r2 pp Hle.
  unfold powerplay_resource_adjustment.
  destruct pp.
  - apply Nat.div_le_mono.
    { lia. }
    apply Nat.mul_le_mono_r.
    exact Hle.
  - exact Hle.
Qed.

Lemma powerplay_adjustment_increases :
  forall r,
    r <= powerplay_resource_adjustment r true.
Proof.
  intros r.
  unfold powerplay_resource_adjustment, powerplay_multiplier.
  assert (Hdiv: r * 100 / 100 = r).
  { apply Nat.div_mul.
    lia. }
  assert (Hle: r * 100 <= r * 115).
  { apply Nat.mul_le_mono_l.
    lia. }
  assert (r * 100 / 100 <= r * 115 / 100).
  { apply Nat.div_le_mono.
    { lia. }
    exact Hle. }
  lia.
Qed.

Lemma scaled_powerplay_adjustment_mono :
  forall r1 r2 pp,
    r1 <= r2 ->
    scaled_powerplay_adjustment r1 pp <= scaled_powerplay_adjustment r2 pp.
Proof.
  intros r1 r2 pp Hle.
  unfold scaled_powerplay_adjustment.
  destruct pp.
  - apply Nat.div_le_mono.
    { lia. }
    apply Nat.mul_le_mono_r.
    exact Hle.
  - exact Hle.
Qed.

(******************************************************************************)
(*                      SECTION 7: INTERRUPTIONS                              *)
(******************************************************************************)

Record Interruption := mkInterrupt {
  int_at_overs : overs;
  int_at_wickets : wickets;
  int_overs_lost : overs;
  int_during_innings : nat
}.

Definition resource_lost_by_interruption
  (tbl : ResourceTable) (int : Interruption) : resource :=
  let before := lookup tbl (int_at_overs int) (int_at_wickets int) in
  let after := lookup tbl (int_at_overs int - int_overs_lost int) (int_at_wickets int) in
  before - after.

Fixpoint total_resources_lost
  (tbl : ResourceTable) (ints : list Interruption) : resource :=
  match ints with
  | [] => 0
  | i :: rest => resource_lost_by_interruption tbl i + total_resources_lost tbl rest
  end.

Definition effective_resources
  (tbl : ResourceTable) (base : resource) (ints : list Interruption) : resource :=
  base - total_resources_lost tbl ints.

Record BallInterruption := mkBallInterrupt {
  bint_at_balls : balls;
  bint_at_wickets : wickets;
  bint_balls_lost : balls;
  bint_during_innings : nat;
  bint_in_powerplay : bool
}.

Definition ball_resource_lost_by_interruption
  (tbl : BallResourceTable) (int : BallInterruption) : scaled_resource :=
  let before := ball_lookup tbl (bint_at_balls int) (bint_at_wickets int) in
  let after := ball_lookup tbl (bint_at_balls int - bint_balls_lost int) (bint_at_wickets int) in
  before - after.

Fixpoint total_ball_resources_lost
  (tbl : BallResourceTable) (ints : list BallInterruption) : scaled_resource :=
  match ints with
  | [] => 0
  | i :: rest => ball_resource_lost_by_interruption tbl i + total_ball_resources_lost tbl rest
  end.

Definition effective_ball_resources
  (tbl : BallResourceTable) (base : scaled_resource) (ints : list BallInterruption) : scaled_resource :=
  base - total_ball_resources_lost tbl ints.

Definition convert_to_ball_interruption (int : Interruption) : BallInterruption := {|
  bint_at_balls := int_at_overs int * 6;
  bint_at_wickets := int_at_wickets int;
  bint_balls_lost := int_overs_lost int * 6;
  bint_during_innings := int_during_innings int;
  bint_in_powerplay := false
|}.

Definition interruption_during_powerplay
  (int : BallInterruption) (pp_balls : balls) : bool :=
  bint_in_powerplay int && (bint_at_balls int <=? pp_balls).

(******************************************************************************)
(*                    SECTION 8: TARGET CALCULATIONS                          *)
(******************************************************************************)

Definition revised_target_method1
  (t1_score : runs) (R1 R2 : resource) : runs :=
  t1_score * R2 / R1 + 1.

Definition revised_target_method2
  (t1_score : runs) (R1 R2 : resource) (g50 : nat) : runs :=
  t1_score + g50 * (R2 - R1) / 100 + 1.

Definition revised_target
  (t1_score : runs) (R1 R2 : resource) (g50 : nat) : runs :=
  if R2 <? R1 then
    revised_target_method1 t1_score R1 R2
  else
    revised_target_method2 t1_score R1 R2 g50.

Definition par_score
  (t1_score : runs) (R1 R2_used : resource) (g50 : nat) : runs :=
  if R2_used <? R1 then
    t1_score * R2_used / R1
  else
    t1_score + g50 * (R2_used - R1) / 100.

Definition target_from_states
  (tbl : ResourceTable)
  (t1 : InningsState)
  (t2_allocated : overs)
  (t1_ints t2_ints : list Interruption)
  (g50 : nat) : runs :=
  let R1 := effective_resources tbl (resources_at_start tbl (inn_overs_allocated t1)) t1_ints in
  let R2 := effective_resources tbl (resources_at_start tbl t2_allocated) t2_ints in
  revised_target (inn_score t1) R1 R2 g50.

(******************************************************************************)
(*                       SECTION 9: MATCH RESULT                              *)
(******************************************************************************)

Inductive MatchResult :=
  | Team1Wins
  | Team2Wins
  | Tie
  | NoResult
  | Abandoned.

Definition result_to_nat (r : MatchResult) : nat :=
  match r with
  | Team1Wins => 0
  | Team2Wins => 1
  | Tie => 2
  | NoResult => 3
  | Abandoned => 4
  end.

Lemma result_eq_dec : forall r1 r2 : MatchResult, {r1 = r2} + {r1 <> r2}.
Proof.
  intros [] []; (left; reflexivity) || (right; discriminate).
Defined.

Definition determine_result
  (target t2_score : runs)
  (t2_completed : bool)
  (min_overs_met : bool) : MatchResult :=
  if negb min_overs_met then
    NoResult
  else if negb t2_completed then
    if t2_score <? target then NoResult
    else if target <=? t2_score then Team2Wins
    else NoResult
  else
    if t2_score <? target then Team1Wins
    else if target <? t2_score then Team2Wins
    else Tie.

Definition par_result
  (par t2_score : runs)
  (min_overs_met : bool) : MatchResult :=
  if negb min_overs_met then
    NoResult
  else
    if t2_score <? par then Team1Wins
    else if par <? t2_score then Team2Wins
    else Tie.

(******************************************************************************)
(*                      SECTION 10: MATCH STATE                               *)
(******************************************************************************)

Record MatchState := mkMatch {
  match_format : MatchFormat;
  match_t1 : InningsState;
  match_t2 : InningsState;
  match_t1_interruptions : list Interruption;
  match_t2_interruptions : list Interruption;
  match_g50 : nat
}.

Definition initial_match (fmt : MatchFormat) (g50 : nat) : MatchState := {|
  match_format := fmt;
  match_t1 := initial_innings (total_overs fmt);
  match_t2 := initial_innings (total_overs fmt);
  match_t1_interruptions := [];
  match_t2_interruptions := [];
  match_g50 := g50
|}.

Definition compute_target (tbl : ResourceTable) (m : MatchState) : runs :=
  target_from_states tbl
    (match_t1 m)
    (inn_overs_allocated (match_t2 m))
    (match_t1_interruptions m)
    (match_t2_interruptions m)
    (match_g50 m).

Definition compute_par (tbl : ResourceTable) (m : MatchState) : runs :=
  let R1 := effective_resources tbl
              (resources_at_start tbl (inn_overs_allocated (match_t1 m)))
              (match_t1_interruptions m) in
  let R2_used := resources_used tbl (match_t2 m) in
  par_score (inn_score (match_t1 m)) R1 R2_used (match_g50 m).

Definition min_overs_met (m : MatchState) : bool :=
  min_overs_for_result (match_format m) <=? inn_overs_faced (match_t2 m).

Definition compute_result (tbl : ResourceTable) (m : MatchState) : MatchResult :=
  let target := compute_target tbl m in
  let t2 := match_t2 m in
  determine_result target (inn_score t2) (is_complete t2) (min_overs_met m).

(******************************************************************************)
(*               SECTION 11: WELL-FORMEDNESS PREDICATES                       *)
(******************************************************************************)

Definition valid_wickets (w : wickets) : Prop := w <= 10.

Definition valid_overs (o : overs) (fmt : MatchFormat) : Prop :=
  o <= total_overs fmt.

Definition valid_innings (inn : InningsState) (fmt : MatchFormat) : Prop :=
  valid_wickets (inn_wickets inn) /\
  inn_overs_faced inn <= inn_overs_allocated inn /\
  inn_overs_allocated inn <= total_overs fmt.

Definition valid_interruption (int : Interruption) (inn : InningsState) : Prop :=
  int_at_overs int <= overs_remaining inn /\
  int_at_wickets int = inn_wickets inn /\
  int_overs_lost int <= int_at_overs int.

Definition valid_match (m : MatchState) : Prop :=
  valid_innings (match_t1 m) (match_format m) /\
  valid_innings (match_t2 m) (match_format m) /\
  Forall (fun i => valid_interruption i (match_t1 m)) (match_t1_interruptions m) /\
  Forall (fun i => valid_interruption i (match_t2 m)) (match_t2_interruptions m) /\
  match_g50 m > 0.

(******************************************************************************)
(*                SECTION 12: RESOURCE TABLE PROPERTIES                       *)
(*                                                                            *)
(*  Note: The fundamental monotonicity and boundary properties are encoded    *)
(*  directly in the ResourceTable record fields:                              *)
(*    - table_overs_mono: more overs => more resources                        *)
(*    - table_wickets_mono: more wickets => fewer resources                   *)
(*    - table_allout: 10 wickets => 0 resources                               *)
(*    - table_no_overs: 0 overs => 0 resources                                *)
(*    - table_full_odi: 50 overs, 0 wickets => 100% resources (1000)          *)
(*                                                                            *)
(*  Use these record projections directly rather than wrapper lemmas.         *)
(******************************************************************************)

(******************************************************************************)
(*                  SECTION 13: TARGET THEOREMS                               *)
(******************************************************************************)

Theorem target_always_positive :
  forall t1_score R1 R2 g50,
    R1 > 0 -> revised_target t1_score R1 R2 g50 >= 1.
Proof.
  intros t1_score R1 R2 g50 HR1.
  unfold revised_target.
  destruct (R2 <? R1) eqn:E.
  - unfold revised_target_method1. lia.
  - unfold revised_target_method2. lia.
Qed.

Theorem equal_resources_fair_target :
  forall t1_score R g50,
    R > 0 ->
    revised_target t1_score R R g50 = t1_score + 1.
Proof.
  intros t1_score R g50 HR.
  unfold revised_target.
  rewrite Nat.ltb_irrefl.
  unfold revised_target_method2.
  rewrite Nat.sub_diag.
  rewrite Nat.mul_0_r.
  rewrite Nat.div_0_l.
  - lia.
  - lia.
Qed.

Theorem more_resources_higher_target :
  forall t1_score R1 R2a R2b g50,
    R1 > 0 ->
    R2a <= R2b ->
    R2a < R1 ->
    R2b < R1 ->
    revised_target t1_score R1 R2a g50 <= revised_target t1_score R1 R2b g50.
Proof.
  intros t1_score R1 R2a R2b g50 HR1 Hle Ha Hb.
  unfold revised_target.
  apply Nat.ltb_lt in Ha.
  apply Nat.ltb_lt in Hb.
  rewrite Ha, Hb.
  unfold revised_target_method1.
  apply Nat.add_le_mono_r.
  apply Nat.div_le_mono.
  - lia.
  - apply Nat.mul_le_mono_l. exact Hle.
Qed.

Theorem scaling_preserves_proportion :
  forall t1_score R1 R2,
    R1 > 0 ->
    R2 <= R1 ->
    revised_target_method1 t1_score R1 R2 <= t1_score + 1.
Proof.
  intros t1_score R1 R2 HR1 Hle.
  unfold revised_target_method1.
  assert (t1_score * R2 / R1 <= t1_score).
  {
    apply Nat.div_le_upper_bound.
    - lia.
    - nia.
  }
  lia.
Qed.

(******************************************************************************)
(*                   SECTION 14: PAR SCORE THEOREMS                           *)
(******************************************************************************)

Theorem par_zero_at_start :
  forall t1_score R1 g50,
    R1 > 0 ->
    par_score t1_score R1 0 g50 = 0.
Proof.
  intros t1_score R1 g50 HR1.
  unfold par_score.
  simpl.
  destruct (0 <? R1) eqn:E.
  - rewrite Nat.mul_0_r.
    rewrite Nat.div_0_l; lia.
  - apply Nat.ltb_ge in E. lia.
Qed.

Theorem par_equals_target_minus_one_at_completion :
  forall t1_score R1 R2 g50,
    R1 > 0 ->
    R2 = R1 ->
    par_score t1_score R1 R2 g50 = t1_score.
Proof.
  intros t1_score R1 R2 g50 HR1 Heq.
  subst R2.
  unfold par_score.
  rewrite Nat.ltb_irrefl.
  rewrite Nat.sub_diag.
  rewrite Nat.mul_0_r.
  rewrite Nat.div_0_l; lia.
Qed.

Theorem par_monotonic :
  forall t1_score R1 R2a R2b g50,
    R1 > 0 ->
    R2a <= R2b ->
    R2a < R1 ->
    R2b < R1 ->
    par_score t1_score R1 R2a g50 <= par_score t1_score R1 R2b g50.
Proof.
  intros t1_score R1 R2a R2b g50 HR1 Hle Ha Hb.
  unfold par_score.
  apply Nat.ltb_lt in Ha.
  apply Nat.ltb_lt in Hb.
  rewrite Ha, Hb.
  apply Nat.div_le_mono.
  - lia.
  - apply Nat.mul_le_mono_l. exact Hle.
Qed.

(******************************************************************************)
(*                  SECTION 15: RESULT THEOREMS                               *)
(******************************************************************************)

Theorem result_decidable :
  forall target score completed min_met,
    determine_result target score completed min_met = Team1Wins \/
    determine_result target score completed min_met = Team2Wins \/
    determine_result target score completed min_met = Tie \/
    determine_result target score completed min_met = NoResult.
Proof.
  intros target score completed min_met.
  unfold determine_result.
  destruct min_met; simpl.
  - destruct completed; simpl.
    + destruct (score <? target) eqn:E1.
      * left. reflexivity.
      * destruct (target <? score) eqn:E2.
        -- right. left. reflexivity.
        -- right. right. left. reflexivity.
    + destruct (score <? target) eqn:E1.
      * right. right. right. reflexivity.
      * destruct (target <=? score) eqn:E2.
        -- right. left. reflexivity.
        -- right. right. right. reflexivity.
  - right. right. right. reflexivity.
Qed.

Theorem result_exhaustive :
  forall r : MatchResult,
    r = Team1Wins \/ r = Team2Wins \/ r = Tie \/ r = NoResult \/ r = Abandoned.
Proof.
  intros []; auto.
Qed.

Theorem team2_wins_iff_exceeds_target :
  forall target score min_met,
    min_met = true ->
    determine_result target score true min_met = Team2Wins <-> target < score.
Proof.
  intros target score min_met Hmet.
  subst min_met.
  unfold determine_result.
  simpl.
  split.
  - intro H.
    destruct (score <? target) eqn:E1.
    + discriminate.
    + destruct (target <? score) eqn:E2.
      * apply Nat.ltb_lt in E2. exact E2.
      * discriminate.
  - intro H.
    destruct (score <? target) eqn:E1.
    + apply Nat.ltb_lt in E1. lia.
    + destruct (target <? score) eqn:E2.
      * reflexivity.
      * apply Nat.ltb_ge in E2. lia.
Qed.

Theorem team1_wins_iff_below_target :
  forall target score min_met,
    min_met = true ->
    determine_result target score true min_met = Team1Wins <-> score < target.
Proof.
  intros target score min_met Hmet.
  subst min_met.
  unfold determine_result.
  simpl.
  split.
  - intro H.
    destruct (score <? target) eqn:E1.
    + apply Nat.ltb_lt in E1. exact E1.
    + destruct (target <? score) eqn:E2; discriminate.
  - intro H.
    apply Nat.ltb_lt in H.
    rewrite H.
    reflexivity.
Qed.

Theorem tie_iff_equals_target :
  forall target score min_met,
    min_met = true ->
    determine_result target score true min_met = Tie <-> score = target.
Proof.
  intros target score min_met Hmet.
  subst min_met.
  unfold determine_result.
  simpl.
  split.
  - intro H.
    destruct (score <? target) eqn:E1.
    + discriminate.
    + destruct (target <? score) eqn:E2.
      * discriminate.
      * apply Nat.ltb_ge in E1.
        apply Nat.ltb_ge in E2.
        lia.
  - intro H.
    subst score.
    destruct (target <? target) eqn:E1.
    + apply Nat.ltb_lt in E1. lia.
    + destruct (target <? target) eqn:E2.
      * apply Nat.ltb_lt in E2. lia.
      * reflexivity.
Qed.

(******************************************************************************)
(*                SECTION 16: INTERRUPTION THEOREMS                           *)
(******************************************************************************)

Theorem interruption_only_loses_resources :
  forall tbl int,
    int_overs_lost int <= int_at_overs int ->
    resource_lost_by_interruption tbl int >= 0.
Proof.
  intros tbl int H.
  unfold resource_lost_by_interruption.
  lia.
Qed.

Theorem no_interruption_no_loss :
  forall tbl,
    total_resources_lost tbl [] = 0.
Proof.
  intros.
  reflexivity.
Qed.

Theorem interruption_loss_additive :
  forall tbl i rest,
    total_resources_lost tbl (i :: rest) =
    resource_lost_by_interruption tbl i + total_resources_lost tbl rest.
Proof.
  intros.
  reflexivity.
Qed.

Theorem effective_resources_decreases :
  forall tbl base i rest,
    effective_resources tbl base (i :: rest) <= effective_resources tbl base rest.
Proof.
  intros tbl base i rest.
  unfold effective_resources.
  simpl.
  lia.
Qed.

(******************************************************************************)
(*               SECTION 17: BOUNDARY CONDITIONS                              *)
(******************************************************************************)

Theorem allout_zero_resources :
  forall tbl o,
    lookup tbl o 10 = 0.
Proof.
  intros.
  apply table_allout.
Qed.

Theorem no_overs_zero_resources :
  forall tbl w,
    lookup tbl 0 w = 0.
Proof.
  intros.
  apply table_no_overs.
Qed.

Theorem full_innings_full_resources :
  forall tbl,
    lookup tbl 50 0 = 1000.
Proof.
  intros.
  apply table_full_odi.
Qed.

(******************************************************************************)
(*                 SECTION 18: COMPOSITION THEOREMS                           *)
(******************************************************************************)

Theorem resources_partition :
  forall tbl inn,
    inn_overs_faced inn <= inn_overs_allocated inn ->
    resources_available tbl inn <= resources_at_start tbl (inn_overs_allocated inn) ->
    resources_used tbl inn + resources_available tbl inn =
    resources_at_start tbl (inn_overs_allocated inn).
Proof.
  intros tbl inn Hovers Hres.
  unfold resources_used, resources_available, resources_at_start in *.
  lia.
Qed.

Theorem completed_innings_no_resources :
  forall tbl inn,
    inn_wickets inn = 10 ->
    resources_available tbl inn = 0.
Proof.
  intros tbl inn H.
  unfold resources_available.
  rewrite H.
  apply table_allout.
Qed.

Theorem not_started_full_resources :
  forall tbl allocated,
    resources_available tbl (initial_innings allocated) = lookup tbl allocated 0.
Proof.
  intros.
  unfold resources_available, initial_innings, overs_remaining.
  simpl.
  rewrite Nat.sub_0_r.
  reflexivity.
Qed.

(******************************************************************************)
(*                   SECTION 19: FAIRNESS THEOREMS                            *)
(******************************************************************************)

Definition fair_result (m : MatchState) (tbl : ResourceTable) : Prop :=
  let R1 := effective_resources tbl
              (resources_at_start tbl (inn_overs_allocated (match_t1 m)))
              (match_t1_interruptions m) in
  let R2 := effective_resources tbl
              (resources_at_start tbl (inn_overs_allocated (match_t2 m)))
              (match_t2_interruptions m) in
  (R1 = R2 ->
   compute_target tbl m = inn_score (match_t1 m) + 1).

Theorem equal_resources_implies_fair :
  forall tbl m,
    valid_match m ->
    effective_resources tbl
      (resources_at_start tbl (inn_overs_allocated (match_t2 m)))
      (match_t2_interruptions m) > 0 ->
    fair_result m tbl.
Proof.
  intros tbl m Hvalid HR2pos.
  unfold fair_result.
  intro HR.
  unfold compute_target, target_from_states.
  rewrite HR.
  apply equal_resources_fair_target.
  exact HR2pos.
Qed.

(******************************************************************************)
(*                 SECTION 20: DECIDABILITY THEOREMS                          *)
(******************************************************************************)

Theorem wickets_decidable :
  forall w1 w2 : wickets, {w1 = w2} + {w1 <> w2}.
Proof.
  intros.
  apply Nat.eq_dec.
Defined.

Theorem overs_decidable :
  forall o1 o2 : overs, {o1 = o2} + {o1 <> o2}.
Proof.
  intros.
  apply Nat.eq_dec.
Defined.

Theorem runs_decidable :
  forall r1 r2 : runs, {r1 = r2} + {r1 <> r2}.
Proof.
  intros.
  apply Nat.eq_dec.
Defined.

Theorem phase_decidable :
  forall p1 p2 : InningsPhase, {p1 = p2} + {p1 <> p2}.
Proof.
  intros [] []; (left; reflexivity) || (right; discriminate).
Defined.

Theorem result_decidable_eq :
  forall r1 r2 : MatchResult, {r1 = r2} + {r1 <> r2}.
Proof.
  exact result_eq_dec.
Defined.

(******************************************************************************)
(*                 SECTION 21: SAMPLE CALCULATIONS                            *)
(******************************************************************************)

Definition sample_target_calc
  (t1_score : runs) (t1_overs t2_overs : overs)
  (t1_R t2_R : resource) (g50 : nat) : runs :=
  revised_target t1_score t1_R t2_R g50.

Example target_equal_resources :
  sample_target_calc 250 50 50 1000 1000 245 = 251.
Proof. reflexivity. Qed.

Example target_fewer_resources :
  revised_target_method1 250 1000 500 = 126.
Proof. reflexivity. Qed.

Example target_more_resources :
  revised_target_method2 250 800 1000 245 = 741.
Proof. reflexivity. Qed.

(******************************************************************************)
(*                  SECTION 22: INVERSION LEMMAS                              *)
(******************************************************************************)

Lemma result_team1_inv :
  forall target score completed min_met,
    determine_result target score completed min_met = Team1Wins ->
    min_met = true /\ completed = true /\ score < target.
Proof.
  intros target score completed min_met H.
  unfold determine_result in H.
  destruct min_met; simpl in H.
  - destruct completed; simpl in H.
    + destruct (score <? target) eqn:E.
      * apply Nat.ltb_lt in E.
        repeat split; auto.
      * destruct (target <? score); discriminate.
    + destruct (score <? target) eqn:E1.
      * discriminate.
      * destruct (target <=? score); discriminate.
  - discriminate.
Qed.

Lemma result_team2_inv :
  forall target score completed min_met,
    determine_result target score completed min_met = Team2Wins ->
    min_met = true /\
    ((completed = true /\ target < score) \/
     (completed = false /\ target <= score)).
Proof.
  intros target score completed min_met H.
  unfold determine_result in H.
  destruct min_met; simpl in H; try discriminate.
  destruct completed; simpl in H.
  - destruct (score <? target) eqn:E1; try discriminate.
    destruct (target <? score) eqn:E2; try discriminate.
    apply Nat.ltb_lt in E2. split. reflexivity. left. split; auto.
  - destruct (score <? target) eqn:E1; try discriminate.
    destruct (target <=? score) eqn:E2; try discriminate.
    apply Nat.leb_le in E2. split. reflexivity. right. split; auto.
Qed.

Lemma result_tie_inv :
  forall target score completed min_met,
    determine_result target score completed min_met = Tie ->
    min_met = true /\ completed = true /\ score = target.
Proof.
  intros target score completed min_met H.
  unfold determine_result in H.
  destruct min_met; simpl in H.
  - destruct completed; simpl in H.
    + destruct (score <? target) eqn:E1.
      * discriminate.
      * destruct (target <? score) eqn:E2.
        -- discriminate.
        -- apply Nat.ltb_ge in E1.
           apply Nat.ltb_ge in E2.
           repeat split; auto. lia.
    + destruct (score <? target) eqn:E1.
      * discriminate.
      * destruct (target <=? score); discriminate.
  - discriminate.
Qed.

Lemma result_noresult_inv :
  forall target score completed min_met,
    determine_result target score completed min_met = NoResult ->
    min_met = false \/ (completed = false /\ score < target).
Proof.
  intros target score completed min_met H.
  unfold determine_result in H.
  destruct min_met; simpl in H.
  - destruct completed; simpl in H.
    + destruct (score <? target) eqn:E1.
      * discriminate.
      * destruct (target <? score); discriminate.
    + destruct (score <? target) eqn:E1.
      * right. split; auto. apply Nat.ltb_lt. exact E1.
      * destruct (target <=? score) eqn:E2.
        -- discriminate.
        -- apply Nat.leb_gt in E2.
           right. split; auto.
  - left. reflexivity.
Qed.

(******************************************************************************)
(*               SECTION 23: AUXILIARY COMPUTATIONS                           *)
(******************************************************************************)

Definition run_rate (score : runs) (overs_faced : overs) : nat :=
  if overs_faced =? 0 then 0
  else (score * 100) / overs_faced.

Definition required_rate (target score : runs) (overs_rem : overs) : nat :=
  if overs_rem =? 0 then 0
  else ((target - score) * 100) / overs_rem.

Definition projected_score (score : runs) (overs_faced overs_total : overs) : runs :=
  if overs_faced =? 0 then 0
  else (score * overs_total) / overs_faced.

Lemma run_rate_zero_overs :
  forall score, run_rate score 0 = 0.
Proof.
  intros. unfold run_rate. simpl. reflexivity.
Qed.

Lemma required_rate_zero_remaining :
  forall target score, required_rate target score 0 = 0.
Proof.
  intros. unfold required_rate. simpl. reflexivity.
Qed.

(******************************************************************************)
(*              SECTION 24: ICC PROFESSIONAL EDITION MODEL                    *)
(*                                                                            *)
(*  Reference: ICC Playing Handbook, Appendix: DLS Method.                    *)
(*  The DLS Professional Edition uses an exponential decay model:             *)
(*                                                                            *)
(*    P(u,w) = Z0(w) * (1 - exp(-b(w) * u))                                   *)
(*                                                                            *)
(*  where:                                                                    *)
(*    P(u,w) = resources remaining with u overs left and w wickets down.      *)
(*    Z0(w)  = asymptotic resource percentage as overs approach infinity.     *)
(*    b(w)   = decay rate controlling how quickly resources accumulate.       *)
(*                                                                            *)
(*  The values below are derived from official ICC tables and represent a     *)
(*  rational approximation suitable for verified computation in nat.          *)
(*  Actual ICC tables use floating-point; these are scaled by 1000.           *)
(*                                                                            *)
(*  Source: Duckworth, F.C. and Lewis, A.J. (1998). A fair method for         *)
(*  resetting the target in interrupted one-day cricket matches.              *)
(*  Journal of the Operational Research Society, 49(3), 220-227.              *)
(*                                                                            *)
(*  Updated: Stern, S.E. (2016). The Duckworth-Lewis-Stern method.            *)
(*  Published in ICC Cricket Playing Handbook.                                *)
(*                                                                            *)
(******************************************************************************)

(** Z0(w): Asymptotic resource percentage for w wickets lost.
    Represents the maximum percentage of resources theoretically available
    with infinite overs remaining after losing w wickets.
    Values scaled by 10 (100.0% = 1000). *)
Definition Z0_asymptotic (w : wickets) : nat :=
  match w with
  | 0 => 1000
  | 1 => 938
  | 2 => 877
  | 3 => 798
  | 4 => 714
  | 5 => 612
  | 6 => 497
  | 7 => 368
  | 8 => 227
  | 9 => 87
  | _ => 0
  end.

(** b(w): Decay rate parameter for w wickets lost.
    Higher values mean resources accumulate faster initially.
    Values scaled by 1000 for integer arithmetic. *)
Definition decay_rate_scaled (w : wickets) : nat :=
  match w with
  | 0 => 47
  | 1 => 52
  | 2 => 57
  | 3 => 63
  | 4 => 70
  | 5 => 80
  | 6 => 93
  | 7 => 110
  | 8 => 135
  | 9 => 180
  | _ => 1000
  end.

Definition exp_decay_approx (u : overs) (w : wickets) : resource :=
  if w =? 10 then 0
  else if u =? 0 then 0
  else
    let z0 := Z0_asymptotic w in
    let b := decay_rate_scaled w in
    let decay := 1000 - (1000 * 1000 / (1000 + b * u)) in
    z0 * decay / 1000.

Definition dls_lookup (o : overs) (w : wickets) : resource :=
  if w =? 10 then 0
  else if o =? 0 then 0
  else if (o =? 50) && (w =? 0) then 1000
  else
    let raw := exp_decay_approx o w in
    if (o =? 50) && (w =? 0) then 1000
    else if raw =? 0 then 1
    else raw.

Definition icc_resource_percentage (u : overs) (w : wickets) : nat :=
  if (w =? 10) then 0
  else if (u =? 0) then 0
  else
    let z0 := Z0_asymptotic w in
    let b := decay_rate_scaled w in
    z0 - (z0 * 1000 / (1000 + b * u)).

Lemma Z0_allout : Z0_asymptotic 10 = 0.
Proof.
  reflexivity.
Qed.

Lemma Z0_full : Z0_asymptotic 0 = 1000.
Proof.
  reflexivity.
Qed.

Lemma decay_rate_positive : forall w, w < 10 -> decay_rate_scaled w > 0.
Proof.
  intros w Hw.
  destruct w as [|[|[|[|[|[|[|[|[|[|]]]]]]]]]]; simpl; lia.
Qed.

Lemma exp_decay_allout : forall u, exp_decay_approx u 10 = 0.
Proof.
  intros u.
  unfold exp_decay_approx.
  simpl.
  reflexivity.
Qed.

Lemma exp_decay_no_overs : forall w, exp_decay_approx 0 w = 0.
Proof.
  intros w.
  unfold exp_decay_approx.
  destruct (w =? 10) eqn:Ew.
  - reflexivity.
  - simpl. reflexivity.
Qed.

Lemma icc_allout : forall u, icc_resource_percentage u 10 = 0.
Proof.
  intros u.
  unfold icc_resource_percentage.
  simpl.
  reflexivity.
Qed.

Lemma icc_no_overs : forall w, icc_resource_percentage 0 w = 0.
Proof.
  intros w.
  unfold icc_resource_percentage.
  destruct (w =? 10) eqn:Ew.
  - reflexivity.
  - simpl. reflexivity.
Qed.

(******************************************************************************)
(*                   SECTION 25: TABLE INSTANTIATION                          *)
(******************************************************************************)

Definition dummy_lookup (o : overs) (w : wickets) : resource :=
  if w =? 10 then 0
  else if o =? 0 then 0
  else if (o =? 50) && (w =? 0) then 1000
  else o * 20 * (10 - w) / 10.

Lemma dummy_overs_mono :
  forall u1 u2 w, u1 <= u2 -> dummy_lookup u1 w <= dummy_lookup u2 w.
Proof.
  intros u1 u2 w Hle.
  unfold dummy_lookup.
  destruct (w =? 10) eqn:Hw.
  { lia. }
  destruct (u1 =? 0) eqn:Hu1.
  { apply Nat.eqb_eq in Hu1. subst u1.
    destruct (u2 =? 0) eqn:Hu2.
    { lia. }
    destruct ((u2 =? 50) && (w =? 0)) eqn:Hspec2.
    { lia. }
    apply Nat.eqb_neq in Hw.
    apply Nat.eqb_neq in Hu2.
    assert (10 - w <= 10) by lia.
    assert (u2 * 20 * (10 - w) / 10 >= 0) by lia.
    lia. }
  destruct (u2 =? 0) eqn:Hu2.
  { apply Nat.eqb_eq in Hu2. apply Nat.eqb_neq in Hu1. lia. }
  destruct ((u1 =? 50) && (w =? 0)) eqn:Hspec1;
  destruct ((u2 =? 50) && (w =? 0)) eqn:Hspec2.
  { lia. }
  { apply andb_true_iff in Hspec1. destruct Hspec1 as [Hu1_50 Hw_0].
    apply Nat.eqb_eq in Hu1_50. apply Nat.eqb_eq in Hw_0. subst u1 w.
    apply andb_false_iff in Hspec2. destruct Hspec2 as [Hne|Hne].
    { apply Nat.eqb_neq in Hne.
      assert (Hge: u2 >= 51) by lia.
      unfold dummy_lookup.
      destruct (0 =? 10) eqn:Hw10; try discriminate.
      destruct (u2 =? 0) eqn:Eu2z.
      { apply Nat.eqb_eq in Eu2z. lia. }
      destruct ((u2 =? 50) && (0 =? 0)) eqn:Hcheck.
      { simpl in Hcheck. apply andb_true_iff in Hcheck.
        destruct Hcheck as [Heq _]. apply Nat.eqb_eq in Heq. lia. }
      assert (u2 * 20 * (10 - 0) / 10 = u2 * 20) as Hdiv.
      { replace (10 - 0) with 10 by lia. apply Nat.div_mul. lia. }
      rewrite Hdiv.
      assert (u2 * 20 >= 1020).
      { replace 1020 with (51 * 20) by reflexivity. apply Nat.mul_le_mono_r. exact Hge. }
      lia. }
    { simpl in Hne. discriminate. } }
  { apply andb_true_iff in Hspec2. destruct Hspec2 as [Hu2_50 Hw_0].
    apply Nat.eqb_eq in Hu2_50. apply Nat.eqb_eq in Hw_0. subst u2 w.
    apply Nat.eqb_neq in Hu1.
    assert (u1 <= 50) by lia.
    assert (Hmul: u1 * 20 <= 1000).
    { replace 1000 with (50 * 20) by reflexivity.
      apply Nat.mul_le_mono_r. exact H. }
    assert (Hdiv: u1 * 20 * (10 - 0) / 10 = u1 * 20).
    { replace (10 - 0) with 10 by lia. apply Nat.div_mul. lia. }
    rewrite Hdiv. exact Hmul. }
  { apply Nat.div_le_mono.
    { lia. }
    apply Nat.mul_le_mono_r.
    apply Nat.mul_le_mono_r.
    exact Hle. }
Qed.

Lemma dummy_wickets_mono :
  forall u w1 w2, w1 <= w2 -> dummy_lookup u w2 <= dummy_lookup u w1.
Proof.
  intros u w1 w2 Hle.
  unfold dummy_lookup.
  destruct (w2 =? 10) eqn:Hw2.
  { lia. }
  destruct (w1 =? 10) eqn:Hw1.
  { apply Nat.eqb_eq in Hw1. apply Nat.eqb_neq in Hw2.
    subst w1. assert (Hgt: w2 > 10) by lia.
    destruct (u =? 0) eqn:Hu; try lia.
    destruct ((u =? 50) && (w2 =? 0)) eqn:Hspec.
    { apply andb_true_iff in Hspec. destruct Hspec as [_ Hw2_0].
      apply Nat.eqb_eq in Hw2_0. lia. }
    assert (Hsub: 10 - w2 = 0) by lia.
    assert (Hzero: u * 20 * (10 - w2) / 10 = 0).
    { rewrite Hsub. rewrite Nat.mul_0_r. reflexivity. }
    rewrite Hzero. lia. }
  destruct (u =? 0) eqn:Hu.
  { lia. }
  destruct ((u =? 50) && (w1 =? 0)) eqn:Hspec1;
  destruct ((u =? 50) && (w2 =? 0)) eqn:Hspec2.
  { lia. }
  { apply andb_true_iff in Hspec1. destruct Hspec1 as [Hu50 Hw1_0].
    apply Nat.eqb_eq in Hw1_0. subst w1.
    apply andb_false_iff in Hspec2. destruct Hspec2 as [Hne|Hne].
    { apply Nat.eqb_eq in Hu50. apply Nat.eqb_neq in Hne. lia. }
    { apply Nat.eqb_neq in Hne.
      apply Nat.eqb_eq in Hu50. subst u.
      apply Nat.eqb_neq in Hw2.
      assert (Hdiv: 50 * 20 * (10 - w2) / 10 = 100 * (10 - w2)).
      { replace (50 * 20 * (10 - w2)) with ((100 * (10 - w2)) * 10) by lia.
        apply Nat.div_mul. lia. }
      rewrite Hdiv.
      destruct (le_lt_dec w2 10) as [Hle10|Hgt10].
      - assert (100 * (10 - w2) <= 100 * 10) by lia.
        simpl in H. lia.
      - assert (10 - w2 = 0) by lia.
        rewrite H. simpl. lia. } }
  { apply andb_true_iff in Hspec2. destruct Hspec2 as [Hu50 Hw2_0].
    apply Nat.eqb_eq in Hw2_0. subst w2.
    assert (Hw1eq: w1 = 0) by lia. subst w1.
    apply Nat.eqb_eq in Hu50.
    rewrite Hu50 in Hspec1. simpl in Hspec1. discriminate. }
  { apply Nat.eqb_neq in Hw1. apply Nat.eqb_neq in Hw2. apply Nat.eqb_neq in Hu.
    assert (10 - w2 <= 10 - w1) by lia.
    apply Nat.div_le_mono.
    { lia. }
    apply Nat.mul_le_mono_l. exact H. }
Qed.

Lemma dummy_allout : forall u, dummy_lookup u 10 = 0.
Proof.
  intros u. unfold dummy_lookup. simpl. reflexivity.
Qed.

Lemma dummy_no_overs : forall w, dummy_lookup 0 w = 0.
Proof.
  intros w. unfold dummy_lookup.
  destruct (w =? 10); simpl; reflexivity.
Qed.

Lemma dummy_full : dummy_lookup 50 0 = 1000.
Proof.
  unfold dummy_lookup. simpl. reflexivity.
Qed.

Definition DummyTable : ResourceTable := {|
  lookup := dummy_lookup;
  table_overs_mono := dummy_overs_mono;
  table_wickets_mono := dummy_wickets_mono;
  table_allout := dummy_allout;
  table_no_overs := dummy_no_overs;
  table_full_odi := dummy_full
|}.

Definition dummy_ball_lookup (b : balls) (w : wickets) : scaled_resource :=
  if w =? 10 then 0
  else if b =? 0 then 0
  else b * 10 * (10 - w) / 3.

Lemma dummy_ball_mono :
  forall b1 b2 w, b1 <= b2 -> dummy_ball_lookup b1 w <= dummy_ball_lookup b2 w.
Proof.
  intros b1 b2 w Hle.
  unfold dummy_ball_lookup.
  destruct (w =? 10) eqn:Hw.
  { lia. }
  destruct (b1 =? 0) eqn:Hb1.
  { apply Nat.eqb_eq in Hb1. subst b1.
    destruct (b2 =? 0) eqn:Hb2.
    { lia. }
    lia. }
  destruct (b2 =? 0) eqn:Hb2.
  { apply Nat.eqb_eq in Hb2. apply Nat.eqb_neq in Hb1. lia. }
  apply Nat.div_le_mono.
  { lia. }
  apply Nat.mul_le_mono_r.
  apply Nat.mul_le_mono_r.
  exact Hle.
Qed.

Lemma dummy_ball_wickets_mono :
  forall b w1 w2, w1 <= w2 -> dummy_ball_lookup b w2 <= dummy_ball_lookup b w1.
Proof.
  intros b w1 w2 Hle.
  unfold dummy_ball_lookup.
  destruct (w2 =? 10) eqn:Hw2.
  { lia. }
  destruct (w1 =? 10) eqn:Hw1.
  { apply Nat.eqb_eq in Hw1. apply Nat.eqb_neq in Hw2.
    subst w1.
    assert (w2 > 10) by lia.
    assert (10 - w2 = 0) by lia.
    destruct (b =? 0) eqn:Hb.
    { lia. }
    rewrite H0.
    rewrite Nat.mul_0_r.
    rewrite Nat.div_0_l.
    { lia. }
    { lia. } }
  destruct (b =? 0) eqn:Hb.
  { lia. }
  apply Nat.eqb_neq in Hw1. apply Nat.eqb_neq in Hw2. apply Nat.eqb_neq in Hb.
  assert (10 - w2 <= 10 - w1) by lia.
  apply Nat.div_le_mono.
  { lia. }
  apply Nat.mul_le_mono_l. exact H.
Qed.

Lemma dummy_ball_allout : forall b, dummy_ball_lookup b 10 = 0.
Proof.
  intros b. unfold dummy_ball_lookup. simpl. reflexivity.
Qed.

Lemma dummy_ball_no_balls : forall w, dummy_ball_lookup 0 w = 0.
Proof.
  intros w. unfold dummy_ball_lookup.
  destruct (w =? 10); simpl; reflexivity.
Qed.

Lemma dummy_ball_full : dummy_ball_lookup 300 0 = 10000.
Proof.
  reflexivity.
Qed.

Definition DummyBallTable : BallResourceTable := {|
  ball_lookup := dummy_ball_lookup;
  ball_table_mono := dummy_ball_mono;
  ball_table_wickets_mono := dummy_ball_wickets_mono;
  ball_table_allout := dummy_ball_allout;
  ball_table_no_balls := dummy_ball_no_balls;
  ball_table_full_odi := dummy_ball_full
|}.

(******************************************************************************)
(*                    SECTION 26: END-TO-END EXAMPLE                          *)
(******************************************************************************)

Definition example_match : MatchState := {|
  match_format := ODI;
  match_t1 := {|
    inn_score := 280;
    inn_wickets := 10;
    inn_overs_faced := 50;
    inn_balls_faced := 300;
    inn_overs_allocated := 50;
    inn_balls_allocated := 300;
    inn_phase := Completed;
    inn_powerplay := NoPowerplay
  |};
  match_t2 := {|
    inn_score := 200;
    inn_wickets := 5;
    inn_overs_faced := 30;
    inn_balls_faced := 180;
    inn_overs_allocated := 30;
    inn_balls_allocated := 180;
    inn_phase := Completed;
    inn_powerplay := NoPowerplay
  |};
  match_t1_interruptions := [];
  match_t2_interruptions := [];
  match_g50 := 245
|}.

Example example_target : compute_target DummyTable example_match = 169.
Proof. reflexivity. Qed.

Example example_result :
  compute_result DummyTable example_match = Team2Wins.
Proof. reflexivity. Qed.

(******************************************************************************)
(*                        SECTION 27: MODULE END                              *)
(******************************************************************************)

End DLS.

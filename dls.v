(******************************************************************************)
(*                                                                            *)
(*          Duckworth-Lewis-Stern Method: Cricket Rain Interruption           *)
(*                                                                            *)
(*     The published Standard Edition resource table, target revision         *)
(*     under interruptions, par score, and result decision. Proves            *)
(*     resource monotonicity, target positivity, and result decidability;     *)
(*     replays the 1992 semi-final. Extracts to OCaml.                        *)
(*                                                                            *)
(*     Governs every rain-affected limited-overs international; the 1992      *)
(*     World Cup semi-final controversy motivated its creation.               *)
(*                                                                            *)
(*     Cricket is unique in that rain can deprive a team of resources         *)
(*     it would otherwise have had.                                           *)
(*     - Frank Duckworth                                                      *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 11, 2025                                                *)
(*     Revised: July 2, 2026                                                  *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.

Local Set Warnings "-abstract-large-number".

Import ListNotations.

Module DLS.

(******************************************************************************)
(*                              CORE TYPES                                   *)
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
(*                          MATCH CONFIGURATION                              *)
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
(*                        RESOURCE TABLE STRUCTURE                            *)
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
(*                            G50 PARAMETER                                  *)
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
(*                            INNINGS STATE                                  *)
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

Scheme Equality for InningsPhase.
Scheme Equality for PowerplayPhase.

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

Definition initial_innings_balls (fmt : MatchFormat) (allocated_balls : balls) : DetailedInningsState := {|
  det_score := 0;
  det_wickets := 0;
  det_balls_faced := 0;
  det_balls_allocated := allocated_balls;
  det_phase := NotStarted;
  det_powerplay := PP1;
  det_in_powerplay := true;
  det_powerplay_balls_remaining := Nat.min (powerplay_balls fmt) allocated_balls
|}.

Example odi_initial_powerplay :
  det_powerplay_balls_remaining (initial_innings_balls ODI 300) = 60.
Proof. reflexivity. Qed.

Example t20_initial_powerplay :
  det_powerplay_balls_remaining (initial_innings_balls T20 120) = 36.
Proof. reflexivity. Qed.

Example hundred_initial_powerplay :
  det_powerplay_balls_remaining (initial_innings_balls TheHundred 100) = 25.
Proof. reflexivity. Qed.

Example reduced_innings_powerplay_clamped :
  det_powerplay_balls_remaining (initial_innings_balls ODI 30) = 30.
Proof. reflexivity. Qed.

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
(*                          RESOURCE CALCULATIONS                            *)
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
  - apply Nat.Div0.div_le_mono.
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
  { apply Nat.Div0.div_le_mono.
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
  - apply Nat.Div0.div_le_mono.
    apply Nat.mul_le_mono_r.
    exact Hle.
  - exact Hle.
Qed.

(******************************************************************************)
(*                            INTERRUPTIONS                                  *)
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
(*                          TARGET CALCULATIONS                              *)
(******************************************************************************)

Definition revised_target_method1
  (t1_score : runs) (R1 R2 : resource) : runs :=
  t1_score * R2 / R1 + 1.

Definition revised_target_method2
  (t1_score : runs) (R1 R2 : resource) (g50 : nat) : runs :=
  t1_score + g50 * (R2 - R1) / 1000 + 1.

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
    t1_score + g50 * (R2_used - R1) / 1000.

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
(*                     BALL-LEVEL TARGET CALCULATIONS                         *)
(******************************************************************************)

(* Clause 5.6 divides the G50 share by 100 over percentages, hence by 1000 at the over-level 1000 = 100.0% scale and by 10000 at the ball-level 10000 scale; the agreement theorems relate the two. *)

Definition ball_revised_target
  (t1_score : runs) (R1 R2 : scaled_resource) (g50 : nat) : runs :=
  if R2 <? R1 then
    t1_score * R2 / R1 + 1
  else
    t1_score + g50 * (R2 - R1) / 10000 + 1.

Definition ball_par_score
  (t1_score : runs) (R1 R2_used : scaled_resource) (g50 : nat) : runs :=
  if R2_used <? R1 then
    t1_score * R2_used / R1
  else
    t1_score + g50 * (R2_used - R1) / 10000.

Lemma div_scale_cancel :
  forall a b k, k <> 0 -> (k * a) / (k * b) = a / b.
Proof.
  intros a b k Hk.
  rewrite <- Nat.Div0.div_div.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul by exact Hk.
  reflexivity.
Qed.

Theorem ball_revised_target_agrees :
  forall t1_score R1 R2 g50,
    ball_revised_target t1_score (10 * R1) (10 * R2) g50 =
    revised_target t1_score R1 R2 g50.
Proof.
  intros t1_score R1 R2 g50.
  unfold ball_revised_target, revised_target,
         revised_target_method1, revised_target_method2.
  destruct (R2 <? R1) eqn:E.
  - assert (E10 : (10 * R2 <? 10 * R1) = true).
    { apply Nat.ltb_lt. apply Nat.ltb_lt in E. lia. }
    rewrite E10.
    assert (Hd : t1_score * (10 * R2) / (10 * R1) = t1_score * R2 / R1).
    { replace (t1_score * (10 * R2)) with (10 * (t1_score * R2)) by nia.
      apply div_scale_cancel. lia. }
    lia.
  - assert (E10 : (10 * R2 <? 10 * R1) = false).
    { apply Nat.ltb_ge. apply Nat.ltb_ge in E. lia. }
    rewrite E10.
    assert (Hd : g50 * (10 * R2 - 10 * R1) / 10000 = g50 * (R2 - R1) / 1000).
    { replace (10 * R2 - 10 * R1) with (10 * (R2 - R1)) by lia.
      replace (g50 * (10 * (R2 - R1))) with (10 * (g50 * (R2 - R1))) by nia.
      change 10000 with (10 * 1000).
      apply div_scale_cancel. lia. }
    lia.
Qed.

Theorem ball_par_score_agrees :
  forall t1_score R1 R2u g50,
    ball_par_score t1_score (10 * R1) (10 * R2u) g50 =
    par_score t1_score R1 R2u g50.
Proof.
  intros t1_score R1 R2u g50.
  unfold ball_par_score, par_score.
  destruct (R2u <? R1) eqn:E.
  - assert (E10 : (10 * R2u <? 10 * R1) = true).
    { apply Nat.ltb_lt. apply Nat.ltb_lt in E. lia. }
    rewrite E10.
    replace (t1_score * (10 * R2u)) with (10 * (t1_score * R2u)) by nia.
    apply div_scale_cancel. lia.
  - assert (E10 : (10 * R2u <? 10 * R1) = false).
    { apply Nat.ltb_ge. apply Nat.ltb_ge in E. lia. }
    rewrite E10.
    assert (Hd : g50 * (10 * R2u - 10 * R1) / 10000 = g50 * (R2u - R1) / 1000).
    { replace (10 * R2u - 10 * R1) with (10 * (R2u - R1)) by lia.
      replace (g50 * (10 * (R2u - R1))) with (10 * (g50 * (R2u - R1))) by nia.
      change 10000 with (10 * 1000).
      apply div_scale_cancel. lia. }
    lia.
Qed.

Theorem ball_revised_target_is_par_plus_one :
  forall t1_score R1 R2 g50,
    ball_revised_target t1_score R1 R2 g50 =
    ball_par_score t1_score R1 R2 g50 + 1.
Proof.
  intros t1_score R1 R2 g50.
  unfold ball_revised_target, ball_par_score.
  destruct (R2 <? R1); reflexivity.
Qed.

Definition ball_target_from_states
  (tbl : BallResourceTable)
  (t1 : DetailedInningsState)
  (t2_allocated_balls : balls)
  (t1_ints t2_ints : list BallInterruption)
  (g50 : nat) : runs :=
  let R1 := effective_ball_resources tbl
              (ball_resources_at_start tbl (det_balls_allocated t1)) t1_ints in
  let R2 := effective_ball_resources tbl
              (ball_resources_at_start tbl t2_allocated_balls) t2_ints in
  ball_revised_target (det_score t1) R1 R2 g50.

(* Ball-level par with clause 5.5 accounting: resources lost to Team 2 suspensions are excluded from the used total. *)
Definition ball_resources_used_net
  (tbl : BallResourceTable) (det : DetailedInningsState)
  (ints : list BallInterruption) : scaled_resource :=
  ball_resources_used tbl det - total_ball_resources_lost tbl ints.

Definition ball_par_from_states
  (tbl : BallResourceTable)
  (t1 t2 : DetailedInningsState)
  (t1_ints t2_ints : list BallInterruption)
  (g50 : nat) : runs :=
  let R1 := effective_ball_resources tbl
              (ball_resources_at_start tbl (det_balls_allocated t1)) t1_ints in
  ball_par_score (det_score t1) R1 (ball_resources_used_net tbl t2 t2_ints) g50.

Theorem ball_par_from_states_no_t2_interruptions :
  forall tbl t1 t2 t1_ints g50,
    ball_par_from_states tbl t1 t2 t1_ints [] g50 =
    ball_par_score (det_score t1)
      (effective_ball_resources tbl
         (ball_resources_at_start tbl (det_balls_allocated t1)) t1_ints)
      (ball_resources_used tbl t2) g50.
Proof.
  intros tbl t1 t2 t1_ints g50.
  unfold ball_par_from_states, ball_resources_used_net. simpl.
  rewrite Nat.sub_0_r. reflexivity.
Qed.

Theorem ball_target_positive :
  forall t1_score R1 R2 g50,
    R1 > 0 -> ball_revised_target t1_score R1 R2 g50 >= 1.
Proof.
  intros. unfold ball_revised_target.
  destruct (R2 <? R1); lia.
Qed.

Theorem ball_target_monotone_in_R2 :
  forall t1_score R1 R2a R2b g50,
    R1 > 0 -> R2a <= R2b ->
    ball_revised_target t1_score R1 R2a g50 <=
    ball_revised_target t1_score R1 R2b g50.
Proof.
  intros t1_score R1 R2a R2b g50 HR1 Hle.
  unfold ball_revised_target.
  destruct (R2a <? R1) eqn:Ea; destruct (R2b <? R1) eqn:Eb.
  - apply Nat.add_le_mono_r.
    apply Nat.Div0.div_le_mono.
    apply Nat.mul_le_mono_l. exact Hle.
  - apply Nat.ltb_lt in Ea. apply Nat.ltb_ge in Eb.
    assert (t1_score * R2a / R1 <= t1_score).
    { apply Nat.Div0.div_le_upper_bound. nia. }
    lia.
  - apply Nat.ltb_ge in Ea. apply Nat.ltb_lt in Eb. lia.
  - apply Nat.ltb_ge in Ea, Eb.
    apply Nat.add_le_mono_r.
    apply Nat.add_le_mono_l.
    apply Nat.Div0.div_le_mono.
    apply Nat.mul_le_mono_l. lia.
Qed.

Theorem ball_equal_resources_fair :
  forall t1_score R g50,
    R > 0 ->
    ball_revised_target t1_score R R g50 = t1_score + 1.
Proof.
  intros t1_score R g50 HR.
  unfold ball_revised_target.
  rewrite Nat.ltb_irrefl.
  rewrite Nat.sub_diag, Nat.mul_0_r, Nat.Div0.div_0_l.
  lia.
Qed.

(******************************************************************************)
(*                            MATCH RESULT                                   *)
(******************************************************************************)

Inductive MatchResult :=
  | Team1Wins
  | Team2Wins
  | Tie
  | NoResult
  | Abandoned.

Scheme Equality for MatchResult.

Definition result_to_nat (r : MatchResult) : nat :=
  match r with
  | Team1Wins => 0
  | Team2Wins => 1
  | Tie => 2
  | NoResult => 3
  | Abandoned => 4
  end.

Definition result_eq_dec : forall r1 r2 : MatchResult, {r1 = r2} + {r1 <> r2} :=
  MatchResult_eq_dec.

(* Clause 2: the target is the minimum winning score, so a completed chase that reaches it wins and one run short ties. *)
Definition determine_result
  (target t2_score : runs)
  (t2_completed : bool)
  (min_overs_met : bool) : MatchResult :=
  if negb min_overs_met then
    NoResult
  else if negb t2_completed then
    if t2_score <? target then NoResult
    else Team2Wins
  else
    if target <=? t2_score then Team2Wins
    else if t2_score + 1 =? target then Tie
    else Team1Wins.

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
(*                             MATCH STATE                                   *)
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

(* Clause 5.5: R2_used excludes resources removed by Team 2 suspensions, which were neither used nor remain available. *)
Definition compute_par (tbl : ResourceTable) (m : MatchState) : runs :=
  let R1 := effective_resources tbl
              (resources_at_start tbl (inn_overs_allocated (match_t1 m)))
              (match_t1_interruptions m) in
  let R2_used := resources_used tbl (match_t2 m)
                 - total_resources_lost tbl (match_t2_interruptions m) in
  par_score (inn_score (match_t1 m)) R1 R2_used (match_g50 m).

(* On an interruption-free chase the netting is inert. *)
Theorem compute_par_no_t2_interruptions :
  forall tbl m,
    match_t2_interruptions m = [] ->
    compute_par tbl m =
    par_score (inn_score (match_t1 m))
      (effective_resources tbl
         (resources_at_start tbl (inn_overs_allocated (match_t1 m)))
         (match_t1_interruptions m))
      (resources_used tbl (match_t2 m))
      (match_g50 m).
Proof.
  intros tbl m H.
  unfold compute_par.
  rewrite H. simpl.
  rewrite Nat.sub_0_r. reflexivity.
Qed.

Definition min_overs_met (m : MatchState) : bool :=
  min_overs_for_result (match_format m) <=? inn_overs_faced (match_t2 m).

Definition compute_result (tbl : ResourceTable) (m : MatchState) : MatchResult :=
  let target := compute_target tbl m in
  let t2 := match_t2 m in
  determine_result target (inn_score t2) (is_complete t2) (min_overs_met m).

(******************************************************************************)
(*                      WELL-FORMEDNESS PREDICATES                           *)
(******************************************************************************)

Definition valid_wickets (w : wickets) : Prop := w <= 10.

Definition valid_overs (o : overs) (fmt : MatchFormat) : Prop :=
  o <= total_overs fmt.

Definition valid_innings (inn : InningsState) (fmt : MatchFormat) : Prop :=
  valid_wickets (inn_wickets inn) /\
  inn_overs_faced inn <= inn_overs_allocated inn /\
  inn_overs_allocated inn <= total_overs fmt /\
  inn_balls_faced inn <= inn_balls_allocated inn /\
  inn_balls_allocated inn = inn_overs_allocated inn * 6.

Lemma initial_innings_valid :
  forall fmt allocated,
    allocated <= total_overs fmt ->
    valid_innings (initial_innings allocated) fmt.
Proof.
  intros fmt allocated H.
  unfold valid_innings, valid_wickets, initial_innings; simpl.
  repeat split; lia.
Qed.

Definition valid_interruption (int : Interruption) (inn : InningsState) : Prop :=
  int_at_overs int <= overs_remaining inn /\
  int_at_wickets int = inn_wickets inn /\
  int_overs_lost int <= int_at_overs int.

(* Interruption histories are recorded in match order with the innings state threaded, so wickets are nondecreasing and overs remaining nonincreasing along the list. *)
Fixpoint valid_interruption_seq
  (wkts_so_far : wickets) (overs_left : overs)
  (ints : list Interruption) : Prop :=
  match ints with
  | [] => True
  | i :: rest =>
      int_at_overs i <= overs_left /\
      int_overs_lost i <= int_at_overs i /\
      wkts_so_far <= int_at_wickets i /\
      int_at_wickets i <= 10 /\
      valid_interruption_seq (int_at_wickets i) (int_at_overs i - int_overs_lost i) rest
  end.

Definition valid_match (m : MatchState) : Prop :=
  valid_innings (match_t1 m) (match_format m) /\
  valid_innings (match_t2 m) (match_format m) /\
  valid_interruption_seq 0 (inn_overs_allocated (match_t1 m)) (match_t1_interruptions m) /\
  valid_interruption_seq 0 (inn_overs_allocated (match_t2 m)) (match_t2_interruptions m) /\
  match_g50 m > 0.

(* Sequential validity yields the pointwise bound each loss computation needs. *)
Lemma valid_seq_losses_bounded :
  forall ints w r,
    valid_interruption_seq w r ints ->
    Forall (fun i => int_overs_lost i <= int_at_overs i) ints.
Proof.
  induction ints as [|i rest IH]; intros w r Hv.
  - constructor.
  - destruct Hv as (H1 & H2 & H3 & H4 & H5).
    constructor.
    + exact H2.
    + eapply IH. exact H5.
Qed.

(* Two interruptions at distinct wicket counts validate under the sequential predicate. *)
Example valid_seq_two_interruptions :
  valid_interruption_seq 0 50
    [ {| int_at_overs := 40; int_at_wickets := 2;
         int_overs_lost := 5; int_during_innings := 1 |} ;
      {| int_at_overs := 20; int_at_wickets := 6;
         int_overs_lost := 10; int_during_innings := 1 |} ].
Proof.
  simpl. repeat split; lia.
Qed.

(******************************************************************************)
(*                      RESOURCE TABLE PROPERTIES                            *)
(******************************************************************************)

(* The monotonicity and boundary laws are ResourceTable record fields; use the projections directly rather than wrapper lemmas. *)

(******************************************************************************)
(*                           TARGET THEOREMS                                 *)
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
  rewrite Nat.Div0.div_0_l.
  lia.
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
  apply Nat.Div0.div_le_mono.
  apply Nat.mul_le_mono_l. exact Hle.
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
    apply Nat.Div0.div_le_upper_bound.
    nia.
  }
  lia.
Qed.

(******************************************************************************)
(*                          PAR SCORE THEOREMS                               *)
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
    rewrite Nat.Div0.div_0_l. lia.
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
  rewrite Nat.Div0.div_0_l. lia.
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
  apply Nat.Div0.div_le_mono.
  apply Nat.mul_le_mono_l. exact Hle.
Qed.

(* Clause 5.5: the par is the target formula without the one run added. *)
Theorem revised_target_is_par_plus_one :
  forall t1_score R1 R2 g50,
    revised_target t1_score R1 R2 g50 = par_score t1_score R1 R2 g50 + 1.
Proof.
  intros t1_score R1 R2 g50.
  unfold revised_target, par_score,
         revised_target_method1, revised_target_method2.
  destruct (R2 <? R1); reflexivity.
Qed.

(******************************************************************************)
(*                           RESULT THEOREMS                                 *)
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
    + destruct (target <=? score) eqn:E1.
      * right. left. reflexivity.
      * destruct (score + 1 =? target) eqn:E2.
        -- right. right. left. reflexivity.
        -- left. reflexivity.
    + destruct (score <? target) eqn:E1.
      * right. right. right. reflexivity.
      * right. left. reflexivity.
  - right. right. right. reflexivity.
Qed.

Theorem result_exhaustive :
  forall r : MatchResult,
    r = Team1Wins \/ r = Team2Wins \/ r = Tie \/ r = NoResult \/ r = Abandoned.
Proof.
  intros []; auto.
Qed.

Theorem team2_wins_iff_reaches_target :
  forall target score min_met,
    min_met = true ->
    determine_result target score true min_met = Team2Wins <-> target <= score.
Proof.
  intros target score min_met Hmet.
  subst min_met.
  unfold determine_result.
  simpl.
  split.
  - intro H.
    destruct (target <=? score) eqn:E1.
    + apply Nat.leb_le. exact E1.
    + destruct (score + 1 =? target); discriminate.
  - intro H.
    apply Nat.leb_le in H.
    rewrite H.
    reflexivity.
Qed.

Theorem team1_wins_iff_below_tie_score :
  forall target score min_met,
    min_met = true ->
    determine_result target score true min_met = Team1Wins <-> score + 1 < target.
Proof.
  intros target score min_met Hmet.
  subst min_met.
  unfold determine_result.
  simpl.
  split.
  - intro H.
    destruct (target <=? score) eqn:E1.
    + discriminate.
    + destruct (score + 1 =? target) eqn:E2.
      * discriminate.
      * apply Nat.leb_gt in E1. apply Nat.eqb_neq in E2. lia.
  - intro H.
    assert (E1: (target <=? score) = false) by (apply Nat.leb_gt; lia).
    assert (E2: (score + 1 =? target) = false) by (apply Nat.eqb_neq; lia).
    rewrite E1, E2.
    reflexivity.
Qed.

Theorem tie_iff_one_short_of_target :
  forall target score min_met,
    min_met = true ->
    determine_result target score true min_met = Tie <-> score + 1 = target.
Proof.
  intros target score min_met Hmet.
  subst min_met.
  unfold determine_result.
  simpl.
  split.
  - intro H.
    destruct (target <=? score) eqn:E1.
    + discriminate.
    + destruct (score + 1 =? target) eqn:E2.
      * apply Nat.eqb_eq. exact E2.
      * discriminate.
  - intro H.
    assert (E1: (target <=? score) = false) by (apply Nat.leb_gt; lia).
    assert (E2: (score + 1 =? target) = true) by (apply Nat.eqb_eq; lia).
    rewrite E1, E2.
    reflexivity.
Qed.

(* Completed-chase boundary regressions: reaching the target wins, one short ties. *)
Example completed_chase_at_target_wins :
  determine_result 235 235 true true = Team2Wins.
Proof. reflexivity. Qed.

Example completed_chase_one_short_ties :
  determine_result 235 234 true true = Tie.
Proof. reflexivity. Qed.

(******************************************************************************)
(*                         INTERRUPTION THEOREMS                             *)
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
(*                          BOUNDARY CONDITIONS                              *)
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
(*                         COMPOSITION THEOREMS                              *)
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
(*                          FAIRNESS THEOREMS                                *)
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
(*                        DECIDABILITY THEOREMS                              *)
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

Definition phase_decidable :
  forall p1 p2 : InningsPhase, {p1 = p2} + {p1 <> p2} := InningsPhase_eq_dec.

Definition result_decidable_eq :
  forall r1 r2 : MatchResult, {r1 = r2} + {r1 <> r2} := MatchResult_eq_dec.

(******************************************************************************)
(*                         SAMPLE CALCULATIONS                               *)
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
  revised_target_method2 250 800 1000 245 = 300.
Proof. reflexivity. Qed.

(******************************************************************************)
(*                          INVERSION LEMMAS                                 *)
(******************************************************************************)

Lemma result_team1_inv :
  forall target score completed min_met,
    determine_result target score completed min_met = Team1Wins ->
    min_met = true /\ completed = true /\ score + 1 < target.
Proof.
  intros target score completed min_met H.
  unfold determine_result in H.
  destruct min_met; simpl in H.
  - destruct completed; simpl in H.
    + destruct (target <=? score) eqn:E1.
      * discriminate.
      * destruct (score + 1 =? target) eqn:E2.
        -- discriminate.
        -- apply Nat.leb_gt in E1. apply Nat.eqb_neq in E2.
           repeat split; auto. lia.
    + destruct (score <? target); discriminate.
  - discriminate.
Qed.

Lemma result_team2_inv :
  forall target score completed min_met,
    determine_result target score completed min_met = Team2Wins ->
    min_met = true /\ target <= score.
Proof.
  intros target score completed min_met H.
  unfold determine_result in H.
  destruct min_met; simpl in H; try discriminate.
  split; [reflexivity|].
  destruct completed; simpl in H.
  - destruct (target <=? score) eqn:E1.
    + apply Nat.leb_le. exact E1.
    + destruct (score + 1 =? target); discriminate.
  - destruct (score <? target) eqn:E1.
    + discriminate.
    + apply Nat.ltb_ge in E1. lia.
Qed.

Lemma result_tie_inv :
  forall target score completed min_met,
    determine_result target score completed min_met = Tie ->
    min_met = true /\ completed = true /\ score + 1 = target.
Proof.
  intros target score completed min_met H.
  unfold determine_result in H.
  destruct min_met; simpl in H.
  - destruct completed; simpl in H.
    + destruct (target <=? score) eqn:E1.
      * discriminate.
      * destruct (score + 1 =? target) eqn:E2.
        -- apply Nat.eqb_eq in E2. repeat split; auto.
        -- discriminate.
    + destruct (score <? target); discriminate.
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
    + destruct (target <=? score) eqn:E1.
      * discriminate.
      * destruct (score + 1 =? target); discriminate.
    + destruct (score <? target) eqn:E1.
      * right. split; auto. apply Nat.ltb_lt. exact E1.
      * discriminate.
  - left. reflexivity.
Qed.

(******************************************************************************)
(*                       AUXILIARY COMPUTATIONS                              *)
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
(*                   ICC PROFESSIONAL EDITION MODEL                          *)
(******************************************************************************)

(* Exponential-decay model P(u,w) = Z0(w) * (1 - exp(-b(w) * u)) after Duckworth-Lewis (JORS 49(3), 1998) and Stern (JORS 67(12), 2016), rationally approximated in nat at scale 1000. *)

(* Z0(w): asymptotic resource percentage with w wickets lost, scaled by 10. *)
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

(* b(w): decay rate with w wickets lost, scaled by 1000. *)
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

(* icc_resource_percentage is definitionally exp_decay_approx, so both boundary lemma sets certify one kernel. *)
Definition icc_resource_percentage (u : overs) (w : wickets) : nat :=
  exp_decay_approx u w.

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
  apply exp_decay_allout.
Qed.

Lemma icc_no_overs : forall w, icc_resource_percentage 0 w = 0.
Proof.
  intros w.
  apply exp_decay_no_overs.
Qed.

(******************************************************************************)
(*                 RATIONAL-DECAY MODEL AS A VERIFIED TABLE                   *)
(******************************************************************************)

(* The raw curves cross at very low overs (the early slope Z0(w) * b(w) grows with w through w = 3), so a running minimum restores wicket antitonicity, the domain caps at 50 overs, and normalization pins 100% at a full innings. *)

Lemma exp_decay_approx_mono_u :
  forall u1 u2 w, u1 <= u2 ->
    exp_decay_approx u1 w <= exp_decay_approx u2 w.
Proof.
  intros u1 u2 w Hle.
  unfold exp_decay_approx.
  destruct (w =? 10) eqn:Hw.
  - lia.
  - destruct (u1 =? 0) eqn:Hu1.
    + lia.
    + destruct (u2 =? 0) eqn:Hu2.
      * apply Nat.eqb_neq in Hu1. apply Nat.eqb_eq in Hu2. lia.
      * apply Nat.Div0.div_le_mono.
        apply Nat.mul_le_mono_l.
        assert (HA : 1000 * 1000 / (1000 + decay_rate_scaled w * u2) <=
                     1000 * 1000 / (1000 + decay_rate_scaled w * u1)).
        { apply Nat.div_le_compat_l.
          split.
          - lia.
          - apply Nat.add_le_mono_l.
            apply Nat.mul_le_mono_l. exact Hle. }
        assert (HB : 1000 * 1000 / (1000 + decay_rate_scaled w * u1) <= 1000).
        { apply Nat.Div0.div_le_upper_bound. nia. }
        lia.
Qed.

Fixpoint rational_capped (u : overs) (w : wickets) : resource :=
  match w with
  | 0 => exp_decay_approx u 0
  | S w' => Nat.min (exp_decay_approx u (S w')) (rational_capped u w')
  end.

Lemma rational_capped_mono_u :
  forall w u1 u2, u1 <= u2 ->
    rational_capped u1 w <= rational_capped u2 w.
Proof.
  induction w as [|w IH]; intros u1 u2 Hle; simpl.
  - apply exp_decay_approx_mono_u. exact Hle.
  - apply Nat.min_le_compat.
    + apply exp_decay_approx_mono_u. exact Hle.
    + apply IH. exact Hle.
Qed.

Lemma rational_capped_antitone_step :
  forall u w, rational_capped u (S w) <= rational_capped u w.
Proof.
  intros u w. simpl. apply Nat.le_min_r.
Qed.

Lemma rational_capped_antitone :
  forall u w1 w2, w1 <= w2 ->
    rational_capped u w2 <= rational_capped u w1.
Proof.
  intros u w1 w2 Hle.
  induction Hle as [|m Hle IH].
  - lia.
  - eapply Nat.le_trans; [apply rational_capped_antitone_step | exact IH].
Qed.

Lemma rational_capped_allout :
  forall u w, 10 <= w -> rational_capped u w = 0.
Proof.
  intros u w Hw.
  assert (H10 : rational_capped u 10 = 0).
  { change (rational_capped u 10) with
      (Nat.min (exp_decay_approx u 10) (rational_capped u 9)).
    rewrite exp_decay_allout. apply Nat.min_0_l. }
  assert (Hle := rational_capped_antitone u 10 w Hw).
  lia.
Qed.

Lemma rational_capped_no_overs :
  forall w, rational_capped 0 w = 0.
Proof.
  induction w as [|w IH]; simpl.
  - apply exp_decay_no_overs.
  - rewrite exp_decay_no_overs, IH. reflexivity.
Qed.

Lemma exp_decay_full_value : exp_decay_approx 50 0 = 702.
Proof. reflexivity. Qed.

(* Rational-decay lookup: capped domain, antitone envelope, normalized to 100% at a full innings. *)
Definition dls_lookup (o : overs) (w : wickets) : resource :=
  rational_capped (Nat.min o 50) w * 1000 / 702.

Lemma dls_lookup_overs_mono :
  forall u1 u2 w, u1 <= u2 -> dls_lookup u1 w <= dls_lookup u2 w.
Proof.
  intros u1 u2 w Hle.
  unfold dls_lookup.
  apply Nat.Div0.div_le_mono.
  apply Nat.mul_le_mono_r.
  apply rational_capped_mono_u.
  apply Nat.min_le_compat_r. exact Hle.
Qed.

Lemma dls_lookup_wickets_mono :
  forall u w1 w2, w1 <= w2 -> dls_lookup u w2 <= dls_lookup u w1.
Proof.
  intros u w1 w2 Hle.
  unfold dls_lookup.
  apply Nat.Div0.div_le_mono.
  apply Nat.mul_le_mono_r.
  apply rational_capped_antitone. exact Hle.
Qed.

Lemma dls_lookup_allout : forall u, dls_lookup u 10 = 0.
Proof.
  intros u. unfold dls_lookup.
  rewrite rational_capped_allout by lia.
  reflexivity.
Qed.

Lemma dls_lookup_no_overs : forall w, dls_lookup 0 w = 0.
Proof.
  intros w. unfold dls_lookup.
  simpl.
  rewrite rational_capped_no_overs. reflexivity.
Qed.

Lemma dls_lookup_full_odi : dls_lookup 50 0 = 1000.
Proof. reflexivity. Qed.

Definition RationalDecayTable : ResourceTable := {|
  lookup := dls_lookup;
  table_overs_mono := dls_lookup_overs_mono;
  table_wickets_mono := dls_lookup_wickets_mono;
  table_allout := dls_lookup_allout;
  table_no_overs := dls_lookup_no_overs;
  table_full_odi := dls_lookup_full_odi
|}.

(* In mid-innings territory the envelope coincides with the raw model. *)
Example rational_capped_agrees_mid :
  rational_capped 25 5 = exp_decay_approx 25 5.
Proof. reflexivity. Qed.

(* At one over left the raw model rates two wickets down above zero and the envelope bites. *)
Example rational_envelope_bites_low_overs :
  exp_decay_approx 1 2 = 47 /\ exp_decay_approx 1 0 = 45 /\
  rational_capped 1 2 = 45.
Proof. repeat split; reflexivity. Qed.

(******************************************************************************)
(*                       DUMMY TABLE INSTANTIATION                           *)
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
  { apply Nat.Div0.div_le_mono.
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
    apply Nat.Div0.div_le_mono.
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
  apply Nat.Div0.div_le_mono.
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
    rewrite Nat.Div0.div_0_l.
    lia. }
  destruct (b =? 0) eqn:Hb.
  { lia. }
  apply Nat.eqb_neq in Hw1. apply Nat.eqb_neq in Hw2. apply Nat.eqb_neq in Hb.
  assert (10 - w2 <= 10 - w1) by lia.
  apply Nat.Div0.div_le_mono.
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
(*                         END-TO-END EXAMPLE                                *)
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
(*                 SCHEME EQUALITY / UNIFORM DECIDABILITY                    *)
(******************************************************************************)

(* Scheme Equality at each inductive's definition site is the uniform decidability mechanism; the ladder names alias the generated instances. *)

Lemma InningsPhase_beq_refl : forall p, InningsPhase_beq p p = true.
Proof. intros []; reflexivity. Qed.

Lemma PowerplayPhase_beq_refl : forall p, PowerplayPhase_beq p p = true.
Proof. intros []; reflexivity. Qed.

Lemma MatchResult_beq_refl : forall r, MatchResult_beq r r = true.
Proof. intros []; reflexivity. Qed.

Lemma InningsPhase_beq_iff :
  forall p1 p2, InningsPhase_beq p1 p2 = true <-> p1 = p2.
Proof.
  intros [] []; simpl; split; intros H; try reflexivity; try discriminate.
Qed.

Lemma PowerplayPhase_beq_iff :
  forall p1 p2, PowerplayPhase_beq p1 p2 = true <-> p1 = p2.
Proof.
  intros [] []; simpl; split; intros H; try reflexivity; try discriminate.
Qed.

Lemma MatchResult_beq_iff :
  forall r1 r2, MatchResult_beq r1 r2 = true <-> r1 = r2.
Proof.
  intros [] []; simpl; split; intros H; try reflexivity; try discriminate.
Qed.

(* Uniform decision procedure for all four types *)
Definition match_result_eq_dec :
  forall r1 r2 : MatchResult, {r1 = r2} + {r1 <> r2} := MatchResult_eq_dec.

Definition phase_eq_dec :
  forall p1 p2 : InningsPhase, {p1 = p2} + {p1 <> p2} := InningsPhase_eq_dec.

Definition powerplay_eq_dec :
  forall p1 p2 : PowerplayPhase, {p1 = p2} + {p1 <> p2} := PowerplayPhase_eq_dec.

(******************************************************************************)
(*                   HINT DATABASE AND CUSTOM TACTICS                        *)
(******************************************************************************)

Create HintDb dls.

#[global] Hint Resolve table_overs_mono : dls.
#[global] Hint Resolve table_wickets_mono : dls.
#[global] Hint Resolve table_allout : dls.
#[global] Hint Resolve table_no_overs : dls.
#[global] Hint Resolve table_full_odi : dls.
#[global] Hint Resolve ball_table_mono : dls.
#[global] Hint Resolve ball_table_wickets_mono : dls.
#[global] Hint Resolve ball_table_allout : dls.
#[global] Hint Resolve ball_table_no_balls : dls.
#[global] Hint Resolve ball_table_full_odi : dls.
#[global] Hint Resolve Nat.Div0.div_le_mono : dls.
#[global] Hint Resolve Nat.mul_le_mono_l : dls.
#[global] Hint Resolve Nat.mul_le_mono_r : dls.
#[global] Hint Resolve Nat.add_le_mono_l : dls.
#[global] Hint Resolve Nat.add_le_mono_r : dls.
#[global] Hint Resolve target_always_positive : dls.

Ltac dls_arith := auto with dls arith; try lia; try nia.

Ltac dls_table_mono :=
  match goal with
  | [ |- lookup ?t ?u1 ?w <= lookup ?t ?u2 ?w ] =>
      apply (table_overs_mono t u1 u2 w); lia
  | [ |- lookup ?t ?u ?w2 <= lookup ?t ?u ?w1 ] =>
      apply (table_wickets_mono t u w1 w2); lia
  | [ |- ball_lookup ?t ?b1 ?w <= ball_lookup ?t ?b2 ?w ] =>
      apply (ball_table_mono t b1 b2 w); lia
  | [ |- ball_lookup ?t ?b ?w2 <= ball_lookup ?t ?b ?w1 ] =>
      apply (ball_table_wickets_mono t b w1 w2); lia
  end.

Ltac dls_unfold_target :=
  unfold revised_target, revised_target_method1, revised_target_method2, par_score.

(******************************************************************************)
(*                     MUTUAL EXCLUSION OF RESULT                            *)
(******************************************************************************)

Theorem result_outcomes_pairwise_distinct :
  Team1Wins <> Team2Wins /\
  Team1Wins <> Tie /\
  Team1Wins <> NoResult /\
  Team1Wins <> Abandoned /\
  Team2Wins <> Tie /\
  Team2Wins <> NoResult /\
  Team2Wins <> Abandoned /\
  Tie <> NoResult /\
  Tie <> Abandoned /\
  NoResult <> Abandoned.
Proof. repeat split; discriminate. Qed.

Theorem result_team1_excludes_others :
  forall target score completed min_met,
    determine_result target score completed min_met = Team1Wins ->
    determine_result target score completed min_met <> Team2Wins /\
    determine_result target score completed min_met <> Tie /\
    determine_result target score completed min_met <> NoResult /\
    determine_result target score completed min_met <> Abandoned.
Proof.
  intros target score completed min_met H.
  rewrite H. repeat split; discriminate.
Qed.

Theorem result_team2_excludes_others :
  forall target score completed min_met,
    determine_result target score completed min_met = Team2Wins ->
    determine_result target score completed min_met <> Team1Wins /\
    determine_result target score completed min_met <> Tie /\
    determine_result target score completed min_met <> NoResult /\
    determine_result target score completed min_met <> Abandoned.
Proof.
  intros target score completed min_met H.
  rewrite H. repeat split; discriminate.
Qed.

Theorem result_tie_excludes_others :
  forall target score completed min_met,
    determine_result target score completed min_met = Tie ->
    determine_result target score completed min_met <> Team1Wins /\
    determine_result target score completed min_met <> Team2Wins /\
    determine_result target score completed min_met <> NoResult /\
    determine_result target score completed min_met <> Abandoned.
Proof.
  intros target score completed min_met H.
  rewrite H. repeat split; discriminate.
Qed.

Theorem result_noresult_excludes_others :
  forall target score completed min_met,
    determine_result target score completed min_met = NoResult ->
    determine_result target score completed min_met <> Team1Wins /\
    determine_result target score completed min_met <> Team2Wins /\
    determine_result target score completed min_met <> Tie /\
    determine_result target score completed min_met <> Abandoned.
Proof.
  intros target score completed min_met H.
  rewrite H. repeat split; discriminate.
Qed.

Theorem determine_result_never_abandoned :
  forall target score completed min_met,
    determine_result target score completed min_met <> Abandoned.
Proof.
  intros target score completed min_met.
  unfold determine_result.
  destruct min_met, completed; simpl;
  repeat (destruct (_ <=? _); simpl);
  repeat (destruct (_ =? _); simpl);
  repeat (destruct (_ <? _); simpl);
  discriminate.
Qed.

Theorem result_trichotomy_completed :
  forall target score,
    let r := determine_result target score true true in
    (r = Team1Wins /\ score + 1 < target) \/
    (r = Team2Wins /\ target <= score) \/
    (r = Tie /\ score + 1 = target).
Proof.
  intros target score.
  unfold determine_result. simpl.
  destruct (target <=? score) eqn:E1.
  - right. left. split; [reflexivity | apply Nat.leb_le; exact E1].
  - destruct (score + 1 =? target) eqn:E2.
    + right. right. split; [reflexivity | apply Nat.eqb_eq; exact E2].
    + left. split; [reflexivity |].
      apply Nat.leb_gt in E1. apply Nat.eqb_neq in E2. lia.
Qed.

(* The exclusive disjunction form: exactly one of the cases holds *)
Theorem result_trichotomy_exclusive :
  forall target score,
    (determine_result target score true true = Team1Wins ->
       determine_result target score true true <> Team2Wins /\
       determine_result target score true true <> Tie) /\
    (determine_result target score true true = Team2Wins ->
       determine_result target score true true <> Team1Wins /\
       determine_result target score true true <> Tie) /\
    (determine_result target score true true = Tie ->
       determine_result target score true true <> Team1Wins /\
       determine_result target score true true <> Team2Wins).
Proof.
  intros target score.
  split; [|split]; intros H; split; rewrite H; discriminate.
Qed.

(******************************************************************************)
(*                   REVISED TARGET MONOTONICITY IN R2                       *)
(******************************************************************************)

Theorem target_monotone_in_R2 :
  forall t1_score R1 R2a R2b g50,
    R1 > 0 ->
    R2a <= R2b ->
    revised_target t1_score R1 R2a g50 <= revised_target t1_score R1 R2b g50.
Proof.
  intros t1_score R1 R2a R2b g50 HR1 Hle.
  unfold revised_target.
  destruct (R2a <? R1) eqn:Ea; destruct (R2b <? R1) eqn:Eb.
  - unfold revised_target_method1.
    apply Nat.add_le_mono_r.
    apply Nat.Div0.div_le_mono.
    apply Nat.mul_le_mono_l. exact Hle.
  - apply Nat.ltb_lt in Ea. apply Nat.ltb_ge in Eb.
    unfold revised_target_method1, revised_target_method2.
    assert (t1_score * R2a / R1 <= t1_score).
    { apply Nat.Div0.div_le_upper_bound. nia. }
    lia.
  - apply Nat.ltb_ge in Ea. apply Nat.ltb_lt in Eb. lia.
  - apply Nat.ltb_ge in Ea, Eb.
    unfold revised_target_method2.
    apply Nat.add_le_mono_r.
    apply Nat.add_le_mono_l.
    apply Nat.Div0.div_le_mono.
    apply Nat.mul_le_mono_l. lia.
Qed.

Theorem par_monotone_in_R2_used :
  forall t1_score R1 R2a R2b g50,
    R1 > 0 ->
    R2a <= R2b ->
    par_score t1_score R1 R2a g50 <= par_score t1_score R1 R2b g50.
Proof.
  intros t1_score R1 R2a R2b g50 HR1 Hle.
  unfold par_score.
  destruct (R2a <? R1) eqn:Ea; destruct (R2b <? R1) eqn:Eb.
  - apply Nat.Div0.div_le_mono. apply Nat.mul_le_mono_l. exact Hle.
  - apply Nat.ltb_lt in Ea. apply Nat.ltb_ge in Eb.
    assert (t1_score * R2a / R1 <= t1_score).
    { apply Nat.Div0.div_le_upper_bound. nia. }
    lia.
  - apply Nat.ltb_ge in Ea. apply Nat.ltb_lt in Eb. lia.
  - apply Nat.ltb_ge in Ea, Eb.
    apply Nat.add_le_mono_l.
    apply Nat.Div0.div_le_mono.
    apply Nat.mul_le_mono_l. lia.
Qed.

Theorem revised_target_method2_mono_in_g50 :
  forall t1_score R1 R2 g50a g50b,
    R2 >= R1 ->
    g50a <= g50b ->
    revised_target t1_score R1 R2 g50a <= revised_target t1_score R1 R2 g50b.
Proof.
  intros t1_score R1 R2 g50a g50b Hge Hle.
  unfold revised_target.
  destruct (R2 <? R1) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - unfold revised_target_method2.
    apply Nat.add_le_mono_r.
    apply Nat.add_le_mono_l.
    apply Nat.Div0.div_le_mono.
    apply Nat.mul_le_mono_r. exact Hle.
Qed.

(******************************************************************************)
(*                     UPPER BOUND ON REVISED TARGET                         *)
(******************************************************************************)

Theorem revised_target_method1_form :
  forall t1_score R1 R2 g50,
    R2 < R1 ->
    revised_target t1_score R1 R2 g50 = t1_score * R2 / R1 + 1.
Proof.
  intros. unfold revised_target.
  apply Nat.ltb_lt in H. rewrite H. reflexivity.
Qed.

Theorem revised_target_method2_form :
  forall t1_score R1 R2 g50,
    R2 >= R1 ->
    revised_target t1_score R1 R2 g50 = t1_score + g50 * (R2 - R1) / 1000 + 1.
Proof.
  intros. unfold revised_target.
  apply Nat.ltb_ge in H. rewrite H. reflexivity.
Qed.

Theorem revised_target_method1_bound :
  forall t1_score R1 R2 g50,
    R1 > 0 -> R2 <= R1 ->
    revised_target t1_score R1 R2 g50 <= t1_score + 1.
Proof.
  intros t1_score R1 R2 g50 HR1 Hle.
  unfold revised_target.
  destruct (R2 <? R1) eqn:E.
  - unfold revised_target_method1.
    apply Nat.add_le_mono_r.
    apply Nat.Div0.div_le_upper_bound. nia.
  - apply Nat.ltb_ge in E.
    unfold revised_target_method2.
    assert (R2 = R1) by lia. subst.
    rewrite Nat.sub_diag, Nat.mul_0_r, Nat.Div0.div_0_l.
    lia.
Qed.

Theorem revised_target_method2_bounded_by_g50_R2 :
  forall t1_score R1 R2 g50,
    R1 > 0 -> R2 >= R1 ->
    revised_target t1_score R1 R2 g50 <= t1_score + g50 * R2 / 1000 + 1.
Proof.
  intros t1_score R1 R2 g50 HR1 Hge.
  rewrite revised_target_method2_form by lia.
  apply Nat.add_le_mono_r.
  apply Nat.add_le_mono_l.
  apply Nat.Div0.div_le_mono.
  apply Nat.mul_le_mono_l. lia.
Qed.

(* Universal upper bound combining both regimes *)
Theorem revised_target_universal_upper_bound :
  forall t1_score R1 R2 g50 R_max,
    R1 > 0 -> R2 <= R_max ->
    revised_target t1_score R1 R2 g50 <= t1_score + g50 * R_max / 1000 + 1.
Proof.
  intros t1_score R1 R2 g50 R_max HR1 Hle.
  destruct (Compare_dec.le_lt_dec R1 R2) as [Hge|Hlt].
  - rewrite revised_target_method2_form by lia.
    apply Nat.add_le_mono_r.
    apply Nat.add_le_mono_l.
    apply Nat.Div0.div_le_mono.
    apply Nat.mul_le_mono_l. lia.
  - rewrite revised_target_method1_form by lia.
    apply Nat.add_le_mono_r.
    assert (t1_score * R2 / R1 <= t1_score).
    { apply Nat.Div0.div_le_upper_bound. nia. }
    assert (t1_score <= t1_score + g50 * R_max / 1000) by lia.
    lia.
Qed.

Theorem revised_target_lower_bound :
  forall t1_score R1 R2 g50,
    R1 > 0 ->
    revised_target t1_score R1 R2 g50 >= 1.
Proof. intros. apply target_always_positive. exact H. Qed.

(******************************************************************************)
(*                       MULTIPLE INTERRUPTIONS                              *)
(******************************************************************************)

Lemma total_resources_lost_app :
  forall tbl xs ys,
    total_resources_lost tbl (xs ++ ys) =
    total_resources_lost tbl xs + total_resources_lost tbl ys.
Proof.
  intros tbl xs ys.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Theorem total_resources_lost_swap :
  forall tbl x y rest,
    total_resources_lost tbl (x :: y :: rest) =
    total_resources_lost tbl (y :: x :: rest).
Proof.
  intros. simpl. lia.
Qed.

Lemma effective_resources_app :
  forall tbl base xs ys,
    effective_resources tbl base (xs ++ ys) =
    base - (total_resources_lost tbl xs + total_resources_lost tbl ys).
Proof.
  intros. unfold effective_resources. rewrite total_resources_lost_app. reflexivity.
Qed.

Theorem effective_resources_decreasing_in_list :
  forall tbl base xs ys,
    total_resources_lost tbl xs <= total_resources_lost tbl ys ->
    effective_resources tbl base ys <= effective_resources tbl base xs.
Proof.
  intros tbl base xs ys H.
  unfold effective_resources. lia.
Qed.

Theorem effective_resources_le_base :
  forall tbl base ints,
    effective_resources tbl base ints <= base.
Proof.
  intros. unfold effective_resources. lia.
Qed.

Theorem effective_resources_cons_dec :
  forall tbl base i ints,
    effective_resources tbl base (i :: ints) =
    effective_resources tbl base ints - resource_lost_by_interruption tbl i.
Proof.
  intros. unfold effective_resources. simpl. lia.
Qed.

Theorem effective_resources_when_overdepleted :
  forall tbl base ints,
    total_resources_lost tbl ints >= base ->
    effective_resources tbl base ints = 0.
Proof.
  intros. unfold effective_resources. lia.
Qed.

Theorem effective_resources_balance :
  forall tbl base ints,
    effective_resources tbl base ints + Nat.min base (total_resources_lost tbl ints) = base.
Proof.
  intros. unfold effective_resources.
  destruct (Compare_dec.le_lt_dec (total_resources_lost tbl ints) base).
  - rewrite Nat.min_r by lia. lia.
  - rewrite Nat.min_l by lia. lia.
Qed.

(* Generalized additivity: any partition of interruptions has cumulative loss *)
Lemma total_resources_lost_concat :
  forall tbl (lls : list (list Interruption)),
    total_resources_lost tbl (List.concat lls) =
    fold_right plus 0 (map (total_resources_lost tbl) lls).
Proof.
  intros tbl lls. induction lls as [|l lls IH]; simpl.
  - reflexivity.
  - rewrite total_resources_lost_app. rewrite IH. reflexivity.
Qed.

(* Multiple non-empty interruptions monotonically decrease effective resources *)
Theorem effective_resources_anti_monotone :
  forall tbl base ints_more ints_less,
    incl ints_less ints_more ->
    NoDup ints_more ->
    total_resources_lost tbl ints_less <= total_resources_lost tbl ints_more ->
    effective_resources tbl base ints_more <= effective_resources tbl base ints_less.
Proof.
  intros tbl base ints_more ints_less _ _ H.
  apply effective_resources_decreasing_in_list. exact H.
Qed.

(******************************************************************************)
(*                   TEAM 1 INTERRUPTIONS / G50 ROLE                         *)
(******************************************************************************)

(* Team 1 interruptions lower R1; when R2 exceeds the lowered R1, method 2 inflates the target by the G50 share. *)

Theorem t1_interruption_lowers_R1 :
  forall tbl base ints,
    effective_resources tbl base ints <= base.
Proof. intros. apply effective_resources_le_base. Qed.

Theorem t1_interruption_target_method2 :
  forall tbl base_R1 t1_score R2 ints g50,
    let R1' := effective_resources tbl base_R1 ints in
    R2 >= R1' ->
    revised_target t1_score R1' R2 g50 =
    t1_score + g50 * (R2 - R1') / 1000 + 1.
Proof.
  intros tbl base_R1 t1_score R2 ints g50 R1' Hge.
  apply revised_target_method2_form. lia.
Qed.

Theorem g50_role_when_R2_greater :
  forall t1_score R1 R2 g50,
    R1 > 0 -> R2 > R1 ->
    revised_target t1_score R1 R2 g50 >=
    revised_target t1_score R1 R1 g50.
Proof.
  intros t1_score R1 R2 g50 HR1 Hgt.
  apply target_monotone_in_R2; lia.
Qed.

(* Strict inflation when g50 * (R2 - R1) reaches a full integer share *)
Theorem g50_strict_inflation :
  forall t1_score R1 R2 g50,
    R1 > 0 -> R2 > R1 ->
    g50 * (R2 - R1) >= 1000 ->
    revised_target t1_score R1 R2 g50 >
    revised_target t1_score R1 R1 g50.
Proof.
  intros t1_score R1 R2 g50 HR1 Hgt H1000.
  rewrite equal_resources_fair_target by lia.
  rewrite revised_target_method2_form by lia.
  assert (g50 * (R2 - R1) / 1000 >= 1).
  { assert (Hgeq: 1000 <= g50 * (R2 - R1)) by lia.
    apply Nat.Div0.div_le_mono with (c := 1000) in Hgeq.
    rewrite Nat.div_same in Hgeq by lia. exact Hgeq. }
  lia.
Qed.

Theorem g50_zero_neutral :
  forall t1_score R1 R2,
    R1 > 0 -> R2 >= R1 ->
    revised_target t1_score R1 R2 0 = t1_score + 1.
Proof.
  intros t1_score R1 R2 HR1 Hge.
  rewrite revised_target_method2_form by lia.
  assert (H0: 0 * (R2 - R1) = 0) by lia.
  rewrite H0.
  rewrite Nat.Div0.div_0_l. lia.
Qed.

Theorem g50_inflation_monotone :
  forall t1_score R1 R2 g50_a g50_b,
    R2 >= R1 ->
    g50_a <= g50_b ->
    revised_target t1_score R1 R2 g50_a <= revised_target t1_score R1 R2 g50_b.
Proof. intros. apply revised_target_method2_mono_in_g50; assumption. Qed.

(* When T1 has an interruption and T2 plays full innings *)
Theorem t1_int_with_t2_full_uses_g50 :
  forall tbl t1_score t1_alloc t2_alloc t1_ints g50,
    let R1 := effective_resources tbl
                (resources_at_start tbl t1_alloc) t1_ints in
    let R2 := resources_at_start tbl t2_alloc in
    R2 >= R1 -> R1 > 0 ->
    revised_target t1_score R1 R2 g50 =
    t1_score + g50 * (R2 - R1) / 1000 + 1.
Proof.
  intros tbl t1_score t1_alloc t2_alloc t1_ints g50 R1 R2 Hgt HR1.
  apply revised_target_method2_form. lia.
Qed.

Theorem g50_with_zero_R_diff :
  forall t1_score R g50,
    R > 0 ->
    revised_target t1_score R R g50 = t1_score + 1.
Proof. intros. apply equal_resources_fair_target. exact H. Qed.

(******************************************************************************)
(*                        MIN-OVERS THRESHOLD                                *)
(******************************************************************************)

Definition is_abandoned_match (m : MatchState) : bool :=
  negb (min_overs_met m).

Theorem abandoned_match_no_result :
  forall tbl m,
    min_overs_met m = false ->
    compute_result tbl m = NoResult.
Proof.
  intros tbl m H.
  unfold compute_result.
  unfold determine_result.
  rewrite H. simpl. reflexivity.
Qed.

Theorem min_overs_met_iff :
  forall m,
    min_overs_met m = true <->
    min_overs_for_result (match_format m) <= inn_overs_faced (match_t2 m).
Proof.
  intros m. unfold min_overs_met.
  split; intro H.
  - apply Nat.leb_le. exact H.
  - apply Nat.leb_le. exact H.
Qed.

Theorem below_threshold_implies_noresult :
  forall tbl m,
    inn_overs_faced (match_t2 m) < min_overs_for_result (match_format m) ->
    compute_result tbl m = NoResult.
Proof.
  intros tbl m H.
  apply abandoned_match_no_result.
  unfold min_overs_met.
  apply Nat.leb_gt. exact H.
Qed.

Theorem above_threshold_completed_definite :
  forall tbl m,
    min_overs_for_result (match_format m) <= inn_overs_faced (match_t2 m) ->
    is_complete (match_t2 m) = true ->
    compute_result tbl m = Team1Wins \/
    compute_result tbl m = Team2Wins \/
    compute_result tbl m = Tie.
Proof.
  intros tbl m Hthresh Hcomp.
  unfold compute_result, determine_result.
  assert (Hmet: min_overs_met m = true).
  { unfold min_overs_met. apply Nat.leb_le. exact Hthresh. }
  rewrite Hmet. rewrite Hcomp. simpl.
  destruct (compute_target tbl m <=? inn_score (match_t2 m)) eqn:E1.
  - right. left. reflexivity.
  - destruct (inn_score (match_t2 m) + 1 =? compute_target tbl m) eqn:E2.
    + right. right. reflexivity.
    + left. reflexivity.
Qed.

(******************************************************************************)
(*                       COMBINED RESULT DECISION                             *)
(******************************************************************************)

(* Clause 5.5: a chase ended by stoppage after the minimum overs is judged against par; completed chases are judged by target (clause 7). *)

Definition ended_by_stoppage (p : InningsPhase) : bool :=
  match p with
  | Interrupted | InningsAbandoned => true
  | _ => false
  end.

Definition decide_match (tbl : ResourceTable) (m : MatchState) : MatchResult :=
  if negb (min_overs_met m) then NoResult
  else if ended_by_stoppage (inn_phase (match_t2 m)) then
    par_result (compute_par tbl m) (inn_score (match_t2 m)) true
  else
    determine_result (compute_target tbl m) (inn_score (match_t2 m))
      (is_complete (match_t2 m)) true.

Theorem decide_match_below_min :
  forall tbl m,
    min_overs_met m = false ->
    decide_match tbl m = NoResult.
Proof.
  intros tbl m H.
  unfold decide_match.
  rewrite H. reflexivity.
Qed.

Theorem decide_match_completed_agrees :
  forall tbl m,
    min_overs_met m = true ->
    inn_phase (match_t2 m) = Completed ->
    decide_match tbl m = compute_result tbl m.
Proof.
  intros tbl m Hmin Hphase.
  unfold decide_match, compute_result.
  rewrite Hmin, Hphase.
  reflexivity.
Qed.

Theorem decide_match_stopped_par :
  forall tbl m,
    min_overs_met m = true ->
    ended_by_stoppage (inn_phase (match_t2 m)) = true ->
    decide_match tbl m =
    par_result (compute_par tbl m) (inn_score (match_t2 m)) true.
Proof.
  intros tbl m Hmin Hstop.
  unfold decide_match.
  rewrite Hmin, Hstop. reflexivity.
Qed.

(* Clause 5.5 par trichotomy on a terminated chase: above par Team 2 win, level a tie, below Team 1 win. *)
Theorem decide_match_stopped_trichotomy :
  forall tbl m,
    min_overs_met m = true ->
    ended_by_stoppage (inn_phase (match_t2 m)) = true ->
    (decide_match tbl m = Team1Wins /\
       inn_score (match_t2 m) < compute_par tbl m) \/
    (decide_match tbl m = Team2Wins /\
       compute_par tbl m < inn_score (match_t2 m)) \/
    (decide_match tbl m = Tie /\
       inn_score (match_t2 m) = compute_par tbl m).
Proof.
  intros tbl m Hmin Hstop.
  rewrite (decide_match_stopped_par tbl m Hmin Hstop).
  unfold par_result. simpl.
  destruct (inn_score (match_t2 m) <? compute_par tbl m) eqn:E1.
  - left. split; [reflexivity | apply Nat.ltb_lt; exact E1].
  - destruct (compute_par tbl m <? inn_score (match_t2 m)) eqn:E2.
    + right; left. split; [reflexivity | apply Nat.ltb_lt; exact E2].
    + right; right. split; [reflexivity |].
      apply Nat.ltb_ge in E1. apply Nat.ltb_ge in E2. lia.
Qed.

(* Clause 7.1.1: set 186, Team 2 make 180 and fall 5 short of the 185 tie score; Team 1 win by 5. *)
Example ecb_example_7_1_1 :
  determine_result 186 180 true true = Team1Wins /\ 186 - 1 - 180 = 5.
Proof. split; reflexivity. Qed.

(* Clause 7.1.2: chasing 201, Team 2 are 115/4 with par 110 when the match is abandoned; Team 2 win by 5. *)
Example ecb_example_7_1_2 : par_result 110 115 true = Team2Wins.
Proof. reflexivity. Qed.

Lemma par_result_never_abandoned :
  forall par score min_met, par_result par score min_met <> Abandoned.
Proof.
  intros par score min_met.
  unfold par_result.
  destruct min_met; simpl;
  repeat (destruct (_ <? _); simpl);
  discriminate.
Qed.

Theorem decide_match_never_abandoned :
  forall tbl m, decide_match tbl m <> Abandoned.
Proof.
  intros tbl m.
  unfold decide_match.
  destruct (negb (min_overs_met m)); [discriminate|].
  destruct (ended_by_stoppage (inn_phase (match_t2 m))).
  - apply par_result_never_abandoned.
  - apply determine_result_never_abandoned.
Qed.

(* When Team 2's chase holds no further resources, the target is the terminal par plus the regulation one run. *)
Theorem compute_target_par_terminal :
  forall tbl m,
    resources_available tbl (match_t2 m) = 0 ->
    compute_target tbl m = compute_par tbl m + 1.
Proof.
  intros tbl m H.
  unfold compute_target, target_from_states, compute_par,
         resources_used, effective_resources, resources_at_start.
  rewrite H, Nat.sub_0_r.
  apply revised_target_is_par_plus_one.
Qed.

(* Soundness bundle over well-formed match states: the decision is total, sub-minimum matches yield no result, the target is positive, Team 2's resources partition, the terminal target-par link holds, and equal resources give score plus one. *)
Theorem calculator_sound_under_validity :
  forall tbl m,
    valid_match m ->
    effective_resources tbl
      (resources_at_start tbl (inn_overs_allocated (match_t1 m)))
      (match_t1_interruptions m) > 0 ->
    decide_match tbl m <> Abandoned /\
    (min_overs_met m = false -> decide_match tbl m = NoResult) /\
    compute_target tbl m >= 1 /\
    resources_used tbl (match_t2 m) + resources_available tbl (match_t2 m) =
      resources_at_start tbl (inn_overs_allocated (match_t2 m)) /\
    (resources_available tbl (match_t2 m) = 0 ->
       compute_target tbl m = compute_par tbl m + 1) /\
    fair_result m tbl.
Proof.
  intros tbl m Hvalid HR1.
  destruct Hvalid as (Hv1 & Hv2 & Hseq1 & Hseq2 & Hg50).
  destruct Hv2 as (Hw2 & Hov2 & Halloc2 & Hballs2 & Hcoh2).
  assert (Havail : resources_available tbl (match_t2 m) <=
                   resources_at_start tbl (inn_overs_allocated (match_t2 m))).
  { unfold resources_available, resources_at_start.
    eapply Nat.le_trans.
    - apply (table_wickets_mono tbl _ 0 (inn_wickets (match_t2 m))). lia.
    - apply table_overs_mono. unfold overs_remaining. lia. }
  repeat split.
  - apply decide_match_never_abandoned.
  - intro H. apply decide_match_below_min. exact H.
  - unfold compute_target, target_from_states.
    apply target_always_positive. exact HR1.
  - apply resources_partition; assumption.
  - intro H. apply compute_target_par_terminal. exact H.
  - unfold fair_result. intro HR.
    unfold compute_target, target_from_states.
    rewrite HR.
    apply equal_resources_fair_target.
    lia.
Qed.

Definition min_balls_met_det (det : DetailedInningsState) (fmt : MatchFormat) : bool :=
  min_balls_for_result fmt <=? det_balls_faced det.

Theorem min_balls_met_iff :
  forall det fmt,
    min_balls_met_det det fmt = true <->
    min_balls_for_result fmt <= det_balls_faced det.
Proof.
  intros det fmt. unfold min_balls_met_det.
  split; intro H.
  - apply Nat.leb_le. exact H.
  - apply Nat.leb_le. exact H.
Qed.

(* Format-specific thresholds *)
Theorem odi_min_threshold_value : min_overs_for_result ODI = 20.
Proof. reflexivity. Qed.

Theorem t20_min_threshold_value : min_overs_for_result T20 = 5.
Proof. reflexivity. Qed.

Theorem hundred_min_threshold_value : min_overs_for_result TheHundred = 4.
Proof. reflexivity. Qed.

Theorem odi_min_balls_threshold : min_balls_for_result ODI = 120.
Proof. reflexivity. Qed.

Theorem t20_min_balls_threshold : min_balls_for_result T20 = 30.
Proof. reflexivity. Qed.

Theorem hundred_min_balls_threshold : min_balls_for_result TheHundred = 25.
Proof. reflexivity. Qed.

Theorem min_threshold_consistent_odi :
  min_overs_for_result ODI * 6 = min_balls_for_result ODI.
Proof. reflexivity. Qed.

Theorem min_threshold_consistent_t20 :
  min_overs_for_result T20 * 6 = min_balls_for_result T20.
Proof. reflexivity. Qed.

(* The Hundred has a different ball-to-over ratio *)
Theorem hundred_min_thresholds_distinct :
  min_overs_for_result TheHundred * 6 <> min_balls_for_result TheHundred.
Proof. simpl. discriminate. Qed.

(******************************************************************************)
(*                         POWERPLAY THEOREMS                                *)
(******************************************************************************)

Theorem powerplay_multiplier_at_least_100 :
  powerplay_multiplier >= 100.
Proof.
  unfold powerplay_multiplier. lia.
Qed.

Theorem powerplay_resource_nondecreasing :
  forall r,
    r <= powerplay_resource_adjustment r true.
Proof. apply powerplay_adjustment_increases. Qed.

Theorem powerplay_off_identity :
  forall r,
    powerplay_resource_adjustment r false = r.
Proof. reflexivity. Qed.

Theorem powerplay_balls_consistent_odi :
  powerplay_balls ODI = max_powerplay_overs ODI * 6.
Proof. reflexivity. Qed.

Theorem powerplay_balls_consistent_t20 :
  powerplay_balls T20 = max_powerplay_overs T20 * 6.
Proof. reflexivity. Qed.

Theorem powerplay_balls_hundred :
  powerplay_balls TheHundred = 25.
Proof. reflexivity. Qed.

Theorem powerplay_overs_remaining_zero_when_done :
  forall inn fmt,
    in_powerplay inn = true ->
    max_powerplay_overs fmt <= inn_overs_faced inn ->
    powerplay_overs_remaining inn fmt = 0.
Proof.
  intros inn fmt Hpp Hge.
  unfold powerplay_overs_remaining.
  rewrite Hpp.
  destruct (inn_overs_faced inn <? max_powerplay_overs fmt) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - reflexivity.
Qed.

Theorem powerplay_overs_remaining_positive :
  forall inn fmt,
    in_powerplay inn = true ->
    inn_overs_faced inn < max_powerplay_overs fmt ->
    powerplay_overs_remaining inn fmt = max_powerplay_overs fmt - inn_overs_faced inn.
Proof.
  intros inn fmt Hpp Hlt.
  unfold powerplay_overs_remaining.
  rewrite Hpp.
  apply Nat.ltb_lt in Hlt as E. rewrite E. reflexivity.
Qed.

Theorem powerplay_no_powerplay_zero :
  forall inn fmt,
    in_powerplay inn = false ->
    powerplay_overs_remaining inn fmt = 0.
Proof.
  intros inn fmt H.
  unfold powerplay_overs_remaining. rewrite H. reflexivity.
Qed.

Theorem powerplay_consistent_odi :
  max_powerplay_overs ODI <= total_overs ODI.
Proof. simpl. lia. Qed.

Theorem powerplay_consistent_t20 :
  max_powerplay_overs T20 <= total_overs T20.
Proof. simpl. lia. Qed.

Theorem powerplay_consistent_hundred :
  max_powerplay_overs TheHundred <= total_overs TheHundred.
Proof. simpl. lia. Qed.

Theorem powerplay_adjustment_max_factor :
  forall r,
    powerplay_resource_adjustment r true <= r * 115 / 100.
Proof.
  intros r.
  unfold powerplay_resource_adjustment, powerplay_multiplier.
  lia.
Qed.

Theorem powerplay_adjustment_strict_increase :
  forall r,
    r >= 7 ->
    r < powerplay_resource_adjustment r true.
Proof.
  intros r Hr.
  unfold powerplay_resource_adjustment, powerplay_multiplier.
  assert (Hge: r * 100 + 100 <= r * 115).
  { nia. }
  assert (Hdiv: (r * 100 + 100) / 100 <= r * 115 / 100).
  { apply Nat.Div0.div_le_mono. exact Hge. }
  assert (Hcompute: (r * 100 + 100) / 100 = r + 1).
  { replace (r * 100 + 100) with ((r + 1) * 100) by lia.
    apply Nat.div_mul. lia. }
  lia.
Qed.

(******************************************************************************)
(*                   POWERPLAY-AWARE TABLE CONSTRUCTOR                        *)
(******************************************************************************)

(* Published tables already price mandatory powerplays, so target computation applies no multiplier; this constructor scopes the explicit what-if boost, capped at 100%, and returns a lawful table. *)

Definition powerplay_boost_lookup (tbl : ResourceTable) (o : overs) (w : wickets) : resource :=
  Nat.min 1000 (powerplay_resource_adjustment (lookup tbl o w) true).

Lemma powerplay_boost_overs_mono :
  forall tbl u1 u2 w, u1 <= u2 ->
    powerplay_boost_lookup tbl u1 w <= powerplay_boost_lookup tbl u2 w.
Proof.
  intros tbl u1 u2 w Hle.
  unfold powerplay_boost_lookup.
  assert (H : powerplay_resource_adjustment (lookup tbl u1 w) true <=
              powerplay_resource_adjustment (lookup tbl u2 w) true).
  { apply powerplay_adjustment_mono. apply table_overs_mono. exact Hle. }
  lia.
Qed.

Lemma powerplay_boost_wickets_mono :
  forall tbl u w1 w2, w1 <= w2 ->
    powerplay_boost_lookup tbl u w2 <= powerplay_boost_lookup tbl u w1.
Proof.
  intros tbl u w1 w2 Hle.
  unfold powerplay_boost_lookup.
  assert (H : powerplay_resource_adjustment (lookup tbl u w2) true <=
              powerplay_resource_adjustment (lookup tbl u w1) true).
  { apply powerplay_adjustment_mono. apply table_wickets_mono. exact Hle. }
  lia.
Qed.

Lemma powerplay_boost_allout :
  forall tbl u, powerplay_boost_lookup tbl u 10 = 0.
Proof.
  intros tbl u.
  unfold powerplay_boost_lookup.
  rewrite table_allout.
  reflexivity.
Qed.

Lemma powerplay_boost_no_overs :
  forall tbl w, powerplay_boost_lookup tbl 0 w = 0.
Proof.
  intros tbl w.
  unfold powerplay_boost_lookup.
  rewrite table_no_overs.
  reflexivity.
Qed.

Lemma powerplay_boost_full_odi :
  forall tbl, powerplay_boost_lookup tbl 50 0 = 1000.
Proof.
  intros tbl.
  unfold powerplay_boost_lookup.
  rewrite table_full_odi.
  reflexivity.
Qed.

Definition PowerplayBoostTable (tbl : ResourceTable) : ResourceTable := {|
  lookup := powerplay_boost_lookup tbl;
  table_overs_mono := powerplay_boost_overs_mono tbl;
  table_wickets_mono := powerplay_boost_wickets_mono tbl;
  table_allout := powerplay_boost_allout tbl;
  table_no_overs := powerplay_boost_no_overs tbl;
  table_full_odi := powerplay_boost_full_odi tbl
|}.

Theorem powerplay_boost_dominates :
  forall tbl o w,
    lookup tbl o w <= 1000 ->
    lookup tbl o w <= lookup (PowerplayBoostTable tbl) o w.
Proof.
  intros tbl o w Hcap.
  simpl.
  unfold powerplay_boost_lookup.
  assert (H := powerplay_adjustment_increases (lookup tbl o w)).
  lia.
Qed.

(******************************************************************************)
(*                     THE HUNDRED FORMAT THEOREMS                           *)
(******************************************************************************)

Theorem hundred_total_balls : total_balls_in_format TheHundred = 100.
Proof. reflexivity. Qed.

Theorem hundred_total_overs : total_overs TheHundred = 16.
Proof. reflexivity. Qed.

Theorem hundred_min_result_overs : min_overs_for_result TheHundred = 4.
Proof. reflexivity. Qed.

Theorem hundred_min_result_balls : min_balls_for_result TheHundred = 25.
Proof. reflexivity. Qed.

Theorem hundred_max_wickets : max_wickets TheHundred = 10.
Proof. reflexivity. Qed.

Theorem hundred_max_powerplay : max_powerplay_overs TheHundred = 4.
Proof. reflexivity. Qed.

Theorem hundred_powerplay_balls : powerplay_balls TheHundred = 25.
Proof. reflexivity. Qed.

Theorem hundred_below_threshold_no_result :
  forall tbl t2,
    inn_overs_faced t2 < 4 ->
    let m := {| match_format := TheHundred;
                match_t1 := initial_innings 16;
                match_t2 := t2;
                match_t1_interruptions := [];
                match_t2_interruptions := [];
                match_g50 := 245 |} in
    compute_result tbl m = NoResult.
Proof.
  intros tbl t2 H m.
  apply below_threshold_implies_noresult.
  simpl. exact H.
Qed.

Theorem hundred_fewer_balls_than_t20 :
  total_balls_in_format TheHundred < total_balls_in_format T20.
Proof. simpl. lia. Qed.

Theorem hundred_fewer_balls_than_odi :
  total_balls_in_format TheHundred < total_balls_in_format ODI.
Proof. simpl. lia. Qed.

Theorem hundred_shorter_powerplay :
  max_powerplay_overs TheHundred <= max_powerplay_overs ODI.
Proof. simpl. lia. Qed.

Theorem hundred_powerplay_proportion :
  let pp := max_powerplay_overs TheHundred in
  let tot := total_overs TheHundred in
  pp * 4 = tot.
Proof. simpl. lia. Qed.

(* The Hundred is 100 balls in twenty five-ball sets; total_overs 16 is the six-ball floor used by the overs machinery, the ball-native model below the faithful one. *)
Theorem hundred_format_consistency :
  total_balls_in_format TheHundred = 100 /\
  total_overs TheHundred = 16 /\
  max_powerplay_overs TheHundred = 4.
Proof. repeat split; reflexivity. Qed.

Definition hundred_sets : nat := 20.

Definition balls_per_set : nat := 5.

Theorem hundred_balls_from_sets :
  hundred_sets * balls_per_set = total_balls_in_format TheHundred.
Proof. reflexivity. Qed.

(* Ball-native innings for The Hundred: 100 balls and a 25-ball powerplay through DetailedInningsState. *)
Definition hundred_innings : DetailedInningsState :=
  initial_innings_balls TheHundred (total_balls_in_format TheHundred).

Example hundred_innings_allocation :
  det_balls_allocated hundred_innings = 100.
Proof. reflexivity. Qed.

Example hundred_innings_powerplay :
  det_powerplay_balls_remaining hundred_innings = 25.
Proof. reflexivity. Qed.

Theorem hundred_min_balls_equals_powerplay :
  min_balls_for_result TheHundred = powerplay_balls TheHundred.
Proof. reflexivity. Qed.

(******************************************************************************)
(*               INTERPOLATED BALL TABLE FROM OVERS TABLE                      *)
(******************************************************************************)

(* Over-floor projection: the simplest lawful BallResourceTable from a ResourceTable. *)

Definition over_lookup_to_ball (tbl : ResourceTable) (b : balls) (w : wickets) : scaled_resource :=
  let o := Nat.min (b / 6) 50 in
  lookup tbl o w * 10.

Lemma over_lookup_to_ball_mono :
  forall tbl b1 b2 w,
    b1 <= b2 ->
    over_lookup_to_ball tbl b1 w <= over_lookup_to_ball tbl b2 w.
Proof.
  intros tbl b1 b2 w Hle.
  unfold over_lookup_to_ball.
  apply Nat.mul_le_mono_r.
  apply table_overs_mono.
  apply Nat.min_le_compat_r.
  apply Nat.Div0.div_le_mono. exact Hle.
Qed.

Lemma over_lookup_to_ball_wickets_mono :
  forall tbl b w1 w2,
    w1 <= w2 ->
    over_lookup_to_ball tbl b w2 <= over_lookup_to_ball tbl b w1.
Proof.
  intros tbl b w1 w2 Hle.
  unfold over_lookup_to_ball.
  apply Nat.mul_le_mono_r.
  apply table_wickets_mono. exact Hle.
Qed.

Lemma over_lookup_to_ball_allout :
  forall tbl b, over_lookup_to_ball tbl b 10 = 0.
Proof.
  intros tbl b.
  unfold over_lookup_to_ball.
  rewrite table_allout. lia.
Qed.

Lemma over_lookup_to_ball_no_balls :
  forall tbl w, over_lookup_to_ball tbl 0 w = 0.
Proof.
  intros tbl w.
  unfold over_lookup_to_ball. simpl.
  rewrite table_no_overs. lia.
Qed.

Lemma over_lookup_to_ball_full_odi :
  forall tbl, over_lookup_to_ball tbl 300 0 = 10000.
Proof.
  intros tbl.
  unfold over_lookup_to_ball.
  replace (300 / 6) with 50 by reflexivity.
  rewrite Nat.min_id.
  rewrite table_full_odi. reflexivity.
Qed.

Definition BallTableFromOvers (tbl : ResourceTable) : BallResourceTable := {|
  ball_lookup := over_lookup_to_ball tbl;
  ball_table_mono := over_lookup_to_ball_mono tbl;
  ball_table_wickets_mono := over_lookup_to_ball_wickets_mono tbl;
  ball_table_allout := over_lookup_to_ball_allout tbl;
  ball_table_no_balls := over_lookup_to_ball_no_balls tbl;
  ball_table_full_odi := over_lookup_to_ball_full_odi tbl
|}.

(* Linear interpolation to ball granularity: monotone in balls and at the boundaries unconditionally, antitone in wickets under the concavity assumption below. *)

Lemma interpolate_resource_at_overs_boundary :
  forall tbl o w,
    interpolate_resource tbl (o * 6) w = lookup tbl o w * 1000.
Proof.
  intros tbl o w.
  unfold interpolate_resource.
  rewrite Nat.div_mul by lia.
  rewrite Nat.Div0.mod_mul.
  rewrite Nat.mul_0_l. rewrite Nat.Div0.div_0_l. lia.
Qed.

Lemma interpolate_resource_allout :
  forall tbl b, interpolate_resource tbl b 10 = 0.
Proof.
  intros tbl b. unfold interpolate_resource.
  rewrite (table_allout tbl). rewrite (table_allout tbl).
  change (0 * 1000) with 0.
  change (0 - 0) with 0.
  change (0 * 1000) with 0.
  rewrite Nat.mul_0_r.
  rewrite Nat.Div0.div_0_l. reflexivity.
Qed.

Lemma interpolate_resource_no_balls :
  forall tbl w, interpolate_resource tbl 0 w = lookup tbl 0 w * 1000.
Proof.
  intros tbl w. unfold interpolate_resource.
  simpl. lia.
Qed.

Lemma interpolate_resource_step :
  forall tbl b w,
    interpolate_resource tbl b w <= interpolate_resource tbl (S b) w.
Proof.
  intros tbl b w.
  unfold interpolate_resource.
  remember (b / 6) as o.
  remember (b mod 6) as r.
  assert (Hr: r < 6).
  { subst r. apply Nat.mod_upper_bound. lia. }
  assert (Hbeq: b = 6 * o + r).
  { subst o r. apply Nat.div_mod_eq. }
  destruct (Nat.eq_dec r 5) as [Heq|Hne].
  - rewrite Heq.
    rewrite Heq in Hbeq.
    assert (HSeq: S b = 6 * (S o)) by lia.
    assert (HSb_div: (S b) / 6 = S o).
    { rewrite HSeq. rewrite Nat.mul_comm. apply Nat.div_mul. lia. }
    assert (HSb_mod: (S b) mod 6 = 0).
    { rewrite HSeq. rewrite Nat.mul_comm. apply Nat.Div0.mod_mul. }
    rewrite HSb_div, HSb_mod.
    rewrite Nat.mul_0_l. rewrite Nat.Div0.div_0_l.
    assert (Hmono: lookup tbl o w <= lookup tbl (S o) w).
    { apply table_overs_mono. lia. }
    assert (Hcell: lookup tbl (o + 1) w = lookup tbl (S o) w).
    { f_equal. lia. }
    rewrite Hcell.
    assert (Hbnd: lookup tbl o w * 1000 +
                  5 * ((lookup tbl (S o) w - lookup tbl o w) * 1000) / 6 <=
                  lookup tbl (S o) w * 1000).
    { eapply Nat.le_trans with
        (lookup tbl o w * 1000 + (lookup tbl (S o) w - lookup tbl o w) * 1000).
      - apply Nat.add_le_mono_l.
        apply Nat.Div0.div_le_upper_bound. nia.
      - assert (HA: lookup tbl o w + (lookup tbl (S o) w - lookup tbl o w) = lookup tbl (S o) w) by lia.
        nia. }
    rewrite Nat.add_0_r. exact Hbnd.
  - assert (HSr: r < 5) by lia.
    assert (HSeq: S b = 6 * o + S r) by lia.
    assert (HSb_div: (S b) / 6 = o).
    { rewrite HSeq.
      rewrite Nat.mul_comm.
      rewrite Nat.div_add_l by lia.
      assert (HSr6: S r < 6) by lia.
      rewrite (Nat.div_small (S r) 6 HSr6). lia. }
    assert (HSb_mod: (S b) mod 6 = S r).
    { rewrite HSeq.
      replace (6 * o + S r) with (S r + o * 6) by lia.
      rewrite Nat.Div0.mod_add.
      apply Nat.mod_small. lia. }
    rewrite HSb_div, HSb_mod.
    assert (Hmono: lookup tbl o w <= lookup tbl (o + 1) w).
    { apply table_overs_mono. lia. }
    apply Nat.add_le_mono_l.
    apply Nat.Div0.div_le_mono.
    apply Nat.mul_le_mono_r.
    lia.
Qed.

Lemma interpolate_resource_mono :
  forall tbl b1 b2 w,
    b1 <= b2 ->
    interpolate_resource tbl b1 w <= interpolate_resource tbl b2 w.
Proof.
  intros tbl b1 b2 w Hle.
  induction Hle as [|n Hle IH].
  - lia.
  - eapply Nat.le_trans; [exact IH | apply interpolate_resource_step].
Qed.

(* Wicket antitonicity of interpolation needs the over-derivative nonincreasing in wickets: the DL concavity condition. *)

Definition table_concave_in_wickets (tbl : ResourceTable) : Prop :=
  forall o w1 w2,
    w1 <= w2 ->
    lookup tbl (o + 1) w2 - lookup tbl o w2 <=
    lookup tbl (o + 1) w1 - lookup tbl o w1.

Lemma interpolate_resource_wickets_mono :
  forall tbl,
    table_concave_in_wickets tbl ->
    forall b w1 w2,
    w1 <= w2 ->
    interpolate_resource tbl b w2 <= interpolate_resource tbl b w1.
Proof.
  intros tbl Hconc b w1 w2 Hle.
  unfold interpolate_resource.
  remember (b / 6) as o.
  remember (b mod 6) as r.
  assert (Hf: lookup tbl o w2 <= lookup tbl o w1).
  { apply table_wickets_mono. exact Hle. }
  assert (Hdiff: lookup tbl (o + 1) w2 - lookup tbl o w2 <=
                 lookup tbl (o + 1) w1 - lookup tbl o w1).
  { apply Hconc. exact Hle. }
  assert (Hp1: lookup tbl o w2 * 1000 <= lookup tbl o w1 * 1000) by nia.
  assert (Hp2: r * ((lookup tbl (o + 1) w2 - lookup tbl o w2) * 1000) / 6 <=
               r * ((lookup tbl (o + 1) w1 - lookup tbl o w1) * 1000) / 6).
  { apply Nat.Div0.div_le_mono.
    apply Nat.mul_le_mono_l.
    apply Nat.mul_le_mono_r. exact Hdiff. }
  lia.
Qed.

(* A concave-in-wickets table interpolates to a lawful BallResourceTable. *)

Lemma interpolate_resource_full :
  forall tbl, interpolate_resource tbl 300 0 = 1000 * 1000.
Proof.
  intros tbl.
  replace 300 with (50 * 6) by reflexivity.
  rewrite (interpolate_resource_at_overs_boundary tbl 50 0).
  rewrite table_full_odi. reflexivity.
Qed.

(* Interpolation lands at the 1,000,000 scale; division by 100 reaches the 10,000 scale of BallResourceTable. *)

Definition interpolate_ball_lookup (tbl : ResourceTable) (b : balls) (w : wickets) : scaled_resource :=
  interpolate_resource tbl (Nat.min b 300) w / 100.

Lemma interpolate_ball_lookup_mono :
  forall tbl b1 b2 w,
    b1 <= b2 ->
    interpolate_ball_lookup tbl b1 w <= interpolate_ball_lookup tbl b2 w.
Proof.
  intros tbl b1 b2 w Hle.
  unfold interpolate_ball_lookup.
  apply Nat.Div0.div_le_mono.
  apply interpolate_resource_mono.
  apply Nat.min_le_compat_r. exact Hle.
Qed.

Lemma interpolate_ball_lookup_wickets_mono :
  forall tbl,
    table_concave_in_wickets tbl ->
    forall b w1 w2,
    w1 <= w2 ->
    interpolate_ball_lookup tbl b w2 <= interpolate_ball_lookup tbl b w1.
Proof.
  intros tbl Hconc b w1 w2 Hle.
  unfold interpolate_ball_lookup.
  apply Nat.Div0.div_le_mono.
  apply interpolate_resource_wickets_mono; assumption.
Qed.

Lemma interpolate_ball_lookup_allout :
  forall tbl b, interpolate_ball_lookup tbl b 10 = 0.
Proof.
  intros tbl b. unfold interpolate_ball_lookup.
  rewrite interpolate_resource_allout.
  rewrite Nat.Div0.div_0_l. reflexivity.
Qed.

Lemma interpolate_ball_lookup_no_balls :
  forall tbl w, interpolate_ball_lookup tbl 0 w = 0.
Proof.
  intros tbl w. unfold interpolate_ball_lookup.
  simpl.
  rewrite interpolate_resource_no_balls.
  rewrite table_no_overs.
  simpl. reflexivity.
Qed.

Lemma interpolate_ball_lookup_full_odi :
  forall tbl, interpolate_ball_lookup tbl 300 0 = 10000.
Proof.
  intros tbl. unfold interpolate_ball_lookup.
  replace (Nat.min 300 300) with 300 by (symmetry; apply Nat.min_id).
  rewrite interpolate_resource_full.
  vm_compute. reflexivity.
Qed.

Definition BallTableFromInterpolation
  (tbl : ResourceTable)
  (Hconc : table_concave_in_wickets tbl) : BallResourceTable := {|
  ball_lookup := interpolate_ball_lookup tbl;
  ball_table_mono := interpolate_ball_lookup_mono tbl;
  ball_table_wickets_mono := interpolate_ball_lookup_wickets_mono tbl Hconc;
  ball_table_allout := interpolate_ball_lookup_allout tbl;
  ball_table_no_balls := interpolate_ball_lookup_no_balls tbl;
  ball_table_full_odi := interpolate_ball_lookup_full_odi tbl
|}.

(******************************************************************************)
(*               ICC STANDARD-EDITION CONCRETE TABLE                          *)
(******************************************************************************)

(* Separable synthetic table lookup(u, w) = u_factor(u) * w_factor(w) / 1000, calibrated to the boundary and monotonicity laws with factors approximating the published sheet at over boundaries. *)

Definition icc_w_factor (w : wickets) : nat :=
  match w with
  | 0  => 1000
  | 1  =>  934
  | 2  =>  851
  | 3  =>  749
  | 4  =>  627
  | 5  =>  490
  | 6  =>  349
  | 7  =>  220
  | 8  =>  119
  | 9  =>   47
  | _  =>    0
  end.

Definition icc_u_factor (u : overs) : nat :=
  match u with
  | 0  =>    0
  | 1  =>   36
  | 2  =>   71
  | 3  =>  105
  | 4  =>  138
  | 5  =>  170
  | 6  =>  201
  | 7  =>  231
  | 8  =>  260
  | 9  =>  288
  | 10 => 315
  | 11 => 341
  | 12 => 366
  | 13 => 390
  | 14 => 413
  | 15 => 435
  | 16 => 456
  | 17 => 477
  | 18 => 497
  | 19 => 516
  | 20 => 534
  | 21 => 552
  | 22 => 569
  | 23 => 585
  | 24 => 601
  | 25 => 616
  | 26 => 630
  | 27 => 644
  | 28 => 657
  | 29 => 670
  | 30 => 682
  | 31 => 694
  | 32 => 705
  | 33 => 716
  | 34 => 727
  | 35 => 737
  | 36 => 747
  | 37 => 757
  | 38 => 766
  | 39 => 775
  | 40 => 784
  | 41 => 793
  | 42 => 801
  | 43 => 810
  | 44 => 818
  | 45 => 826
  | 46 => 834
  | 47 => 842
  | 48 => 850
  | 49 => 925
  | _  => 1000  (* u >= 50: full innings *)
  end.

Definition icc_lookup (u : overs) (w : wickets) : resource :=
  if 10 <=? w then 0
  else
    icc_u_factor u * icc_w_factor w / 1000.

Lemma icc_w_factor_zero_at_10 : icc_w_factor 10 = 0.
Proof. reflexivity. Qed.

Lemma icc_u_factor_zero_at_0 : icc_u_factor 0 = 0.
Proof. reflexivity. Qed.

Lemma icc_u_factor_full_at_50 : icc_u_factor 50 = 1000.
Proof. reflexivity. Qed.

Lemma icc_w_factor_step :
  forall w, icc_w_factor (S w) <= icc_w_factor w.
Proof.
  intros w.
  destruct w as [|[|[|[|[|[|[|[|[|[|w']]]]]]]]]]; simpl; lia.
Qed.

Lemma icc_w_factor_mono :
  forall w1 w2, w1 <= w2 -> icc_w_factor w2 <= icc_w_factor w1.
Proof.
  intros w1 w2 Hle.
  induction Hle as [|m Hle IH].
  - lia.
  - eapply Nat.le_trans; [apply icc_w_factor_step | exact IH].
Qed.

Lemma icc_u_factor_step :
  forall u, icc_u_factor u <= icc_u_factor (S u).
Proof.
  intros u.
  do 50 (destruct u as [|u]; [simpl; lia|]).
  simpl. lia.
Qed.

Lemma icc_u_factor_mono :
  forall u1 u2, u1 <= u2 -> icc_u_factor u1 <= icc_u_factor u2.
Proof.
  intros u1 u2 Hle.
  induction Hle as [|m Hle IH].
  - lia.
  - eapply Nat.le_trans; [exact IH | apply icc_u_factor_step].
Qed.

Lemma icc_overs_mono :
  forall u1 u2 w, u1 <= u2 -> icc_lookup u1 w <= icc_lookup u2 w.
Proof.
  intros u1 u2 w Hle.
  unfold icc_lookup.
  destruct (10 <=? w); [lia|].
  apply Nat.Div0.div_le_mono.
  apply Nat.mul_le_mono_r.
  apply icc_u_factor_mono. exact Hle.
Qed.

Lemma icc_wickets_mono :
  forall u w1 w2, w1 <= w2 -> icc_lookup u w2 <= icc_lookup u w1.
Proof.
  intros u w1 w2 Hle.
  unfold icc_lookup.
  destruct (10 <=? w2) eqn:H2.
  - lia.
  - destruct (10 <=? w1) eqn:H1.
    + apply Nat.leb_le in H1. apply Nat.leb_gt in H2. lia.
    + apply Nat.Div0.div_le_mono.
      apply Nat.mul_le_mono_l.
      apply icc_w_factor_mono. exact Hle.
Qed.

Lemma icc_table_allout :
  forall u, icc_lookup u 10 = 0.
Proof.
  intros u. unfold icc_lookup. simpl. reflexivity.
Qed.

Lemma icc_table_no_overs :
  forall w, icc_lookup 0 w = 0.
Proof.
  intros w. unfold icc_lookup.
  destruct (10 <=? w); [reflexivity|].
  simpl. reflexivity.
Qed.

Lemma icc_table_full_odi : icc_lookup 50 0 = 1000.
Proof. reflexivity. Qed.

Definition ICCStandardTable : ResourceTable := {|
  lookup := icc_lookup;
  table_overs_mono := icc_overs_mono;
  table_wickets_mono := icc_wickets_mono;
  table_allout := icc_table_allout;
  table_no_overs := icc_table_no_overs;
  table_full_odi := icc_table_full_odi
|}.

(* The over-floor projection serves the separable model without a concavity certificate. *)

Definition ICCBallTable : BallResourceTable :=
  BallTableFromOvers ICCStandardTable.

(* Sanity check: the table gives sensible values *)
Example icc_table_25_5 : icc_lookup 25 5 = (616 * 490) / 1000.
Proof. reflexivity. Qed.

Example icc_table_50_0 : icc_lookup 50 0 = 1000.
Proof. reflexivity. Qed.

Example icc_table_10_3 : icc_lookup 10 3 < icc_lookup 25 3.
Proof. vm_compute. lia. Qed.

(******************************************************************************)
(*              PUBLISHED DL STANDARD EDITION TABLE (2002)                    *)
(******************************************************************************)

(* The official ball-by-ball Standard Edition table (ECB Duckworth/Lewis/Stern Regulations; ICC Playing Handbook): rows are balls remaining 0-300, columns wickets lost 0-9, percentages scaled by 10 so the printed 0.1% resolution is exact; the record laws are certified by vm_compute over the whole grid. *)

(* The grid is transcribed in binary N so its 3010 literals stay logarithmic as kernel terms and in extraction; lookups convert to nat at the cell level. *)
Local Open Scope N_scope.

Definition dl2002_data : list (list N) := [
  [0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
  [6; 6; 6; 6; 6; 6; 6; 6; 6; 6];
  [12; 12; 12; 12; 12; 12; 12; 12; 12; 11];
  [18; 18; 18; 18; 18; 18; 18; 18; 17; 15];
  [24; 24; 24; 24; 24; 24; 24; 23; 22; 19];
  [30; 30; 30; 30; 30; 30; 29; 29; 27; 22];
  [36; 36; 36; 36; 36; 35; 35; 34; 32; 25];
  [42; 42; 42; 42; 42; 41; 40; 39; 36; 28];
  [48; 48; 48; 48; 47; 47; 46; 44; 40; 30];
  [54; 54; 54; 53; 53; 52; 51; 49; 44; 32];
  [60; 60; 59; 59; 59; 58; 56; 53; 48; 34];
  [66; 65; 65; 65; 64; 63; 61; 58; 51; 36];
  [72; 71; 71; 70; 70; 68; 66; 62; 55; 37];
  [77; 77; 77; 76; 75; 74; 71; 67; 58; 38];
  [83; 83; 82; 82; 80; 79; 76; 71; 61; 39];
  [89; 88; 88; 87; 86; 84; 81; 75; 64; 40];
  [94; 94; 93; 93; 91; 89; 85; 79; 67; 41];
  [100; 100; 99; 98; 96; 94; 90; 83; 69; 42];
  [106; 105; 104; 103; 102; 99; 95; 87; 72; 42];
  [111; 111; 110; 109; 107; 104; 99; 90; 74; 43];
  [117; 116; 115; 114; 112; 109; 103; 94; 77; 43];
  [123; 122; 121; 119; 117; 113; 108; 97; 79; 44];
  [128; 127; 126; 125; 122; 118; 112; 101; 81; 44];
  [134; 133; 132; 130; 127; 123; 116; 104; 83; 45];
  [139; 138; 137; 135; 132; 127; 120; 107; 84; 45];
  [145; 144; 142; 140; 137; 132; 124; 110; 86; 45];
  [150; 149; 147; 145; 142; 136; 128; 113; 88; 45];
  [156; 154; 153; 150; 147; 141; 132; 116; 89; 46];
  [161; 160; 158; 155; 151; 145; 136; 119; 91; 46];
  [166; 165; 163; 160; 156; 150; 139; 122; 92; 46];
  [172; 170; 168; 165; 161; 154; 143; 125; 94; 46];
  [177; 175; 173; 170; 165; 158; 147; 127; 95; 46];
  [182; 181; 178; 175; 170; 162; 150; 130; 96; 46];
  [188; 186; 183; 180; 174; 166; 154; 132; 97; 46];
  [193; 191; 188; 185; 179; 170; 157; 135; 98; 46];
  [198; 196; 193; 189; 183; 174; 160; 137; 100; 46];
  [203; 201; 198; 194; 188; 178; 164; 139; 101; 46];
  [208; 206; 203; 199; 192; 182; 167; 141; 101; 47];
  [214; 211; 208; 203; 197; 186; 170; 144; 102; 47];
  [219; 216; 213; 208; 201; 190; 173; 146; 103; 47];
  [224; 221; 218; 213; 205; 194; 176; 148; 104; 47];
  [229; 226; 223; 217; 209; 198; 179; 150; 105; 47];
  [234; 231; 227; 222; 214; 201; 182; 152; 105; 47];
  [239; 236; 232; 226; 218; 205; 185; 153; 106; 47];
  [244; 241; 237; 231; 222; 209; 188; 155; 107; 47];
  [249; 246; 241; 235; 226; 212; 191; 157; 107; 47];
  [254; 251; 246; 240; 230; 216; 194; 159; 108; 47];
  [259; 256; 251; 244; 234; 219; 196; 160; 109; 47];
  [264; 260; 255; 248; 238; 223; 199; 162; 109; 47];
  [269; 265; 260; 253; 242; 226; 202; 164; 110; 47];
  [274; 270; 264; 257; 246; 229; 204; 165; 110; 47];
  [279; 275; 269; 261; 250; 233; 207; 167; 111; 47];
  [283; 279; 273; 265; 253; 236; 209; 168; 111; 47];
  [288; 284; 278; 269; 257; 239; 212; 170; 111; 47];
  [293; 289; 282; 274; 261; 242; 214; 171; 112; 47];
  [298; 293; 287; 278; 265; 245; 217; 172; 112; 47];
  [303; 298; 291; 282; 268; 249; 219; 174; 113; 47];
  [307; 302; 296; 286; 272; 252; 221; 175; 113; 47];
  [312; 307; 300; 290; 276; 255; 223; 176; 113; 47];
  [317; 311; 304; 294; 279; 258; 226; 177; 114; 47];
  [321; 316; 308; 298; 283; 261; 228; 179; 114; 47];
  [326; 320; 313; 302; 286; 264; 230; 180; 114; 47];
  [331; 325; 317; 306; 290; 266; 232; 181; 114; 47];
  [335; 329; 321; 310; 293; 269; 234; 182; 115; 47];
  [340; 334; 325; 314; 297; 272; 236; 183; 115; 47];
  [344; 338; 329; 317; 300; 275; 238; 184; 115; 47];
  [349; 342; 334; 321; 304; 278; 240; 185; 115; 47];
  [353; 347; 338; 325; 307; 280; 242; 186; 115; 47];
  [358; 351; 342; 329; 310; 283; 244; 187; 116; 47];
  [362; 355; 346; 332; 313; 286; 246; 188; 116; 47];
  [367; 360; 350; 336; 317; 288; 248; 189; 116; 47];
  [371; 364; 354; 340; 320; 291; 249; 189; 116; 47];
  [376; 368; 358; 343; 323; 294; 251; 190; 116; 47];
  [380; 372; 362; 347; 326; 296; 253; 191; 116; 47];
  [385; 377; 366; 351; 329; 299; 255; 192; 117; 47];
  [389; 381; 370; 354; 332; 301; 256; 193; 117; 47];
  [393; 385; 374; 358; 336; 304; 258; 193; 117; 47];
  [398; 389; 377; 361; 339; 306; 259; 194; 117; 47];
  [402; 393; 381; 365; 342; 308; 261; 195; 117; 47];
  [406; 397; 385; 368; 345; 311; 263; 195; 117; 47];
  [410; 401; 389; 372; 348; 313; 264; 196; 117; 47];
  [415; 405; 393; 375; 350; 315; 266; 197; 117; 47];
  [419; 409; 396; 379; 353; 318; 267; 197; 118; 47];
  [423; 413; 400; 382; 356; 320; 269; 198; 118; 47];
  [427; 417; 404; 385; 359; 322; 270; 199; 118; 47];
  [431; 421; 408; 389; 362; 324; 271; 199; 118; 47];
  [435; 425; 411; 392; 365; 326; 273; 200; 118; 47];
  [440; 429; 415; 395; 368; 328; 274; 200; 118; 47];
  [444; 433; 418; 398; 370; 331; 275; 201; 118; 47];
  [448; 437; 422; 402; 373; 333; 277; 201; 118; 47];
  [452; 441; 426; 405; 376; 335; 278; 202; 118; 47];
  [456; 445; 429; 408; 378; 337; 279; 202; 118; 47];
  [460; 448; 433; 411; 381; 339; 281; 203; 118; 47];
  [464; 452; 436; 414; 384; 341; 282; 203; 118; 47];
  [468; 456; 440; 417; 386; 343; 283; 204; 118; 47];
  [472; 460; 443; 420; 389; 345; 284; 204; 118; 47];
  [476; 463; 447; 423; 391; 347; 285; 205; 118; 47];
  [480; 467; 450; 427; 394; 348; 286; 205; 118; 47];
  [484; 471; 454; 430; 396; 350; 288; 205; 119; 47];
  [488; 475; 457; 433; 399; 352; 289; 206; 119; 47];
  [492; 478; 460; 436; 401; 354; 290; 206; 119; 47];
  [495; 482; 464; 438; 404; 356; 291; 207; 119; 47];
  [499; 485; 467; 441; 406; 358; 292; 207; 119; 47];
  [503; 489; 470; 444; 409; 359; 293; 207; 119; 47];
  [507; 493; 474; 447; 411; 361; 294; 208; 119; 47];
  [511; 496; 477; 450; 413; 363; 295; 208; 119; 47];
  [515; 500; 480; 453; 416; 364; 296; 208; 119; 47];
  [518; 503; 483; 456; 418; 366; 297; 209; 119; 47];
  [522; 507; 486; 459; 420; 368; 298; 209; 119; 47];
  [526; 510; 490; 461; 423; 369; 299; 209; 119; 47];
  [529; 514; 493; 464; 425; 371; 300; 210; 119; 47];
  [533; 517; 496; 467; 427; 373; 300; 210; 119; 47];
  [537; 521; 499; 470; 429; 374; 301; 210; 119; 47];
  [541; 524; 502; 472; 432; 376; 302; 210; 119; 47];
  [544; 528; 505; 475; 434; 377; 303; 211; 119; 47];
  [548; 531; 508; 478; 436; 379; 304; 211; 119; 47];
  [551; 534; 511; 480; 438; 380; 305; 211; 119; 47];
  [555; 538; 515; 483; 440; 382; 306; 211; 119; 47];
  [559; 541; 518; 486; 442; 383; 306; 212; 119; 47];
  [562; 544; 521; 488; 444; 385; 307; 212; 119; 47];
  [566; 548; 524; 491; 446; 386; 308; 212; 119; 47];
  [569; 551; 526; 493; 448; 388; 309; 212; 119; 47];
  [573; 554; 529; 496; 450; 389; 309; 212; 119; 47];
  [576; 557; 532; 498; 452; 390; 310; 213; 119; 47];
  [580; 561; 535; 501; 454; 392; 311; 213; 119; 47];
  [583; 564; 538; 503; 456; 393; 311; 213; 119; 47];
  [587; 567; 541; 506; 458; 394; 312; 213; 119; 47];
  [590; 570; 544; 508; 460; 396; 313; 213; 119; 47];
  [593; 573; 547; 511; 462; 397; 314; 214; 119; 47];
  [597; 577; 550; 513; 464; 398; 314; 214; 119; 47];
  [600; 580; 552; 515; 466; 400; 315; 214; 119; 47];
  [604; 583; 555; 518; 468; 401; 315; 214; 119; 47];
  [607; 586; 558; 520; 470; 402; 316; 214; 119; 47];
  [610; 589; 561; 523; 471; 403; 317; 214; 119; 47];
  [614; 592; 563; 525; 473; 404; 317; 215; 119; 47];
  [617; 595; 566; 527; 475; 406; 318; 215; 119; 47];
  [620; 598; 569; 529; 477; 407; 318; 215; 119; 47];
  [624; 601; 572; 532; 479; 408; 319; 215; 119; 47];
  [627; 604; 574; 534; 480; 409; 320; 215; 119; 47];
  [630; 607; 577; 536; 482; 410; 320; 215; 119; 47];
  [633; 610; 580; 538; 484; 411; 321; 215; 119; 47];
  [637; 613; 582; 541; 485; 412; 321; 216; 119; 47];
  [640; 616; 585; 543; 487; 414; 322; 216; 119; 47];
  [643; 619; 587; 545; 489; 415; 322; 216; 119; 47];
  [646; 622; 590; 547; 490; 416; 323; 216; 119; 47];
  [649; 625; 593; 549; 492; 417; 323; 216; 119; 47];
  [652; 628; 595; 552; 494; 418; 324; 216; 119; 47];
  [656; 631; 598; 554; 495; 419; 324; 216; 119; 47];
  [659; 633; 600; 556; 497; 420; 325; 216; 119; 47];
  [662; 636; 603; 558; 498; 421; 325; 216; 119; 47];
  [665; 639; 605; 560; 500; 422; 326; 216; 119; 47];
  [668; 642; 608; 562; 502; 423; 326; 217; 119; 47];
  [671; 645; 610; 564; 503; 424; 326; 217; 119; 47];
  [674; 648; 613; 566; 505; 425; 327; 217; 119; 47];
  [677; 650; 615; 568; 506; 426; 327; 217; 119; 47];
  [680; 653; 617; 570; 508; 427; 328; 217; 119; 47];
  [683; 656; 620; 572; 509; 428; 328; 217; 119; 47];
  [686; 659; 622; 574; 511; 428; 328; 217; 119; 47];
  [689; 661; 625; 576; 512; 429; 329; 217; 119; 47];
  [692; 664; 627; 578; 513; 430; 329; 217; 119; 47];
  [695; 667; 629; 580; 515; 431; 330; 217; 119; 47];
  [698; 669; 632; 582; 516; 432; 330; 217; 119; 47];
  [701; 672; 634; 584; 518; 433; 330; 217; 119; 47];
  [704; 675; 636; 585; 519; 434; 331; 217; 119; 47];
  [707; 677; 639; 587; 520; 434; 331; 218; 119; 47];
  [710; 680; 641; 589; 522; 435; 331; 218; 119; 47];
  [713; 682; 643; 591; 523; 436; 332; 218; 119; 47];
  [715; 685; 645; 593; 524; 437; 332; 218; 119; 47];
  [718; 688; 648; 595; 526; 438; 332; 218; 119; 47];
  [721; 690; 650; 597; 527; 439; 333; 218; 119; 47];
  [724; 693; 652; 598; 528; 439; 333; 218; 119; 47];
  [727; 695; 654; 600; 530; 440; 333; 218; 119; 47];
  [730; 698; 656; 602; 531; 441; 334; 218; 119; 47];
  [732; 700; 659; 604; 532; 442; 334; 218; 119; 47];
  [735; 703; 661; 605; 534; 442; 334; 218; 119; 47];
  [738; 705; 663; 607; 535; 443; 335; 218; 119; 47];
  [741; 708; 665; 609; 536; 444; 335; 218; 119; 47];
  [743; 710; 667; 611; 537; 444; 335; 218; 119; 47];
  [746; 713; 669; 612; 538; 445; 335; 218; 119; 47];
  [749; 715; 671; 614; 540; 446; 336; 218; 119; 47];
  [751; 718; 673; 616; 541; 447; 336; 218; 119; 47];
  [754; 720; 676; 617; 542; 447; 336; 218; 119; 47];
  [757; 722; 678; 619; 543; 448; 336; 218; 119; 47];
  [759; 725; 680; 620; 544; 449; 337; 218; 119; 47];
  [762; 727; 682; 622; 545; 449; 337; 219; 119; 47];
  [765; 729; 684; 624; 547; 450; 337; 219; 119; 47];
  [767; 732; 686; 625; 548; 451; 337; 219; 119; 47];
  [770; 734; 688; 627; 549; 451; 338; 219; 119; 47];
  [773; 736; 690; 628; 550; 452; 338; 219; 119; 47];
  [775; 739; 692; 630; 551; 452; 338; 219; 119; 47];
  [778; 741; 694; 632; 552; 453; 338; 219; 119; 47];
  [780; 743; 696; 633; 553; 454; 339; 219; 119; 47];
  [783; 746; 697; 635; 554; 454; 339; 219; 119; 47];
  [785; 748; 699; 636; 555; 455; 339; 219; 119; 47];
  [788; 750; 701; 638; 556; 455; 339; 219; 119; 47];
  [790; 752; 703; 639; 557; 456; 339; 219; 119; 47];
  [793; 755; 705; 641; 558; 457; 340; 219; 119; 47];
  [795; 757; 707; 642; 559; 457; 340; 219; 119; 47];
  [798; 759; 709; 644; 560; 458; 340; 219; 119; 47];
  [800; 761; 711; 645; 561; 458; 340; 219; 119; 47];
  [803; 763; 713; 646; 562; 459; 340; 219; 119; 47];
  [805; 766; 714; 648; 563; 459; 341; 219; 119; 47];
  [808; 768; 716; 649; 564; 460; 341; 219; 119; 47];
  [810; 770; 718; 651; 565; 460; 341; 219; 119; 47];
  [813; 772; 720; 652; 566; 461; 341; 219; 119; 47];
  [815; 774; 722; 653; 567; 461; 341; 219; 119; 47];
  [817; 776; 723; 655; 568; 462; 342; 219; 119; 47];
  [820; 778; 725; 656; 569; 462; 342; 219; 119; 47];
  [822; 780; 727; 658; 570; 463; 342; 219; 119; 47];
  [825; 783; 729; 659; 571; 463; 342; 219; 119; 47];
  [827; 785; 730; 660; 572; 464; 342; 219; 119; 47];
  [829; 787; 732; 662; 573; 464; 342; 219; 119; 47];
  [832; 789; 734; 663; 574; 465; 342; 219; 119; 47];
  [834; 791; 736; 664; 574; 465; 343; 219; 119; 47];
  [836; 793; 737; 666; 575; 466; 343; 219; 119; 47];
  [838; 795; 739; 667; 576; 466; 343; 219; 119; 47];
  [841; 797; 741; 668; 577; 466; 343; 219; 119; 47];
  [843; 799; 742; 669; 578; 467; 343; 219; 119; 47];
  [845; 801; 744; 671; 579; 467; 343; 219; 119; 47];
  [848; 803; 746; 672; 580; 468; 343; 219; 119; 47];
  [850; 805; 747; 673; 580; 468; 344; 219; 119; 47];
  [852; 807; 749; 674; 581; 469; 344; 219; 119; 47];
  [854; 809; 750; 676; 582; 469; 344; 219; 119; 47];
  [856; 811; 752; 677; 583; 469; 344; 219; 119; 47];
  [859; 813; 754; 678; 584; 470; 344; 219; 119; 47];
  [861; 815; 755; 679; 584; 470; 344; 219; 119; 47];
  [863; 816; 757; 680; 585; 471; 344; 219; 119; 47];
  [865; 818; 758; 682; 586; 471; 344; 219; 119; 47];
  [867; 820; 760; 683; 587; 471; 345; 219; 119; 47];
  [870; 822; 762; 684; 588; 472; 345; 219; 119; 47];
  [872; 824; 763; 685; 588; 472; 345; 219; 119; 47];
  [874; 826; 765; 686; 589; 473; 345; 219; 119; 47];
  [876; 828; 766; 687; 590; 473; 345; 219; 119; 47];
  [878; 830; 768; 689; 590; 473; 345; 219; 119; 47];
  [880; 831; 769; 690; 591; 474; 345; 220; 119; 47];
  [882; 833; 771; 691; 592; 474; 345; 220; 119; 47];
  [884; 835; 772; 692; 593; 474; 345; 220; 119; 47];
  [886; 837; 774; 693; 593; 475; 346; 220; 119; 47];
  [889; 839; 775; 694; 594; 475; 346; 220; 119; 47];
  [891; 840; 777; 695; 595; 475; 346; 220; 119; 47];
  [893; 842; 778; 696; 595; 476; 346; 220; 119; 47];
  [895; 844; 779; 697; 596; 476; 346; 220; 119; 47];
  [897; 846; 781; 698; 597; 476; 346; 220; 119; 47];
  [899; 847; 782; 699; 597; 477; 346; 220; 119; 47];
  [901; 849; 784; 701; 598; 477; 346; 220; 119; 47];
  [903; 851; 785; 702; 599; 477; 346; 220; 119; 47];
  [905; 853; 787; 703; 599; 478; 346; 220; 119; 47];
  [907; 854; 788; 704; 600; 478; 346; 220; 119; 47];
  [909; 856; 789; 705; 601; 478; 347; 220; 119; 47];
  [911; 858; 791; 706; 601; 478; 347; 220; 119; 47];
  [913; 859; 792; 707; 602; 479; 347; 220; 119; 47];
  [915; 861; 793; 708; 603; 479; 347; 220; 119; 47];
  [917; 863; 795; 709; 603; 479; 347; 220; 119; 47];
  [918; 864; 796; 710; 604; 480; 347; 220; 119; 47];
  [920; 866; 797; 711; 604; 480; 347; 220; 119; 47];
  [922; 868; 799; 712; 605; 480; 347; 220; 119; 47];
  [924; 869; 800; 713; 606; 480; 347; 220; 119; 47];
  [926; 871; 801; 713; 606; 481; 347; 220; 119; 47];
  [928; 873; 803; 714; 607; 481; 347; 220; 119; 47];
  [930; 874; 804; 715; 607; 481; 347; 220; 119; 47];
  [932; 876; 805; 716; 608; 481; 347; 220; 119; 47];
  [934; 877; 807; 717; 608; 482; 347; 220; 119; 47];
  [935; 879; 808; 718; 609; 482; 348; 220; 119; 47];
  [937; 881; 809; 719; 610; 482; 348; 220; 119; 47];
  [939; 882; 810; 720; 610; 483; 348; 220; 119; 47];
  [941; 884; 812; 721; 611; 483; 348; 220; 119; 47];
  [943; 885; 813; 722; 611; 483; 348; 220; 119; 47];
  [945; 887; 814; 723; 612; 483; 348; 220; 119; 47];
  [946; 888; 815; 724; 612; 483; 348; 220; 119; 47];
  [948; 890; 817; 724; 613; 484; 348; 220; 119; 47];
  [950; 891; 818; 725; 613; 484; 348; 220; 119; 47];
  [952; 893; 819; 726; 614; 484; 348; 220; 119; 47];
  [954; 894; 820; 727; 614; 484; 348; 220; 119; 47];
  [955; 896; 821; 728; 615; 485; 348; 220; 119; 47];
  [957; 897; 823; 729; 615; 485; 348; 220; 119; 47];
  [959; 899; 824; 730; 616; 485; 348; 220; 119; 47];
  [961; 900; 825; 730; 616; 485; 348; 220; 119; 47];
  [962; 902; 826; 731; 617; 485; 348; 220; 119; 47];
  [964; 903; 827; 732; 617; 486; 348; 220; 119; 47];
  [966; 905; 828; 733; 618; 486; 348; 220; 119; 47];
  [967; 906; 829; 734; 618; 486; 349; 220; 119; 47];
  [969; 908; 831; 734; 619; 486; 349; 220; 119; 47];
  [971; 909; 832; 735; 619; 486; 349; 220; 119; 47];
  [973; 910; 833; 736; 620; 487; 349; 220; 119; 47];
  [974; 912; 834; 737; 620; 487; 349; 220; 119; 47];
  [976; 913; 835; 738; 621; 487; 349; 220; 119; 47];
  [978; 915; 836; 738; 621; 487; 349; 220; 119; 47];
  [979; 916; 837; 739; 622; 487; 349; 220; 119; 47];
  [981; 917; 838; 740; 622; 488; 349; 220; 119; 47];
  [982; 919; 839; 741; 622; 488; 349; 220; 119; 47];
  [984; 920; 840; 741; 623; 488; 349; 220; 119; 47];
  [986; 922; 842; 742; 623; 488; 349; 220; 119; 47];
  [987; 923; 843; 743; 624; 488; 349; 220; 119; 47];
  [989; 924; 844; 744; 624; 489; 349; 220; 119; 47];
  [991; 926; 845; 744; 625; 489; 349; 220; 119; 47];
  [992; 927; 846; 745; 625; 489; 349; 220; 119; 47];
  [994; 928; 847; 746; 625; 489; 349; 220; 119; 47];
  [995; 930; 848; 746; 626; 489; 349; 220; 119; 47];
  [997; 931; 849; 747; 626; 489; 349; 220; 119; 47];
  [998; 932; 850; 748; 627; 490; 349; 220; 119; 47];
  [1000; 934; 851; 749; 627; 490; 349; 220; 119; 47]
].

Local Close Scope N_scope.

Definition dl2002_cell (b : balls) (w : wickets) : resource :=
  N.to_nat (nth w (nth (Nat.min b 300) dl2002_data []) 0%N).

(* Boolean certificates over the whole grid, discharged by vm_compute. *)

Definition dl2002_shape_ok : bool :=
  (length dl2002_data =? 301) &&
  forallb (fun r => length r =? 10) dl2002_data.

Definition dl2002_balls_mono_ok : bool :=
  forallb (fun b => forallb (fun w => dl2002_cell b w <=? dl2002_cell (S b) w)
                            (seq 0 10))
          (seq 0 300).

Definition dl2002_wickets_mono_ok : bool :=
  forallb (fun b => forallb (fun w => dl2002_cell b (S w) <=? dl2002_cell b w)
                            (seq 0 9))
          (seq 0 301).

Lemma dl2002_shape_true : dl2002_shape_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dl2002_balls_mono_true : dl2002_balls_mono_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dl2002_wickets_mono_true : dl2002_wickets_mono_ok = true.
Proof. vm_compute. reflexivity. Qed.

(* Transcription tripwire: the sum of all 3010 cells. *)
Example dl2002_checksum :
  fold_right N.add 0%N
    (map (fun r => fold_right N.add 0%N r) dl2002_data) = 1108540%N.
Proof. vm_compute. reflexivity. Qed.

(* Reflection bridges from the boolean certificates to the record laws. *)

Lemma dl2002_length : length dl2002_data = 301.
Proof.
  assert (H := dl2002_shape_true).
  unfold dl2002_shape_ok in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply Nat.eqb_eq in H. exact H.
Qed.

Lemma dl2002_row_length :
  forall i, i < 301 -> length (nth i dl2002_data []) = 10.
Proof.
  intros i Hi.
  assert (H := dl2002_shape_true).
  unfold dl2002_shape_ok in H.
  apply andb_true_iff in H. destruct H as [_ H].
  rewrite forallb_forall in H.
  apply Nat.eqb_eq.
  apply H.
  apply nth_In.
  rewrite dl2002_length. exact Hi.
Qed.

Lemma dl2002_cell_high_wickets :
  forall b w, 10 <= w -> dl2002_cell b w = 0.
Proof.
  intros b w Hw.
  unfold dl2002_cell.
  rewrite nth_overflow.
  - reflexivity.
  - rewrite dl2002_row_length.
    + exact Hw.
    + lia.
Qed.

Lemma dl2002_cell_no_balls : forall w, dl2002_cell 0 w = 0.
Proof.
  intros w.
  unfold dl2002_cell.
  destruct w as [|[|[|[|[|[|[|[|[|[|w]]]]]]]]]]; try reflexivity.
  rewrite nth_overflow.
  - reflexivity.
  - simpl. lia.
Qed.

Lemma dl2002_cell_step_b :
  forall b w, dl2002_cell b w <= dl2002_cell (S b) w.
Proof.
  intros b w.
  destruct (le_lt_dec 10 w) as [Hw|Hw].
  { rewrite (dl2002_cell_high_wickets b w Hw).
    rewrite (dl2002_cell_high_wickets (S b) w Hw).
    lia. }
  destruct (le_lt_dec 300 b) as [Hb|Hb].
  { unfold dl2002_cell.
    replace (Nat.min b 300) with 300 by lia.
    replace (Nat.min (S b) 300) with 300 by lia.
    lia. }
  assert (H := dl2002_balls_mono_true).
  unfold dl2002_balls_mono_ok in H.
  rewrite forallb_forall in H.
  specialize (H b).
  assert (Hin : In b (seq 0 300)) by (apply in_seq; lia).
  specialize (H Hin).
  rewrite forallb_forall in H.
  specialize (H w).
  assert (Hin2 : In w (seq 0 10)) by (apply in_seq; lia).
  specialize (H Hin2).
  apply Nat.leb_le in H. exact H.
Qed.

Lemma dl2002_cell_mono_b :
  forall b1 b2 w, b1 <= b2 -> dl2002_cell b1 w <= dl2002_cell b2 w.
Proof.
  intros b1 b2 w Hle.
  induction Hle as [|m Hle IH].
  - lia.
  - eapply Nat.le_trans; [exact IH | apply dl2002_cell_step_b].
Qed.

Lemma dl2002_cell_step_w :
  forall b w, dl2002_cell b (S w) <= dl2002_cell b w.
Proof.
  intros b w.
  destruct (le_lt_dec 9 w) as [Hw|Hw].
  { rewrite (dl2002_cell_high_wickets b (S w)) by lia. lia. }
  assert (H := dl2002_wickets_mono_true).
  unfold dl2002_wickets_mono_ok in H.
  rewrite forallb_forall in H.
  specialize (H (Nat.min b 300)).
  assert (Hin : In (Nat.min b 300) (seq 0 301)) by (apply in_seq; lia).
  specialize (H Hin).
  rewrite forallb_forall in H.
  specialize (H w).
  assert (Hin2 : In w (seq 0 9)) by (apply in_seq; lia).
  specialize (H Hin2).
  apply Nat.leb_le in H.
  unfold dl2002_cell in H |- *.
  replace (Nat.min (Nat.min b 300) 300) with (Nat.min b 300) in H by lia.
  exact H.
Qed.

Lemma dl2002_cell_mono_w :
  forall b w1 w2, w1 <= w2 -> dl2002_cell b w2 <= dl2002_cell b w1.
Proof.
  intros b w1 w2 Hle.
  induction Hle as [|m Hle IH].
  - lia.
  - eapply Nat.le_trans; [apply dl2002_cell_step_w | exact IH].
Qed.

(* The published per-ball table as a lawful BallResourceTable at the 10000 = 100.0% scale. *)

Definition dl_std_ball_lookup (b : balls) (w : wickets) : scaled_resource :=
  dl2002_cell b w * 10.

Lemma dl_std_ball_mono :
  forall b1 b2 w, b1 <= b2 ->
    dl_std_ball_lookup b1 w <= dl_std_ball_lookup b2 w.
Proof.
  intros. unfold dl_std_ball_lookup.
  apply Nat.mul_le_mono_r, dl2002_cell_mono_b. assumption.
Qed.

Lemma dl_std_ball_wickets_mono :
  forall b w1 w2, w1 <= w2 ->
    dl_std_ball_lookup b w2 <= dl_std_ball_lookup b w1.
Proof.
  intros. unfold dl_std_ball_lookup.
  apply Nat.mul_le_mono_r, dl2002_cell_mono_w. assumption.
Qed.

Lemma dl_std_ball_allout : forall b, dl_std_ball_lookup b 10 = 0.
Proof.
  intros b. unfold dl_std_ball_lookup.
  rewrite dl2002_cell_high_wickets by lia. reflexivity.
Qed.

Lemma dl_std_ball_no_balls : forall w, dl_std_ball_lookup 0 w = 0.
Proof.
  intros w. unfold dl_std_ball_lookup.
  rewrite dl2002_cell_no_balls. reflexivity.
Qed.

Lemma dl_std_ball_full_odi : dl_std_ball_lookup 300 0 = 10000.
Proof. vm_compute. reflexivity. Qed.

Definition DLStandardBallTable : BallResourceTable := {|
  ball_lookup := dl_std_ball_lookup;
  ball_table_mono := dl_std_ball_mono;
  ball_table_wickets_mono := dl_std_ball_wickets_mono;
  ball_table_allout := dl_std_ball_allout;
  ball_table_no_balls := dl_std_ball_no_balls;
  ball_table_full_odi := dl_std_ball_full_odi
|}.

(* The published per-over sheet is the over-boundary restriction of the per-ball data. *)

Definition dl_std_over_lookup (u : overs) (w : wickets) : resource :=
  dl2002_cell (u * 6) w.

Lemma dl_std_over_mono :
  forall u1 u2 w, u1 <= u2 ->
    dl_std_over_lookup u1 w <= dl_std_over_lookup u2 w.
Proof.
  intros. unfold dl_std_over_lookup.
  apply dl2002_cell_mono_b. lia.
Qed.

Lemma dl_std_over_wickets_mono :
  forall u w1 w2, w1 <= w2 ->
    dl_std_over_lookup u w2 <= dl_std_over_lookup u w1.
Proof.
  intros. unfold dl_std_over_lookup.
  apply dl2002_cell_mono_w. assumption.
Qed.

Lemma dl_std_over_allout : forall u, dl_std_over_lookup u 10 = 0.
Proof.
  intros u. unfold dl_std_over_lookup.
  apply dl2002_cell_high_wickets. lia.
Qed.

Lemma dl_std_over_no_overs : forall w, dl_std_over_lookup 0 w = 0.
Proof.
  intros w. unfold dl_std_over_lookup.
  apply dl2002_cell_no_balls.
Qed.

Lemma dl_std_over_full_odi : dl_std_over_lookup 50 0 = 1000.
Proof. vm_compute. reflexivity. Qed.

Definition DLStandardTable : ResourceTable := {|
  lookup := dl_std_over_lookup;
  table_overs_mono := dl_std_over_mono;
  table_wickets_mono := dl_std_over_wickets_mono;
  table_allout := dl_std_over_allout;
  table_no_overs := dl_std_over_no_overs;
  table_full_odi := dl_std_over_full_odi
|}.

(* Over-floor ball table from the published over sheet; DLStandardBallTable is the faithful one. *)
Definition DLStandardOverFloorBallTable : BallResourceTable :=
  BallTableFromOvers DLStandardTable.

(* Fidelity anchors against the published sheet. *)

Example dl_std_45_overs : lookup DLStandardTable 45 0 = 950.
Proof. vm_compute. reflexivity. Qed.

Example dl_std_40_overs : lookup DLStandardTable 40 0 = 893.
Proof. vm_compute. reflexivity. Qed.

Example dl_std_30_overs_5_wkts : lookup DLStandardTable 30 5 = 447.
Proof. vm_compute. reflexivity. Qed.

Example dl_std_20_overs_2_wkts : lookup DLStandardTable 20 2 = 524.
Proof. vm_compute. reflexivity. Qed.

Example dl_std_10_overs_7_wkts : lookup DLStandardTable 10 7 = 179.
Proof. vm_compute. reflexivity. Qed.

Example dl_std_ball_13_6 : ball_lookup DLStandardBallTable 13 6 = 710.
Proof. vm_compute. reflexivity. Qed.

Example dl_std_ball_1_6 : ball_lookup DLStandardBallTable 1 6 = 60.
Proof. vm_compute. reflexivity. Qed.

(* Clause 5.6 with R2 > R1 on published values: Team 1 on 250 loses its last 20 overs at 2 wickets (R1 = 100.0% - 52.4% = 47.6%), Team 2 receives 30 overs (R2 = 75.1%), extra runs floor(245 * 27.5 / 100) = 67, target 318. *)
Example method2_regulation_arithmetic :
  revised_target 250
    (effective_resources DLStandardTable
       (resources_at_start DLStandardTable 50)
       [ {| int_at_overs := 20; int_at_wickets := 2;
            int_overs_lost := 20; int_during_innings := 1 |} ])
    (resources_at_start DLStandardTable 30) 245 = 318.
Proof. vm_compute. reflexivity. Qed.

(* The published over sheet fails wicket-concavity (w = 7 steps 219 -> 220 across overs 38 -> 39 while w = 6 is flat at 345), so interpolation cannot serve it and the per-ball table is transcribed directly. *)
Example dl_standard_not_concave_in_wickets :
  ~ table_concave_in_wickets DLStandardTable.
Proof.
  intro H.
  assert (Hc := H 38 6 7 ltac:(lia)).
  vm_compute in Hc.
  lia.
Qed.

(******************************************************************************)
(*               SECTION/VARIABLE REFACTOR DEMONSTRATION                       *)
(******************************************************************************)

(* Section/Variable pattern: theorems against a fixed table without threading the parameter through each signature. *)

Section WithTable.
  Variable tbl : ResourceTable.

  Definition s_resources_avail (inn : InningsState) : resource :=
    lookup tbl (overs_remaining inn) (inn_wickets inn).

  Definition s_resources_start (allocated : overs) : resource :=
    lookup tbl allocated 0.

  Lemma s_resources_avail_le_start :
    forall inn,
      inn_wickets inn = 0 ->
      inn_overs_faced inn <= inn_overs_allocated inn ->
      s_resources_avail inn <= s_resources_start (inn_overs_allocated inn).
  Proof.
    intros inn Hw Hov.
    unfold s_resources_avail, s_resources_start.
    rewrite Hw. apply table_overs_mono.
    unfold overs_remaining. lia.
  Qed.

  Lemma s_resources_avail_mono_in_overs :
    forall inn1 inn2,
      inn_wickets inn1 = inn_wickets inn2 ->
      overs_remaining inn1 <= overs_remaining inn2 ->
      s_resources_avail inn1 <= s_resources_avail inn2.
  Proof.
    intros inn1 inn2 Hwq Hov.
    unfold s_resources_avail. rewrite Hwq.
    apply table_overs_mono. exact Hov.
  Qed.

  Lemma s_resources_avail_mono_in_wickets :
    forall inn1 inn2,
      overs_remaining inn1 = overs_remaining inn2 ->
      inn_wickets inn1 <= inn_wickets inn2 ->
      s_resources_avail inn2 <= s_resources_avail inn1.
  Proof.
    intros inn1 inn2 Hov Hw.
    unfold s_resources_avail. rewrite Hov.
    apply table_wickets_mono. exact Hw.
  Qed.

  Lemma s_completed_innings_no_resources :
    forall inn,
      inn_wickets inn = 10 ->
      s_resources_avail inn = 0.
  Proof.
    intros inn H. unfold s_resources_avail.
    rewrite H. apply table_allout.
  Qed.

End WithTable.

(* After ending the section, tbl is generalized into each lemma. *)
Example s_resources_avail_generalized :
  forall (tbl : ResourceTable) (inn : InningsState),
    s_resources_avail tbl inn = lookup tbl (overs_remaining inn) (inn_wickets inn).
Proof. reflexivity. Qed.

Example s_resources_avail_mono_generalized :
  forall (tbl : ResourceTable) (inn1 inn2 : InningsState),
    inn_wickets inn1 = inn_wickets inn2 ->
    overs_remaining inn1 <= overs_remaining inn2 ->
    s_resources_avail tbl inn1 <= s_resources_avail tbl inn2
  := s_resources_avail_mono_in_overs.

(******************************************************************************)
(*               STERN PROFESSIONAL EDITION                                    *)
(******************************************************************************)

(* Synthetic stand-in for the proprietary, unpublished Professional Edition high-score correction: qualitative only, excluded from the extraction surface, no fidelity claim beyond the theorems below. *)

Definition stern_high_score_threshold : nat := 350.

Definition stern_adjustment_factor (t1_score : runs) : nat :=
  if t1_score <? stern_high_score_threshold then 100
  else 100 + (t1_score - stern_high_score_threshold) / 4.

Definition revised_target_stern
  (t1_score : runs) (R1 R2 : resource) (g50 : nat) : runs :=
  if R2 <? R1 then
    revised_target_method1 t1_score R1 R2
  else
    let adj := stern_adjustment_factor t1_score in
    t1_score + (g50 * (R2 - R1) * adj) / 100000 + 1.

(* When score is below threshold, Stern reduces to standard DL *)
Theorem stern_equals_standard_below_threshold :
  forall t1_score R1 R2 g50,
    t1_score < stern_high_score_threshold ->
    revised_target_stern t1_score R1 R2 g50 =
    if R2 <? R1 then revised_target_method1 t1_score R1 R2
    else t1_score + (g50 * (R2 - R1) * 100) / 100000 + 1.
Proof.
  intros t1_score R1 R2 g50 H.
  unfold revised_target_stern, stern_adjustment_factor.
  destruct (R2 <? R1) eqn:E1.
  - reflexivity.
  - apply Nat.ltb_lt in H. rewrite H. reflexivity.
Qed.

Theorem stern_above_threshold_adjustment :
  forall t1_score R1 R2 g50,
    t1_score >= stern_high_score_threshold ->
    R2 >= R1 ->
    revised_target_stern t1_score R1 R2 g50 =
    t1_score + (g50 * (R2 - R1) *
                  (100 + (t1_score - stern_high_score_threshold) / 4)) / 100000 + 1.
Proof.
  intros t1_score R1 R2 g50 Hs HR.
  unfold revised_target_stern, stern_adjustment_factor.
  apply Nat.ltb_ge in HR. rewrite HR.
  apply Nat.ltb_ge in Hs. rewrite Hs. reflexivity.
Qed.

Theorem stern_target_positive :
  forall t1_score R1 R2 g50,
    R1 > 0 ->
    revised_target_stern t1_score R1 R2 g50 >= 1.
Proof.
  intros. unfold revised_target_stern.
  destruct (R2 <? R1) eqn:E.
  - unfold revised_target_method1. lia.
  - lia.
Qed.

Theorem stern_adjustment_monotone :
  forall s1 s2,
    s1 <= s2 -> stern_adjustment_factor s1 <= stern_adjustment_factor s2.
Proof.
  intros s1 s2 Hle.
  unfold stern_adjustment_factor.
  destruct (s1 <? stern_high_score_threshold) eqn:E1;
  destruct (s2 <? stern_high_score_threshold) eqn:E2.
  - lia.
  - assert (Hpos: 0 <= (s2 - stern_high_score_threshold) / 4) by lia.
    lia.
  - apply Nat.ltb_ge in E1. apply Nat.ltb_lt in E2. lia.
  - apply Nat.add_le_mono_l.
    apply Nat.Div0.div_le_mono.
    apply Nat.ltb_ge in E1. lia.
Qed.

Theorem stern_below_threshold_floor :
  forall s, s < stern_high_score_threshold -> stern_adjustment_factor s = 100.
Proof.
  intros s Hs. unfold stern_adjustment_factor.
  apply Nat.ltb_lt in Hs. rewrite Hs. reflexivity.
Qed.

(* Stern target is monotone in R2 *)
Theorem stern_target_monotone_in_R2 :
  forall t1_score R1 R2a R2b g50,
    R1 > 0 -> R2a <= R2b ->
    revised_target_stern t1_score R1 R2a g50 <=
    revised_target_stern t1_score R1 R2b g50.
Proof.
  intros t1_score R1 R2a R2b g50 HR1 Hle.
  unfold revised_target_stern.
  destruct (R2a <? R1) eqn:Ea; destruct (R2b <? R1) eqn:Eb.
  - unfold revised_target_method1.
    apply Nat.add_le_mono_r.
    apply Nat.Div0.div_le_mono.
    apply Nat.mul_le_mono_l. exact Hle.
  - apply Nat.ltb_lt in Ea. apply Nat.ltb_ge in Eb.
    unfold revised_target_method1.
    assert (t1_score * R2a / R1 <= t1_score).
    { apply Nat.Div0.div_le_upper_bound. nia. }
    lia.
  - apply Nat.ltb_ge in Ea. apply Nat.ltb_lt in Eb. lia.
  - apply Nat.add_le_mono_r.
    apply Nat.add_le_mono_l.
    apply Nat.Div0.div_le_mono.
    apply Nat.ltb_ge in Ea, Eb.
    nia.
Qed.

(******************************************************************************)
(*               ANALYTIC REAL-VALUED DL FORMULA                              *)
(******************************************************************************)

(* The published DL formula is real-valued; a separate module proves its monotonicity symbolically. *)

End DLS.

(* Real-valued analytic DL model in a separate module *)
From Stdlib Require Import Reals.
From Stdlib Require Import Lra.

Open Scope R_scope.

Module DLS_Real.

(* R(u, w) = Z0(w) * (1 - exp(-b(w) * u)) with asymptote Z0 and decay rate b. *)

Definition Z0_real (w : nat) : R :=
  match w with
  | 0%nat => 100
  | 1%nat => 93.4
  | 2%nat => 85.1
  | 3%nat => 74.9
  | 4%nat => 62.7
  | 5%nat => 49.0
  | 6%nat => 34.9
  | 7%nat => 22.0
  | 8%nat => 11.9
  | 9%nat => 4.7
  | _ => 0
  end.

Definition b_real (w : nat) : R :=
  match w with
  | 0%nat => 0.0349
  | 1%nat => 0.0383
  | 2%nat => 0.0428
  | 3%nat => 0.0489
  | 4%nat => 0.0574
  | 5%nat => 0.0708
  | 6%nat => 0.0936
  | 7%nat => 0.1382
  | 8%nat => 0.2483
  | 9%nat => 0.5701
  | _ => 1
  end.

Definition dl_resource (u : R) (w : nat) : R :=
  Z0_real w * (1 - exp (- b_real w * u)).

Lemma Z0_real_nonneg : forall w, (Z0_real w >= 0)%R.
Proof.
  intros w. destruct w as [|[|[|[|[|[|[|[|[|[|n]]]]]]]]]];
  simpl; lra.
Qed.

Lemma Z0_real_w0 : Z0_real 0 = 100.
Proof. reflexivity. Qed.

Lemma Z0_real_w10 : forall w, (10 <= w)%nat -> Z0_real w = 0.
Proof.
  intros w Hw.
  do 10 (destruct w as [|w]; [lia|]).
  reflexivity.
Qed.

Lemma b_real_pos : forall w, (w < 10)%nat -> (b_real w > 0)%R.
Proof.
  intros w Hw. destruct w as [|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]; simpl; lra.
Qed.

Lemma dl_resource_at_zero : forall w, dl_resource 0 w = 0.
Proof.
  intros w. unfold dl_resource.
  replace (- b_real w * 0) with 0 by ring.
  rewrite exp_0. ring.
Qed.

Lemma exp_neg_decreasing :
  forall x y, x <= y -> exp (-y) <= exp (-x).
Proof.
  intros x y Hxy.
  destruct (Rlt_or_le x y) as [Hlt | Hge].
  - apply Rlt_le. apply exp_increasing. lra.
  - assert (Heq: x = y) by lra. rewrite Heq. apply Rle_refl.
Qed.

Lemma dl_resource_monotone_in_u :
  forall u1 u2 w,
    (w < 10)%nat ->
    (0 <= u1)%R -> u1 <= u2 ->
    dl_resource u1 w <= dl_resource u2 w.
Proof.
  intros u1 u2 w Hw Hu1 Hu2.
  unfold dl_resource.
  apply Rmult_le_compat_l.
  - apply Rge_le. apply Z0_real_nonneg.
  - apply Rplus_le_compat_l.
    apply Ropp_le_contravar.
    replace (- b_real w * u2) with (- (b_real w * u2)) by ring.
    replace (- b_real w * u1) with (- (b_real w * u1)) by ring.
    apply exp_neg_decreasing.
    assert (Hb: (b_real w > 0)%R) by (apply b_real_pos; assumption).
    nra.
Qed.

Lemma dl_resource_at_50_w0_lt_100 :
  dl_resource 50 0 < 100.
Proof.
  unfold dl_resource. simpl Z0_real. simpl b_real.
  match goal with
  | |- _ * (_ - exp ?x) < _ =>
    assert (Hpos: 0 < exp x) by apply exp_pos
  end.
  lra.
Qed.

Lemma dl_resource_nonneg :
  forall u w, (0 <= u)%R -> (0 <= dl_resource u w)%R.
Proof.
  intros u w Hu. unfold dl_resource.
  destruct (le_dec 10 w) as [Hge|Hlt].
  - rewrite Z0_real_w10 by lia. lra.
  - apply Rmult_le_pos.
    + apply Rge_le. apply Z0_real_nonneg.
    + apply Rplus_le_reg_r with (exp (- b_real w * u) - 1).
      replace (0 + (exp (- b_real w * u) - 1)) with (exp (- b_real w * u) - 1) by ring.
      replace (1 - exp (- b_real w * u) + (exp (- b_real w * u) - 1)) with 0 by ring.
      assert (Hb: (b_real w >= 0)%R).
      { destruct (Compare_dec.lt_dec w 10) as [Hwlt|Hwge].
        - apply Rgt_ge. apply b_real_pos. lia.
        - exfalso. apply Hlt. lia. }
      assert (Hexp_le: (exp (- b_real w * u) <= 1)%R).
      { rewrite <- exp_0.
        destruct (Rle_lt_dec (- b_real w * u) 0) as [Hle|Hgt].
        - destruct Hle.
          + apply Rlt_le. apply exp_increasing. lra.
          + rewrite <- H. lra.
        - exfalso. nra. }
      lra.
Qed.

End DLS_Real.

Close Scope R_scope.

(******************************************************************************)
(*               KERNEL-TO-EXPONENTIAL BRIDGE                                  *)
(******************************************************************************)

(* The computational rational-decay kernel tracks the exponential-decay law at its own integer parameters: exp_decay_approx lies within a one-unit floor slack of Z0 (1 - exp(-b u / 1000)) minus a Taylor remainder that is stated exactly. *)
Module DLS_Bridge.
Import DLS.

Open Scope R_scope.

Definition z0R (w : wickets) : R := INR (Z0_asymptotic w).

Definition buR (w : wickets) (u : overs) : R := INR (decay_rate_scaled w * u).

(* The exponential law at the kernel's parameters. *)
Definition exponential_ideal (u : overs) (w : wickets) : R :=
  z0R w * (1 - exp (- (buR w u / 1000))).

(* The Taylor remainder separating the rational kernel from the exponential. *)
Definition taylor_gap (u : overs) (w : wickets) : R :=
  z0R w * ((buR w u / 1000) * (buR w u / 1000) / (1 + buR w u / 1000)).

Lemma INR_1000 : INR 1000 = 1000.
Proof. rewrite INR_IZR_INZ. reflexivity. Qed.

Lemma Z0_asymptotic_le_1000 : forall w, (Z0_asymptotic w <= 1000)%nat.
Proof.
  intro w.
  do 10 (destruct w as [|w]; [simpl; lia|]).
  simpl. lia.
Qed.

Lemma one_plus_le_exp : forall x : R, 1 + x <= exp x.
Proof.
  intro x.
  destruct (Req_dec x 0) as [->|Hx].
  - rewrite exp_0. lra.
  - left. apply exp_ineq1. exact Hx.
Qed.

Lemma exp_neg_lower : forall x : R, 1 - x <= exp (- x).
Proof.
  intro x.
  pose proof (one_plus_le_exp (- x)).
  lra.
Qed.

Lemma exp_neg_upper : forall x : R, 0 <= x -> exp (- x) * (1 + x) <= 1.
Proof.
  intros x Hx.
  pose proof (one_plus_le_exp x) as He.
  pose proof (exp_pos x) as Hp.
  rewrite exp_Ropp.
  apply Rmult_le_reg_l with (exp x); [exact Hp|].
  rewrite <- Rmult_assoc, Rinv_r by lra.
  lra.
Qed.

(* INR of a nat quotient, bracketed in multiplied form. *)
Lemma INR_div_bounds :
  forall a b : nat, (b <> 0)%nat ->
    INR b * INR (a / b) <= INR a < INR b * (INR (a / b) + 1).
Proof.
  intros a b Hb.
  pose proof (Nat.div_mod_eq a b) as Heq.
  pose proof (Nat.mod_upper_bound a b Hb) as Hm.
  apply (f_equal INR) in Heq.
  rewrite plus_INR, mult_INR in Heq.
  apply lt_INR in Hm.
  pose proof (pos_INR (a mod b)) as Hm0.
  split; nra.
Qed.

Lemma taylor_gap_nonneg : forall u w, 0 <= taylor_gap u w.
Proof.
  intros u w.
  unfold taylor_gap, z0R, buR, Rdiv.
  assert (HX : 0 <= INR (decay_rate_scaled w * u) * / 1000).
  { apply Rmult_le_pos; [apply pos_INR|].
    left. apply Rinv_0_lt_compat. lra. }
  apply Rmult_le_pos; [apply pos_INR|].
  apply Rmult_le_pos.
  - apply Rmult_le_pos; exact HX.
  - left. apply Rinv_0_lt_compat. lra.
Qed.

(* The kernel is bracketed by the exponential law within the floor slack and the Taylor remainder. *)
Theorem exp_decay_approx_bounds :
  forall u w,
    exponential_ideal u w - 1 - taylor_gap u w <= INR (exp_decay_approx u w) <=
    exponential_ideal u w + 1.
Proof.
  intros u w.
  unfold exponential_ideal, taylor_gap, z0R, buR.
  destruct (Nat.eqb_spec u 0) as [->|Hu].
  - rewrite Nat.mul_0_r.
    assert (Hk : exp_decay_approx 0%nat w = 0%nat).
    { unfold exp_decay_approx. destruct (w =? 10); reflexivity. }
    rewrite Hk.
    change (INR 0) with 0.
    replace (0 / 1000) with 0 by (unfold Rdiv; ring).
    rewrite Ropp_0, exp_0.
    replace (0 * 0 / (1 + 0)) with 0 by (unfold Rdiv; ring).
    pose proof (pos_INR (Z0_asymptotic w)).
    split; nra.
  - assert (Hk : exp_decay_approx u w =
        (Z0_asymptotic w *
         (1000 - 1000 * 1000 / (1000 + decay_rate_scaled w * u)) / 1000)%nat).
    { unfold exp_decay_approx.
      rewrite (proj2 (Nat.eqb_neq u 0) Hu).
      destruct (Nat.eqb_spec w 10) as [->|Hw]; reflexivity. }
    rewrite Hk.
    set (Z := INR (Z0_asymptotic w)) in *.
    set (X := INR (decay_rate_scaled w * u) / 1000) in *.
    set (T := exp (- X)) in *.
    assert (HX0 : 0 <= X).
    { unfold X, Rdiv. apply Rmult_le_pos; [apply pos_INR|].
      left. apply Rinv_0_lt_compat. lra. }
    assert (HZ0 : 0 <= Z) by apply pos_INR.
    assert (HZ1000 : Z <= 1000).
    { unfold Z. rewrite <- INR_1000. apply le_INR. apply Z0_asymptotic_le_1000. }
    assert (HB : INR (decay_rate_scaled w * u) = 1000 * X).
    { unfold X. field. }
    set (d := (1000 + decay_rate_scaled w * u)%nat) in *.
    set (q := ((1000 * 1000) / d)%nat) in *.
    assert (Hd : (d <> 0)%nat) by (unfold d; lia).
    assert (HdR : INR d = 1000 * (1 + X)).
    { unfold d. rewrite plus_INR, INR_1000, HB. ring. }
    assert (Hq1000 : (q <= 1000)%nat).
    { unfold q. apply Nat.Div0.div_le_upper_bound.
      assert (Hd1000 : (1000 <= d)%nat) by (unfold d; lia).
      nia. }
    pose proof (INR_div_bounds (1000 * 1000) d Hd) as Hqb.
    fold q in Hqb.
    rewrite mult_INR, INR_1000, HdR in Hqb.
    set (Q := INR q) in *.
    destruct Hqb as [Hq_lo Hq_hi].
    assert (HQ0 : 0 <= Q) by apply pos_INR.
    set (dec := (1000 - q)%nat) in *.
    assert (HdecR : INR dec = 1000 - Q).
    { unfold dec, Q. rewrite minus_INR by exact Hq1000.
      now rewrite INR_1000. }
    pose proof (INR_div_bounds (Z0_asymptotic w * dec) 1000 ltac:(lia)) as Hkb.
    rewrite mult_INR, INR_1000 in Hkb.
    fold Z in Hkb.
    rewrite HdecR in Hkb.
    destruct Hkb as [Hk_lo Hk_hi].
    assert (HXpos : 0 < 1 + X) by lra.
    set (Sx := / (1 + X)).
    assert (HS1 : Sx * (1 + X) = 1) by (unfold Sx; field; lra).
    assert (HSpos : 0 < Sx) by (unfold Sx; apply Rinv_0_lt_compat; lra).
    assert (HQ_hi : Q <= 1000 * Sx).
    { apply Rmult_le_reg_r with (1 + X); [exact HXpos|]. nra. }
    assert (HQ_lo : 1000 * Sx - 1 < Q).
    { apply Rmult_lt_reg_r with (1 + X); [exact HXpos|]. nra. }
    assert (HT_lo : 1 - X <= T) by (unfold T; apply exp_neg_lower).
    assert (HT_hi : T * (1 + X) <= 1) by (unfold T; apply exp_neg_upper; exact HX0).
    assert (HTS : T <= Sx).
    { apply Rmult_le_reg_r with (1 + X); [exact HXpos|]. nra. }
    assert (Hring : Sx - 1 + X = X * X * Sx).
    { assert (HH : Sx - 1 + X - X * X * Sx = (Sx * (1 + X) - 1) * (1 - X)) by ring.
      rewrite HS1 in HH. lra. }
    assert (Hgap : Z * (X * X / (1 + X)) = Z * X * X * Sx).
    { unfold Sx, Rdiv. ring. }
    rewrite Hgap.
    split.
    + assert (Ha : Q - 1000 * T <= 1000 * (X * X * Sx)).
      { rewrite <- Hring. lra. }
      pose proof (Rmult_le_compat_l Z _ _ HZ0 Ha) as Hmul.
      nra.
    + assert (Hab : 1000 * T - Q <= 1000 * Sx - Q) by lra.
      pose proof (Rmult_le_compat_l Z _ _ HZ0 Hab) as H1.
      assert (Hb0 : 0 <= 1000 * Sx - Q) by lra.
      pose proof (Rmult_le_compat_r (1000 * Sx - Q) Z 1000 Hb0 HZ1000) as H2.
      nra.
Qed.

(* Headline: the kernel tracks the exponential law within one unit plus the Taylor remainder. *)
Theorem exp_decay_approx_tracks_exponential :
  forall u w,
    Rabs (INR (exp_decay_approx u w) - exponential_ideal u w) <=
    1 + taylor_gap u w.
Proof.
  intros u w.
  pose proof (exp_decay_approx_bounds u w) as [Hlo Hhi].
  pose proof (taylor_gap_nonneg u w).
  apply Rabs_le. lra.
Qed.

(* Transport to the normalized table at zero wickets, where the envelope coincides with the raw kernel. *)
Theorem dls_lookup_tracks_exponential_w0 :
  forall u, (u <= 50)%nat ->
    1000 / 702 * (exponential_ideal u 0%nat - 1 - taylor_gap u 0%nat) - 1 <=
    INR (dls_lookup u 0%nat) <=
    1000 / 702 * (exponential_ideal u 0%nat + 1).
Proof.
  intros u Hu.
  assert (Hdef : dls_lookup u 0%nat = ((exp_decay_approx u 0) * 1000 / 702)%nat).
  { unfold dls_lookup. rewrite Nat.min_l by exact Hu. reflexivity. }
  rewrite Hdef.
  pose proof (INR_div_bounds ((exp_decay_approx u 0 * 1000)%nat) 702 ltac:(lia)) as Hb.
  rewrite mult_INR, INR_1000 in Hb.
  replace (INR 702) with 702 in Hb by (rewrite INR_IZR_INZ; reflexivity).
  pose proof (exp_decay_approx_bounds u 0%nat) as [Hlo Hhi].
  pose proof (taylor_gap_nonneg u 0%nat).
  destruct Hb as [Hb_lo Hb_hi].
  split.
  - apply Rmult_le_reg_r with 702; [lra|].
    replace ((1000 / 702 * (exponential_ideal u 0%nat - 1 - taylor_gap u 0%nat) - 1) * 702)
      with (1000 * (exponential_ideal u 0%nat - 1 - taylor_gap u 0%nat) - 702)
      by field.
    nra.
  - apply Rmult_le_reg_r with 702; [lra|].
    replace (1000 / 702 * (exponential_ideal u 0%nat + 1) * 702)
      with (1000 * (exponential_ideal u 0%nat + 1))
      by field.
    nra.
Qed.

Close Scope R_scope.

End DLS_Bridge.

(* Pluggable resource-table interface *)
Module Type DLS_TABLE_SIG.
  Parameter the_table : DLS.ResourceTable.
  Parameter the_g50 : nat.
  Parameter the_g50_positive : the_g50 > 0.
End DLS_TABLE_SIG.

Module DLS_Standard <: DLS_TABLE_SIG.
  Definition the_table : DLS.ResourceTable := DLS.DLStandardTable.
  Definition the_g50 : nat := 245.
  Lemma the_g50_positive : the_g50 > 0.
  Proof. unfold the_g50. lia. Qed.
End DLS_Standard.

Module DLS_Dummy <: DLS_TABLE_SIG.
  Definition the_table : DLS.ResourceTable := DLS.DummyTable.
  Definition the_g50 : nat := 245.
  Lemma the_g50_positive : the_g50 > 0.
  Proof. unfold the_g50. lia. Qed.
End DLS_Dummy.

Module DLS_Functor (P : DLS_TABLE_SIG).
  Import DLS.
  Definition compute_target_param (m : MatchState) : runs :=
    target_from_states P.the_table
      (match_t1 m) (inn_overs_allocated (match_t2 m))
      (match_t1_interruptions m) (match_t2_interruptions m) P.the_g50.

  Definition compute_par_param (m : MatchState) : runs :=
    let R1 := effective_resources P.the_table
                (resources_at_start P.the_table (inn_overs_allocated (match_t1 m)))
                (match_t1_interruptions m) in
    let R2_used := resources_used P.the_table (match_t2 m) in
    par_score (inn_score (match_t1 m)) R1 R2_used P.the_g50.

  Theorem param_target_positive :
    forall t1_score R1 R2,
      R1 > 0 ->
      revised_target t1_score R1 R2 P.the_g50 >= 1.
  Proof. intros. apply target_always_positive. exact H. Qed.
End DLS_Functor.

Module DLS_Standard_Instance := DLS_Functor DLS_Standard.
Module DLS_Dummy_Instance := DLS_Functor DLS_Dummy.

Module DLS_Extras.
Import DLS.

(******************************************************************************)
(*               WORKED EXAMPLE: 1992 SA vs ENG WORLD CUP SEMI-FINAL          *)
(******************************************************************************)

(* Sydney, 22 March 1992: England 252/6 in 45 overs; South Africa 231/6 when rain forfeited 12 of the last 13 balls and Most Productive Overs demanded 21 off the one remaining; the published table gives target 235, four to win, and South Africa finished 232. *)

Definition england_1992 : DetailedInningsState := {|
  det_score := 252;
  det_wickets := 6;
  det_balls_faced := 270;
  det_balls_allocated := 270;
  det_phase := Completed;
  det_powerplay := NoPowerplay;
  det_in_powerplay := false;
  det_powerplay_balls_remaining := 0
|}.

(* Rain at 13 balls remaining, 6 wickets down; 12 balls lost. *)
Definition sa_rain_1992 : BallInterruption := {|
  bint_at_balls := 13;
  bint_at_wickets := 6;
  bint_balls_lost := 12;
  bint_during_innings := 2;
  bint_in_powerplay := false
|}.

(* Both sides were allocated 270 balls: 95.0% of full resources. *)
Example r1_1992 :
  effective_ball_resources DLStandardBallTable
    (ball_resources_at_start DLStandardBallTable 270) [] = 9500.
Proof. vm_compute. reflexivity. Qed.

(* The stoppage read 7.1% remaining and the resumption 0.6%: 6.5% lost. *)
Example resources_lost_1992 :
  ball_resource_lost_by_interruption DLStandardBallTable sa_rain_1992 = 650.
Proof. vm_compute. reflexivity. Qed.

Example r2_1992 :
  effective_ball_resources DLStandardBallTable
    (ball_resources_at_start DLStandardBallTable 270) [sa_rain_1992] = 8850.
Proof. vm_compute. reflexivity. Qed.

(* T = floor(252 * 8850 / 9500) + 1 = 235. *)
Example target_1992 :
  ball_target_from_states DLStandardBallTable
    england_1992 270 [] [sa_rain_1992] 245 = 235.
Proof. vm_compute. reflexivity. Qed.

(* Four to win off the final ball, not twenty-one. *)
Example needed_off_final_ball_1992 :
  ball_target_from_states DLStandardBallTable
    england_1992 270 [] [sa_rain_1992] 245 - 231 = 4.
Proof. vm_compute. reflexivity. Qed.

(* South Africa finished on 232: England win under the revised target. *)
Example result_1992 :
  determine_result
    (ball_target_from_states DLStandardBallTable
       england_1992 270 [] [sa_rain_1992] 245)
    232 true true = Team1Wins.
Proof. vm_compute. reflexivity. Qed.

(******************************************************************************)
(*               OCAML EXTRACTION                                              *)
(******************************************************************************)

End DLS_Extras.

From Stdlib Require Extraction.

Set Extraction Output Directory ".".

Extraction Language OCaml.

Extract Inductive nat => "int" [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].

(* The nat arithmetic notations elaborate to Init.Nat, so the maps anchor there; unqualified names hit dead PeanoNat aliases and extraction falls back to unary-cost recursion. *)
Extract Constant Init.Nat.add => "( + )".
Extract Constant Init.Nat.mul => "( * )".
Extract Constant Init.Nat.sub => "(fun a b -> max 0 (a - b))".
Extract Constant Init.Nat.div => "(fun a b -> if b = 0 then 0 else a / b)".
Extract Constant Init.Nat.modulo => "(fun a b -> if b = 0 then a else a mod b)".
Extract Constant Init.Nat.eqb => "(=)".
Extract Constant Init.Nat.ltb => "(<)".
Extract Constant Init.Nat.leb => "(<=)".
Extract Constant Nat.min => "(fun a b -> if a < b then a else b)".

(* Extraction surface: both formula scales, the match pipeline, the decision functions, and the verified tables. *)
Extraction "dls_extracted.ml"
  DLS.revised_target
  DLS.par_score
  DLS.ball_revised_target
  DLS.ball_par_score
  DLS.ball_target_from_states
  DLS.ball_par_from_states
  DLS.ball_resources_used_net
  DLS.ball_resource_lost_by_interruption
  DLS.effective_ball_resources
  DLS.ball_resources_at_start
  DLS.compute_target
  DLS.compute_par
  DLS.compute_result
  DLS.decide_match
  DLS.determine_result
  DLS.par_result
  DLS.DLStandardBallTable
  DLS.DLStandardTable
  DLS.RationalDecayTable
  DLS.ICCStandardTable
  DLS.DummyTable
  DLS_Extras.england_1992
  DLS_Extras.sa_rain_1992
  DLS.ODI DLS.T20 DLS.TheHundred.

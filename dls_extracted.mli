
val negb : bool -> bool

val fst : ('a1*'a2) -> 'a1



val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

val eqb : int -> int -> bool

val leb : int -> int -> bool

val ltb : int -> int -> bool

val divmod : int -> int -> int -> int -> int*int

val div : int -> int -> int

module Nat :
 sig
  val min : int -> int -> int
 end

val nth : int -> 'a1 list -> 'a1 -> 'a1

module DLS :
 sig
  type overs = int

  type balls = int

  type wickets = int

  type resource = int

  type runs = int

  type scaled_resource = int

  type coq_MatchFormat = { total_overs : overs;
                           total_balls_in_format : balls;
                           max_wickets : wickets;
                           max_powerplay_overs : overs;
                           powerplay_balls : balls;
                           min_overs_for_result : overs;
                           min_balls_for_result : balls }

  val min_overs_for_result : coq_MatchFormat -> overs

  val coq_ODI : coq_MatchFormat

  val coq_T20 : coq_MatchFormat

  val coq_TheHundred : coq_MatchFormat

  type coq_ResourceTable =
    overs -> wickets -> resource
    (* singleton inductive, whose constructor was mkTable *)

  val lookup : coq_ResourceTable -> overs -> wickets -> resource

  type coq_BallResourceTable =
    balls -> wickets -> scaled_resource
    (* singleton inductive, whose constructor was mkBallTable *)

  val ball_lookup :
    coq_BallResourceTable -> balls -> wickets -> scaled_resource

  type coq_InningsPhase =
  | NotStarted
  | InProgress
  | Completed
  | Interrupted
  | InningsAbandoned

  type coq_PowerplayPhase =
  | PP1
  | PP2
  | PP3
  | NoPowerplay

  type coq_InningsState = { inn_score : runs; inn_wickets : wickets;
                            inn_overs_faced : overs; inn_balls_faced : 
                            balls; inn_overs_allocated : overs;
                            inn_balls_allocated : balls;
                            inn_phase : coq_InningsPhase;
                            inn_powerplay : coq_PowerplayPhase }

  val inn_score : coq_InningsState -> runs

  val inn_wickets : coq_InningsState -> wickets

  val inn_overs_faced : coq_InningsState -> overs

  val inn_overs_allocated : coq_InningsState -> overs

  val inn_phase : coq_InningsState -> coq_InningsPhase

  type coq_DetailedInningsState = { det_score : runs; det_wickets : wickets;
                                    det_balls_faced : balls;
                                    det_balls_allocated : balls;
                                    det_phase : coq_InningsPhase;
                                    det_powerplay : coq_PowerplayPhase;
                                    det_in_powerplay : bool;
                                    det_powerplay_balls_remaining : balls }

  val det_score : coq_DetailedInningsState -> runs

  val det_balls_allocated : coq_DetailedInningsState -> balls

  val overs_remaining : coq_InningsState -> overs

  val is_complete : coq_InningsState -> bool

  val resources_available : coq_ResourceTable -> coq_InningsState -> resource

  val resources_used : coq_ResourceTable -> coq_InningsState -> resource

  val resources_at_start : coq_ResourceTable -> overs -> resource

  val ball_resources_at_start :
    coq_BallResourceTable -> balls -> scaled_resource

  type coq_Interruption = { int_at_overs : overs; int_at_wickets : wickets;
                            int_overs_lost : overs; int_during_innings : 
                            int }

  val int_at_overs : coq_Interruption -> overs

  val int_at_wickets : coq_Interruption -> wickets

  val int_overs_lost : coq_Interruption -> overs

  val resource_lost_by_interruption :
    coq_ResourceTable -> coq_Interruption -> resource

  val total_resources_lost :
    coq_ResourceTable -> coq_Interruption list -> resource

  val effective_resources :
    coq_ResourceTable -> resource -> coq_Interruption list -> resource

  type coq_BallInterruption = { bint_at_balls : balls;
                                bint_at_wickets : wickets;
                                bint_balls_lost : balls;
                                bint_during_innings : int;
                                bint_in_powerplay : bool }

  val bint_at_balls : coq_BallInterruption -> balls

  val bint_at_wickets : coq_BallInterruption -> wickets

  val bint_balls_lost : coq_BallInterruption -> balls

  val ball_resource_lost_by_interruption :
    coq_BallResourceTable -> coq_BallInterruption -> scaled_resource

  val total_ball_resources_lost :
    coq_BallResourceTable -> coq_BallInterruption list -> scaled_resource

  val effective_ball_resources :
    coq_BallResourceTable -> scaled_resource -> coq_BallInterruption list ->
    scaled_resource

  val revised_target_method1 : runs -> resource -> resource -> runs

  val revised_target_method2 : runs -> resource -> resource -> int -> runs

  val revised_target : runs -> resource -> resource -> int -> runs

  val par_score : runs -> resource -> resource -> int -> runs

  val target_from_states :
    coq_ResourceTable -> coq_InningsState -> overs -> coq_Interruption list
    -> coq_Interruption list -> int -> runs

  val ball_revised_target :
    runs -> scaled_resource -> scaled_resource -> int -> runs

  val ball_par_score :
    runs -> scaled_resource -> scaled_resource -> int -> runs

  val ball_target_from_states :
    coq_BallResourceTable -> coq_DetailedInningsState -> balls ->
    coq_BallInterruption list -> coq_BallInterruption list -> int -> runs

  type coq_MatchResult =
  | Team1Wins
  | Team2Wins
  | Tie
  | NoResult
  | Abandoned

  val determine_result : runs -> runs -> bool -> bool -> coq_MatchResult

  val par_result : runs -> runs -> bool -> coq_MatchResult

  type coq_MatchState = { match_format : coq_MatchFormat;
                          match_t1 : coq_InningsState;
                          match_t2 : coq_InningsState;
                          match_t1_interruptions : coq_Interruption list;
                          match_t2_interruptions : coq_Interruption list;
                          match_g50 : int }

  val match_format : coq_MatchState -> coq_MatchFormat

  val match_t1 : coq_MatchState -> coq_InningsState

  val match_t2 : coq_MatchState -> coq_InningsState

  val match_t1_interruptions : coq_MatchState -> coq_Interruption list

  val match_t2_interruptions : coq_MatchState -> coq_Interruption list

  val match_g50 : coq_MatchState -> int

  val compute_target : coq_ResourceTable -> coq_MatchState -> runs

  val compute_par : coq_ResourceTable -> coq_MatchState -> runs

  val min_overs_met : coq_MatchState -> bool

  val compute_result : coq_ResourceTable -> coq_MatchState -> coq_MatchResult

  val coq_Z0_asymptotic : wickets -> int

  val decay_rate_scaled : wickets -> int

  val exp_decay_approx : overs -> wickets -> resource

  val rational_capped : overs -> wickets -> resource

  val dls_lookup : overs -> wickets -> resource

  val coq_RationalDecayTable : coq_ResourceTable

  val dummy_lookup : overs -> wickets -> resource

  val coq_DummyTable : coq_ResourceTable

  val ended_by_stoppage : coq_InningsPhase -> bool

  val decide_match : coq_ResourceTable -> coq_MatchState -> coq_MatchResult

  val icc_w_factor : wickets -> int

  val icc_u_factor : overs -> int

  val icc_lookup : overs -> wickets -> resource

  val coq_ICCStandardTable : coq_ResourceTable

  val dl2002_data : int list list

  val dl2002_cell : balls -> wickets -> resource

  val dl_std_ball_lookup : balls -> wickets -> scaled_resource

  val coq_DLStandardBallTable : coq_BallResourceTable

  val dl_std_over_lookup : overs -> wickets -> resource

  val coq_DLStandardTable : coq_ResourceTable
 end

module DLS_Extras :
 sig
  val england_1992 : DLS.coq_DetailedInningsState

  val sa_rain_1992 : DLS.coq_BallInterruption
 end

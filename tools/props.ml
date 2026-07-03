(* The theorems proven in dls.v replayed as property-based tests; rebind Impl to an adapter to test a third-party implementation against the machine-checked semantics. *)

open Dls_extracted

module Impl = struct
  let revised_target = DLS.revised_target
  let par_score = DLS.par_score
  let ball_revised_target = DLS.ball_revised_target
  let ball_par_score = DLS.ball_par_score
  let determine_result = DLS.determine_result
  let ball_lookup = DLS.ball_lookup DLS.coq_DLStandardBallTable
  let over_lookup = DLS.lookup DLS.coq_DLStandardTable
end

let checks = ref 0
let failures = ref 0

let check name cond case =
  incr checks;
  if not cond then begin
    incr failures;
    Printf.printf "FAIL %-32s %s\n" name case
  end

(* Park-Miller generator with Schrage reduction: intermediates stay below 2^31, so runs agree between the native and 32-bit js_of_ocaml builds. *)
let lcg_state = ref 1
let rand k =
  let s = !lcg_state in
  let s' = 16807 * (s mod 127773) - 2836 * (s / 127773) in
  let s' = if s' <= 0 then s' + 2147483647 else s' in
  lcg_state := s';
  s' mod k

let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 20000 in
  lcg_state := (if Array.length Sys.argv > 2 then
                  (let s = int_of_string Sys.argv.(2) mod 2147483647 in
                   if s <= 0 then s + 2147483646 else s)
                else 1);

  for _ = 1 to n do
    let s = rand 500 and g50 = 1 + rand 400 in
    let r1 = 1 + rand 1000 in
    let a = rand 1001 and b = rand 1001 in
    let r2 = min a b and r2' = max a b in
    let case = Printf.sprintf "s=%d g50=%d r1=%d r2=%d r2'=%d" s g50 r1 r2 r2' in

    (* target_always_positive *)
    check "target-positive" (Impl.revised_target s r1 r2 g50 >= 1) case;
    (* equal_resources_fair_target *)
    check "equal-resources-score-plus-one" (Impl.revised_target s r1 r1 g50 = s + 1) case;
    (* target_monotone_in_R2 *)
    check "monotone-in-r2"
      (Impl.revised_target s r1 r2 g50 <= Impl.revised_target s r1 r2' g50) case;
    (* revised_target_method1_bound *)
    if r2 <= r1 then
      check "method1-bounded-by-score-plus-one"
        (Impl.revised_target s r1 r2 g50 <= s + 1) case;
    (* clause 5.5: par is the target formula without the one run added *)
    check "par-is-target-minus-one"
      (Impl.par_score s r1 r2 g50 + 1 = Impl.revised_target s r1 r2 g50) case;
    check "ball-par-is-target-minus-one"
      (Impl.ball_par_score s (10 * r1) (10 * r2) g50 + 1 =
       Impl.ball_revised_target s (10 * r1) (10 * r2) g50) case;
    (* ball_revised_target_agrees / ball_par_score_agrees *)
    check "ball-over-scale-agreement"
      (Impl.ball_revised_target s (10 * r1) (10 * r2) g50 =
       Impl.revised_target s r1 r2 g50) case;
    (* revised_target_method2_mono_in_g50 *)
    if r2' >= r1 then
      check "monotone-in-g50"
        (Impl.revised_target s r1 r2' g50 <= Impl.revised_target s r1 r2' (g50 + rand 100)) case;
    (* completed-chase boundary, regulations clause 2 *)
    let t = 1 + rand 500 and sc = rand 600 in
    let expected =
      if sc >= t then DLS.Team2Wins
      else if sc + 1 = t then DLS.Tie
      else DLS.Team1Wins in
    check "completed-chase-boundary"
      (Impl.determine_result t sc true false true = expected)
      (Printf.sprintf "target=%d score=%d" t sc);
    (* clause 2 exemptions: dismissal and the target decide below the minimum *)
    check "all-out-decides-below-minimum"
      (Impl.determine_result t sc true true false = expected)
      (Printf.sprintf "target=%d score=%d" t sc);
    check "target-reached-wins-below-minimum"
      (sc < t || Impl.determine_result t sc false false false = DLS.Team2Wins)
      (Printf.sprintf "target=%d score=%d" t sc)
  done;

  for _ = 1 to n / 4 do
    (* table laws, sampled beyond the grid edge to cover the clamp *)
    let b1 = rand 321 in
    let b2 = b1 + rand (321 - b1) in
    let w1 = rand 10 in
    let w2 = w1 + rand (10 - w1) in
    let case = Printf.sprintf "b1=%d b2=%d w1=%d w2=%d" b1 b2 w1 w2 in
    check "table-monotone-in-balls" (Impl.ball_lookup b1 w1 <= Impl.ball_lookup b2 w1) case;
    check "table-antitone-in-wickets" (Impl.ball_lookup b1 w2 <= Impl.ball_lookup b1 w1) case;
    check "table-allout-zero" (Impl.ball_lookup b1 10 = 0) case;
    check "table-no-balls-zero" (Impl.ball_lookup 0 w1 = 0) case
  done;

  (* published anchors *)
  check "anchor-270b-0w" (Impl.ball_lookup 270 0 = 9500) "";
  check "anchor-13b-6w" (Impl.ball_lookup 13 6 = 710) "";
  check "anchor-1b-6w" (Impl.ball_lookup 1 6 = 60) "";
  check "anchor-300b-0w" (Impl.ball_lookup 300 0 = 10000) "";
  check "anchor-over-50-0" (Impl.over_lookup 50 0 = 1000) "";
  check "anchor-over-20-2" (Impl.over_lookup 20 2 = 524) "";
  check "anchor-over-30-5" (Impl.over_lookup 30 5 = 447) "";

  (* the 1992 semi-final, end to end *)
  check "replay-1992-target"
    (DLS.ball_target_from_states DLS.coq_DLStandardBallTable DLS_Extras.england_1992
       270 [] [DLS_Extras.sa_rain_1992] 245 = 235) "";

  Printf.printf "%d checks, %d failures\n" !checks !failures;
  exit (if !failures = 0 then 0 else 1)

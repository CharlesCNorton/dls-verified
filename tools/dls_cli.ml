(* Command-line front-end over the extracted verified calculator: every printed number is computed by code extracted from dls.v; this file only parses arguments and formats output. *)

open Dls_extracted

let tbl = DLS.coq_DLStandardBallTable

let usage = "\
dls -- verified Duckworth/Lewis Standard Edition calculator\n\
\n\
Resource model: the published ball-by-ball Standard Edition table,\n\
machine-checked in dls.v (monotone in balls, antitone in wickets,\n\
boundary rows certified; targets and pars proven positive, monotone,\n\
and regulation-faithful). Interruptions are given as AT:W:LOST where\n\
AT is balls remaining when play was suspended, W wickets down at that\n\
moment, LOST the number of balls removed. Elapsed balls include removed\n\
deliveries: after a suspension, T2_FACED and the track count advance\n\
past the LOST balls, so balls remaining always reads the physical\n\
figure and the suspension's resources are netted by the AT:W:LOST\n\
record rather than left in the allocation clock.\n\
\n\
usage:\n\
  dls target S T1_BALLS T2_BALLS [G50] [--t1-int AT:W:LOST]... [--t2-int AT:W:LOST]...\n\
      revised target for Team 2 (clause 5.6)\n\
  dls par S T1_BALLS T2_BALLS T2_FACED T2_WKTS [G50] [--t1-int ...]... [--t2-int ...]...\n\
      par score at the given point of Team 2's innings (clause 5.5)\n\
  dls sheet S T1_BALLS T2_BALLS [G50] [--csv] [--t1-int ...]...\n\
      umpires' par sheet: par at the end of every over x wickets lost\n\
  dls track S T1_BALLS T2_BALLS [G50] [--t1-int ...]... [--t2-int ...]...\n\
      live ball-by-ball par tracking; stdin lines: RUNS ['w'] per legal ball\n\
  dls oracle N [SEED]\n\
      differential-testing corpus: N random cases with reference outputs, JSONL\n\
  dls sensitivity N [SEED]\n\
      target spread of the three lawful tables over N random reduced matches\n\
  dls replay\n\
      certified replays of historical rain-affected matches\n\
G50 defaults to 245 (regulations clause 1.12).\n"

let die msg = prerr_endline msg; exit 2

let int_arg what s =
  try int_of_string s with _ -> die (Printf.sprintf "%s: not a number: %s" what s)

let pct r = Printf.sprintf "%d.%d%%" (r / 100) (r mod 100 / 10)

let show_result = function
  | DLS.Team1Wins -> "Team 1 win"
  | DLS.Team2Wins -> "Team 2 win"
  | DLS.Tie -> "Tie"
  | DLS.NoResult -> "No result"
  | DLS.Abandoned -> "Abandoned"

let mk_innings score wickets faced alloc = {
  DLS.det_score = score; det_wickets = wickets;
  det_balls_faced = faced; det_balls_allocated = alloc;
  det_phase = DLS.InProgress; det_powerplay = DLS.NoPowerplay;
  det_in_powerplay = false; det_powerplay_balls_remaining = 0 }

let parse_int_spec what during s =
  match String.split_on_char ':' s with
  | [a; w; l] ->
      let at = int_arg (what ^ " AT") a
      and wk = int_arg (what ^ " W") w
      and lost = int_arg (what ^ " LOST") l in
      if lost > at then die (Printf.sprintf "%s: LOST %d exceeds AT %d" what lost at);
      if wk > 9 then die (Printf.sprintf "%s: W %d exceeds 9" what wk);
      { DLS.bint_at_balls = at; bint_at_wickets = wk; bint_balls_lost = lost;
        bint_during_innings = during; bint_in_powerplay = false }
  | _ -> die (what ^ ": expected AT:W:LOST")

(* Splits argv rest into positional arguments and interruption/flag lists; suspensions are tagged with their innings. *)
let parse_rest rest =
  let pos = ref [] and t1i = ref [] and t2i = ref [] and csv = ref false in
  let rec go = function
    | [] -> ()
    | "--t1-int" :: v :: r -> t1i := !t1i @ [parse_int_spec "--t1-int" 1 v]; go r
    | "--t2-int" :: v :: r -> t2i := !t2i @ [parse_int_spec "--t2-int" 2 v]; go r
    | "--csv" :: r -> csv := true; go r
    | ("--t1-int" | "--t2-int") :: [] -> die "missing AT:W:LOST after interruption flag"
    | a :: r -> pos := !pos @ [a]; go r
  in
  go rest; (!pos, !t1i, !t2i, !csv)

let resources_line label alloc ints =
  let base = DLS.ball_resources_at_start tbl alloc in
  let eff = DLS.effective_ball_resources tbl base ints in
  Printf.printf "%s: allocation %d balls (%d overs%s), resources %s%s\n"
    label alloc (alloc / 6) (if alloc mod 6 = 0 then "" else Printf.sprintf ".%d" (alloc mod 6))
    (pct eff)
    (if ints = [] then ""
     else Printf.sprintf " (%s at start less %s lost to suspensions)"
            (pct base) (pct (base - eff)));
  eff

let cmd_target pos t1i t2i =
  match pos with
  | [s; b1; b2] | [s; b1; b2; _] ->
      let g50 = (match pos with [_; _; _; g] -> int_arg "G50" g | _ -> 245) in
      let s = int_arg "S" s and b1 = int_arg "T1_BALLS" b1 and b2 = int_arg "T2_BALLS" b2 in
      let r1 = resources_line "Team 1" b1 t1i in
      let r2 = resources_line "Team 2" b2 t2i in
      let t = DLS.ball_target_from_states tbl (mk_innings s 0 b1 b1) b2 t1i t2i g50 in
      Printf.printf "Team 1 scored %d; G50 = %d\n" s g50;
      Printf.printf "Method: %s\n"
        (if r2 < r1 then "R2 < R1, scale down by resource ratio (clause 5.6)"
         else if r2 = r1 then "equal resources, target is score plus one"
         else "R2 > R1, inflate by G50 share of excess resources (clause 5.6)");
      Printf.printf "Revised target: %d (%d to tie)\n" t (t - 1)
  | _ -> die usage

let cmd_par pos t1i t2i =
  match pos with
  | [s; b1; b2; f; w] | [s; b1; b2; f; w; _] ->
      let g50 = (match pos with [_; _; _; _; _; g] -> int_arg "G50" g | _ -> 245) in
      let s = int_arg "S" s and b1 = int_arg "T1_BALLS" b1 and b2 = int_arg "T2_BALLS" b2 in
      let f = int_arg "T2_FACED" f and w = int_arg "T2_WKTS" w in
      if f > b2 then die "T2_FACED exceeds T2_BALLS";
      let _ = resources_line "Team 1" b1 t1i in
      let t2 = mk_innings 0 w f b2 in
      let p = DLS.ball_par_from_states tbl (mk_innings s 0 b1 b1) t2 t1i t2i g50 in
      Printf.printf
        "Par after %d balls, %d wickets down: %d\n\
         If the match ends here: above %d Team 2 win, exactly %d tie, below Team 1 win (clause 5.5).\n"
        f w p p p
  | _ -> die usage

let cmd_sheet pos t1i csv =
  match pos with
  | [s; b1; b2] | [s; b1; b2; _] ->
      let g50 = (match pos with [_; _; _; g] -> int_arg "G50" g | _ -> 245) in
      let s = int_arg "S" s and b1 = int_arg "T1_BALLS" b1 and b2 = int_arg "T2_BALLS" b2 in
      let t = DLS.ball_target_from_states tbl (mk_innings s 0 b1 b1) b2 t1i [] g50 in
      let par faced w =
        DLS.ball_par_from_states tbl (mk_innings s 0 b1 b1) (mk_innings 0 w faced b2) t1i [] g50 in
      if csv then begin
        Printf.printf "# verified DLS Standard Edition par sheet; S=%d T1_BALLS=%d T2_BALLS=%d G50=%d target=%d\n"
          s b1 b2 g50 t;
        print_string "overs";
        for w = 0 to 9 do Printf.printf ",w%d" w done; print_newline ();
        for o = 1 to b2 / 6 do
          Printf.printf "%d" o;
          for w = 0 to 9 do Printf.printf ",%d" (par (6 * o) w) done;
          print_newline ()
        done
      end else begin
        Printf.printf "Verified DLS Standard Edition par sheet\n";
        Printf.printf "Team 1 %d in %d balls; Team 2 allocated %d balls; G50 = %d\n" s b1 b2 g50;
        Printf.printf "Revised target (full allocation): %d\n" t;
        Printf.printf "Par at the end of each over (Team 2 ahead if strictly above par):\n\n";
        Printf.printf "        wickets lost\n";
        Printf.printf "overs ";
        for w = 0 to 9 do Printf.printf "%5d" w done; print_newline ();
        for o = 1 to b2 / 6 do
          Printf.printf "%5d " o;
          for w = 0 to 9 do Printf.printf "%5d" (par (6 * o) w) done;
          print_newline ()
        done;
        Printf.printf "\nRegenerate after any suspension: pass the revised allocation and\n";
        Printf.printf "the recorded interruptions to reflect the new state of the chase.\n"
      end
  | _ -> die usage

let cmd_track pos t1i t2i =
  match pos with
  | [s; b1; b2] | [s; b1; b2; _] ->
      let g50 = (match pos with [_; _; _; g] -> int_arg "G50" g | _ -> 245) in
      let s = int_arg "S" s and b1 = int_arg "T1_BALLS" b1 and b2 = int_arg "T2_BALLS" b2 in
      let t1 = mk_innings s 0 b1 b1 in
      let t = DLS.ball_target_from_states tbl t1 b2 t1i t2i g50 in
      Printf.printf "Chasing %d off %d balls (par shown after every legal delivery; input RUNS ['w'])\n" t b2;
      let score = ref 0 and wkts = ref 0 and faced = ref 0 in
      (try
        while !faced < b2 && !wkts < 10 do
          let line = String.trim (input_line stdin) in
          if line <> "" then begin
            let wicket = String.length line > 0 && line.[String.length line - 1] = 'w' in
            let runs_str = if wicket then String.sub line 0 (String.length line - 1) else line in
            let runs = if runs_str = "" then 0 else int_arg "RUNS" runs_str in
            score := !score + runs;
            if wicket then incr wkts;
            incr faced;
            let p = DLS.ball_par_from_states tbl t1 (mk_innings 0 !wkts !faced b2) t1i t2i g50 in
            Printf.printf "%d.%d  %d/%d  par %d  (%s%d)\n"
              (!faced / 6) (!faced mod 6) !score !wkts p
              (if !score >= p then "+" else "-") (abs (!score - p))
          end
        done
      with End_of_file -> ());
      let p = DLS.ball_par_from_states tbl t1 (mk_innings 0 !wkts !faced b2) t1i t2i g50 in
      if !faced = b2 || !wkts = 10 then
        Printf.printf "Innings complete: %d/%d -- %s\n" !score !wkts
          (show_result (DLS.determine_result t !score true (!wkts >= 10) true))
      else
        Printf.printf "Suspended at %d/%d after %d balls -- on termination: %s (par %d)\n"
          !score !wkts !faced (show_result (DLS.par_result p !score true)) p
  | _ -> die usage

(* Park-Miller generator with Schrage reduction: intermediates stay below 2^31, so corpora agree between the native and 32-bit js_of_ocaml builds. *)
let lcg_state = ref 1
let lcg_seed s =
  let s = s mod 2147483647 in
  lcg_state := (if s <= 0 then s + 2147483646 else s)
let rand k =
  let s = !lcg_state in
  let s' = 16807 * (s mod 127773) - 2836 * (s / 127773) in
  let s' = if s' <= 0 then s' + 2147483647 else s' in
  lcg_state := s';
  s' mod k

let cmd_oracle pos =
  match pos with
  | [n] | [n; _] ->
      let n = int_arg "N" n in
      lcg_seed (match pos with [_; sd] -> int_arg "SEED" sd | _ -> 1);
      Printf.printf
        "# dls oracle corpus: replay each case through the implementation under test\n\
         # and diff its target/par against these reference values, which are computed\n\
         # by the machine-checked calculator. seed and case fields make runs reproducible.\n";
      for i = 1 to n do
        let t1b = 6 * (5 + rand 46) in
        let s = 50 + rand 351 in
        let t2b = 6 * (1 + rand (t1b / 6)) in
        let t2i =
          if rand 2 = 0 then []
          else
            let at = 1 + rand t2b in
            let lost = 1 + rand at in
            [ { DLS.bint_at_balls = at; bint_at_wickets = rand 10; bint_balls_lost = lost;
                bint_during_innings = 0; bint_in_powerplay = false } ] in
        let faced = rand (t2b + 1) and wkts = rand 10 in
        let t1 = mk_innings s 0 t1b t1b in
        let target = DLS.ball_target_from_states tbl t1 t2b [] t2i 245 in
        let par = DLS.ball_par_from_states tbl t1 (mk_innings 0 wkts faced t2b) [] t2i 245 in
        let int_json =
          match t2i with
          | [] -> "null"
          | i :: _ -> Printf.sprintf "{\"at\":%d,\"w\":%d,\"lost\":%d}"
                        i.DLS.bint_at_balls i.DLS.bint_at_wickets i.DLS.bint_balls_lost in
        Printf.printf
          "{\"case\":%d,\"s\":%d,\"t1_balls\":%d,\"t2_balls\":%d,\"g50\":245,\"t2_int\":%s,\"target\":%d,\"par_faced\":%d,\"par_wkts\":%d,\"par\":%d}\n"
          i s t1b t2b int_json target faced wkts par
      done
  | _ -> die usage

let cmd_sensitivity pos =
  match pos with
  | [n] | [n; _] ->
      let n = int_arg "N" n in
      lcg_seed (match pos with [_; sd] -> int_arg "SEED" sd | _ -> 1);
      let tables = [ "published", DLS.coq_DLStandardTable;
                     "rational-decay", DLS.coq_RationalDecayTable;
                     "separable-icc", DLS.coq_ICCStandardTable ] in
      Printf.printf
        "# target spread across the three lawful ResourceTable instances on the\n\
         # same reduced match (Team 1 full T1_OVERS innings, Team 2 allocated T2_OVERS)\n";
      Printf.printf "%-6s %-6s %-9s %-10s %-15s %-14s %-7s\n"
        "s" "t1_ov" "t2_ov" "published" "rational-decay" "separable-icc" "spread";
      let max_spread = ref 0 and sum_spread = ref 0 and disagreements = ref 0 in
      for _ = 1 to n do
        let t1o = 20 + rand 31 in
        let t2o = 10 + rand (t1o - 9) in
        let s = 100 + rand 301 in
        let targets =
          List.map (fun (_, t) ->
            DLS.revised_target s (DLS.lookup t t1o 0) (DLS.lookup t t2o 0) 245) tables in
        let lo = List.fold_left min max_int targets
        and hi = List.fold_left max 0 targets in
        let spread = hi - lo in
        if spread > !max_spread then max_spread := spread;
        sum_spread := !sum_spread + spread;
        if spread > 0 then incr disagreements;
        (match targets with
         | [a; b; c] ->
             Printf.printf "%-6d %-6d %-9d %-10d %-15d %-14d %-7d\n" s t1o t2o a b c spread
         | _ -> ())
      done;
      Printf.printf
        "# %d cases: models disagree on %d; mean spread %.1f runs; max spread %d runs\n"
        n !disagreements (float_of_int !sum_spread /. float_of_int (max n 1)) !max_spread
  | _ -> die usage

(* Every rain-affected 1992 World Cup match replayed against the Most Productive Overs rule; interruption states per the Wikipedia 1992 tournament pages; G50 = 245 throughout. *)

let bint during at w lost = {
  DLS.bint_at_balls = at; bint_at_wickets = w; bint_balls_lost = lost;
  bint_during_innings = during; bint_in_powerplay = false }

let target s t1_alloc t2_alloc t1_ints t2_ints =
  DLS.ball_target_from_states tbl (mk_innings s 0 t1_alloc t1_alloc)
    t2_alloc t1_ints t2_ints 245

let cmd_replay () =
  Printf.printf
    "Certified DLS Standard Edition counterfactuals, 1992 World Cup\n\
     (verified pipeline vs the Most Productive Overs rule then in force; G50 = 245)\n\n";

  Printf.printf
    "28 Feb, Mackay: India v Sri Lanka washed out after two balls.\n\
     MPO: no result. DLS: no result (no minimum innings possible).\n\n";

  (* Australia 237/9; India 45/1 after 16.2 of 50 when 3 overs were lost. *)
  let t = target 237 300 300 [] [bint 2 202 1 18] in
  Printf.printf
    "1 Mar, Brisbane: Australia 237/9 (50); India 45/1 after 16.2 when rain cost\n\
     3 overs. MPO set 236 off 47 and India fell 1 run short on 234.\n\
     DLS: revised target %d -- India's 234 %s.\n\n" t
    (if 234 >= t then "wins the match India actually lost by a run"
     else if 234 + 1 = t then "ties the match India actually lost by a run"
     else Printf.sprintf "still loses, by %d" (t - 1 - 234));

  (* Pakistan 74 all out; England 24/1 after 8 overs, abandoned below any minimum. *)
  let t = target 74 300 300 [] [] in
  Printf.printf
    "1 Mar, Adelaide: Pakistan 74 all out; England 24/1 after 8 overs, abandoned.\n\
     MPO: no result (Pakistan's escaped point carried them to the title).\n\
     DLS: %s -- an 8-over innings is below the 20-over minimum either way.\n\n"
    (show_result (DLS.determine_result t 24 false false false));

  (* New Zealand cut from 50 to 35 to 24 overs (9/1 at 2.1, 52/2 at 11.2) and ended at 20.5 on 162/3; Zimbabwe received 18 overs: the tournament's one Team 1-interrupted case. *)
  let nz_ints = [bint 1 287 1 90; bint 1 142 2 66; bint 1 19 3 19] in
  let r1 = DLS.effective_ball_resources tbl (DLS.ball_resources_at_start tbl 300) nz_ints in
  let r2 = DLS.ball_resources_at_start tbl 108 in
  let t = target 162 300 108 nz_ints [] in
  Printf.printf
    "3 Mar, Napier: New Zealand 162/3 in a thrice-cut innings (50 to 35 to 24\n\
     overs, ended at 20.5); Zimbabwe set 154 off 18 by MPO and closed 105/7,\n\
     losing by 48. DLS (Team 1 interrupted, G50 regime): R1 %s, R2 %s,\n\
     revised target %d -- Zimbabwe's 105 %s.\n\n"
    (pct r1) (pct r2) t
    (if 105 + 1 < t then Printf.sprintf "still loses, by %d" (t - 1 - 105)
     else "changes the result");

  (* Reduced to 32 a side pre-match; India 203/7; Zimbabwe terminated at 104/1 after 19.1: a par decision. *)
  let p = DLS.ball_par_from_states tbl (mk_innings 203 0 192 192)
            (mk_innings 104 1 115 192) [] [] 245 in
  Printf.printf
    "7 Mar, Hamilton: reduced to 32 overs a side before play; India 203/7;\n\
     Zimbabwe 104/1 after 19.1 when the match ended. MPO: India by 55.\n\
     DLS par at termination: %d -- Zimbabwe's 104 gives %s%s.\n\n" p
    (show_result (DLS.par_result p 104 true))
    (if 104 < p then Printf.sprintf " by %d runs" (p - 104)
     else if 104 > p then Printf.sprintf " by %d runs" (104 - p) else "");

  (* South Africa 211/7; Pakistan 74/2 after 21.3 when 14 overs were lost. *)
  let t = target 211 300 300 [] [bint 2 171 2 84] in
  Printf.printf
    "8 Mar, Brisbane: South Africa 211/7 (50); Pakistan 74/2 after 21.3 when an\n\
     hour's rain cost 14 overs. MPO set 194 off 36; Pakistan closed 173/8,\n\
     losing by 20. DLS: revised target %d -- 173 %s.\n\n" t
    (if 173 + 1 < t then Printf.sprintf "still loses, by %d" (t - 1 - 173)
     else "changes the result");

  (* India 197 all out; 4 overs lost in West Indies' 11th over, wickets at the stoppage unsourced, so the counterfactual brackets 0-2. *)
  Printf.printf
    "10 Mar, Wellington: India 197 all out; rain in West Indies' 11th over cost\n\
     4 overs. MPO set 195 off 46, chased with 5 wickets in hand. DLS: revised\n\
     target %d, %d or %d for 0, 1 or 2 wickets down at the stoppage (state\n\
     unsourced) -- a few runs easier than the MPO figure; the chase stands.\n\n"
    (target 197 300 300 [] [bint 2 240 0 24])
    (target 197 300 300 [] [bint 2 240 1 24])
    (target 197 300 300 [] [bint 2 240 2 24]);

  (* South Africa 236/4; England 62/0 after 12 when 9 overs were lost. *)
  let t = target 236 300 300 [] [bint 2 228 0 54] in
  Printf.printf
    "12 Mar, Melbourne: South Africa 236/4 (50); England 62/0 after 12 when rain\n\
     cost 9 overs. MPO set 226 off 41, chased with 3 wickets in hand. DLS:\n\
     revised target %d -- %s.\n\n" t
    (if t <= 226 then "no harder than the target England actually chased"
     else Printf.sprintf "%d harder than the MPO figure" (t - 226));

  (* The semi-final, proven in dls.v as target_1992 and result_1992. *)
  let r1 = DLS.effective_ball_resources tbl (DLS.ball_resources_at_start tbl 270) [] in
  let lost = DLS.ball_resource_lost_by_interruption tbl DLS_Extras.sa_rain_1992 in
  let r2 = DLS.effective_ball_resources tbl (DLS.ball_resources_at_start tbl 270)
             [DLS_Extras.sa_rain_1992] in
  let t = DLS.ball_target_from_states tbl DLS_Extras.england_1992
            270 [] [DLS_Extras.sa_rain_1992] 245 in
  Printf.printf
    "22 Mar, Sydney (semi-final): England 252/6 in 45; rain took 12 of South\n\
     Africa's last 13 balls at 231/6 and MPO demanded 21 off the final ball.\n\
     DLS: R1 %s, suspension cost %s, R2 %s, revised target %d -- four to win\n\
     off the last ball. South Africa finished 232: %s. Proven in dls.v.\n\n"
    (pct r1) (pct lost) (pct r2) t
    (show_result (DLS.determine_result t 232 true false true));

  Printf.printf
    "1996 World Cup: no innings was cut by rain mid-match; the only weather\n\
     casualties were Kenya v Zimbabwe at Patna (abandoned, replayed from\n\
     scratch) and New Zealand v UAE at Faisalabad (fog-reduced to 47 overs a\n\
     side before the start, equal allocations). Under DLS both proceed\n\
     identically: a fresh match and an equal-resources target of score plus\n\
     one. The Standard Edition would first have changed a 1996 result only\n\
     if rain had returned mid-innings, which that tournament escaped.\n"

let () =
  match Array.to_list Sys.argv with
  | _ :: cmd :: rest ->
      let pos, t1i, t2i, csv = parse_rest rest in
      (match cmd with
       | "target" -> cmd_target pos t1i t2i
       | "par" -> cmd_par pos t1i t2i
       | "sheet" -> cmd_sheet pos t1i csv
       | "track" -> cmd_track pos t1i t2i
       | "oracle" -> cmd_oracle pos
       | "sensitivity" -> cmd_sensitivity pos
       | "replay" -> cmd_replay ()
       | "help" | "--help" | "-h" -> print_string usage
       | c -> die ("unknown command: " ^ c ^ "\n\n" ^ usage))
  | _ -> print_string usage

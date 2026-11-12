(* ========================================================================= *)
(* Unit pc_rfa_hpsd: the Harnack quadratic at a point of a 3D chart in frame *)
(* and coordinate form, the perturbed quadratic Z(R + alpha I, P,            *)
(* M + beta g), its positive semidefiniteness in a chart through             *)
(* constant-coefficient fields, and the chart independence and continuity    *)
(* needed by the maximum principle.                                          *)
(* ========================================================================= *)

needs "src/pc_rfa_h3d.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The frame form of the Harnack quadratic (RFA_QFORM_FRAME),                *)
(* the identity 4-field rfa_ifld with frame array rfa_i4, and the perturbed  *)
(* quadratic rfa_hz(R + alpha I, P, M + beta g) = rfa_hz + alpha|u|^2 +     *)
(* beta|w|^2 for antisymmetric u (RFA_HZ_PERTURB).                           *)
(* ========================================================================= *)

let rfa_i4 = new_definition
 `rfa_i4 (a:num) (b:num) (c:num) (d:num) =
    ((if a = d /\ b = c then &1 else &0) - (if a = c /\ b = d then &1 else &0)) / &2`;;

let rfa_ifld = new_definition
 `rfa_ifld (G:real^N->real^N^N) =
    \y u. (lmetric2 G y (\m. if m = 1 then u 1 else u 3) *
           lmetric2 G y (\m. if m = 1 then u 2 else u 4) -
           lmetric2 G y (\m. if m = 1 then u 1 else u 4) *
           lmetric2 G y (\m. if m = 1 then u 2 else u 3)) / &2`;;

(* Frame evaluation of a closed equation lhs = rhs whose two sides are       *)
(* frame expressions: both sides go through RFA_FRV_CONV and RFA_MPOLY.     *)

let RFA_FRAME_EQ mf yth sth tm =
  let l = lhs tm and r = rhs tm in
  let ev t = let th1 = RFA_FRV_CONV mf yth sth t in
             let th2 = CONV_RULE (RAND_CONV (REWRITE_CONV[] THENC DEPTH_CONV BETA_CONV)) th1 in
             TRANS th2 (RFA_MPOLY (rand(concl th2))) in
  let thl = ev l and thr = ev r in
  if aconv (rand(concl thl)) (rand(concl thr)) then TRANS thl (SYM thr)
  else failwith "RFA_FRAME_EQ: normal forms differ";;

let RFA_ENGINE_SAVE () =
  (!rfa_sf_bases, !rfa_sf_unfolds, !rfa_lnf_unfolds, !rfa_frv_unfolds, !rfa_mp_hook);;

let RFA_ENGINE_RESTORE (b1, b2, b3, b4, b5) =
  rfa_sf_bases := b1; rfa_sf_unfolds := b2; rfa_lnf_unfolds := b3; rfa_frv_unfolds := b4;
  rfa_mp_hook := b5;
  Hashtbl.reset rfa_sf_cache; Hashtbl.reset rfa_lnf_cache;
  Hashtbl.reset rfa_atom_cache; Hashtbl.reset rfa_mp_cache;;

let RFA_ENGINE_RESET () =
  Hashtbl.reset rfa_sf_cache; Hashtbl.reset rfa_lnf_cache;
  Hashtbl.reset rfa_atom_cache; Hashtbl.reset rfa_mp_cache;;

let RFA_QFORM_FRAME_DERIVE asm w =
  let hs = map ASSUME (conjuncts asm) in
  let h k = el k hs in
  let mf = h 0 and h_y = h 1 and h_frame = h 3 in
  let saved = RFA_ENGINE_SAVE () in
  RFA_ENGINE_RESET ();
  rfa_sf_bases := [h 4; h 5; h 6; h 7; h 8; RFA_SF_LRIC2; RFA_SF_LMETRIC2; RFA_SF_LRM4;
                   RFA_SF_SC; RFA_SF_HRIC];
  rfa_sf_unfolds := []; rfa_lnf_unfolds := []; rfa_frv_unfolds := [rfa_qform];
  rfa_mp_hook := (fun tm -> failwith "atom");
  let th1 = RFA_FRV_CONV mf h_y h_frame (lhs w) in
  let nfl = TRANS th1 (RFA_MPOLY (rand(concl th1))) in
  let th2 = (REWRITE_CONV[rfa_hz] THENC DEPTH_CONV BETA_CONV) (rhs w) in
  let nfr = TRANS th2 (RFA_MPOLY (rand(concl th2))) in
  RFA_ENGINE_RESTORE saved;
  if not (aconv (rand(concl nfl)) (rand(concl nfr)))
  then failwith "RFA_QFORM_FRAME_DERIVE: normal forms"
  else itlist PROVE_HYP (CONJUNCTS (ASSUME asm)) (TRANS nfl (SYM nfr));;

let RFA_QFORM_FRAME = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) M P R (Uf:real^3->(num->real^3)->real) Wf u.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     rfa_sf 2 U M /\ rfa_sf 3 U P /\ rfa_sf 4 U R /\ rfa_sf 2 U Uf /\ rfa_sf 1 U Wf
     ==> rfa_qform G M P R Uf Wf y u =
         rfa_hz 3 (\a b c d. R y (rfa_ft S [a; b; d; c])) (\a b c. P y (rfa_ft S [a; b; c]))
                  (\a b. M y (rfa_ft S [a; b])) (\a b. Uf y (rfa_ft S [a; b]))
                  (\a. Wf y (rfa_ft S [a]))`,
  REPEAT GEN_TAC THEN
  W(fun (_, w) -> let a, c = dest_imp w in ACCEPT_TAC (DISCH a (RFA_QFORM_FRAME_DERIVE a c))));;

let RFA_IFLD_FRAME = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) a b c d.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N) /\
     1 <= c /\ c <= dimindex(:N) /\ 1 <= d /\ d <= dimindex(:N)
     ==> rfa_ifld G y (rfa_ft S [a; b; d; c]) = rfa_i4 a b c d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  REWRITE_TAC[rfa_ifld; lmetric2; rfa_ft] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; ARITH] THEN
  ASM_SIMP_TAC[RFA_GFRAME_ORTHO] THEN REWRITE_TAC[rfa_i4] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC);;

let RFA_HZ_PERTURB = prove
 (`!(R:num->num->num->num->real) P M (u:num->num->real) w alpha beta.
     (!i j. u i j = --(u j i))
     ==> rfa_hz 3 (\a b c d. R a b c d + alpha * rfa_i4 a b c d) P
                  (\a b. M a b + beta * (if a = b then &1 else &0)) u w =
         rfa_hz 3 R P M u w +
         alpha * sum(1..3) (\a. sum(1..3) (\b. u a b pow 2)) +
         beta * sum(1..3) (\a. w a pow 2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "anti") THEN
  SUBGOAL_THEN `(u:num->num->real) 1 1 = &0 /\ u 2 2 = &0 /\ u 3 3 = &0 /\
                u 2 1 = --(u 1 2) /\ u 3 1 = --(u 1 3) /\ u 3 2 = --(u 2 3)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC(REAL_ARITH `!x:real. x = --x ==> x = &0`)) THEN
    USE_THEN "anti" MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "anti" (K ALL_TAC) THEN
  REWRITE_TAC[rfa_hz; rfa_i4; SUM_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Frame arrays.  The base arrays of Ric, nabla Ric and                      *)
(* nabla^2 Ric in a frame (rfa_ric_a, rfa_dr_a, rfa_ddr_a), the 3D array     *)
(* formulas for the Harnack tensors (rfa_arr_r in the rfa_hz slot           *)
(* convention, rfa_arr_p, rfa_arr_m), and their frame values                *)
(* (RFA_LRM4_ARR, RFA_HP_ARR, RFA_HM_ARR), proved index by index by frame    *)
(* evaluation.                                                               *)
(* ========================================================================= *)

let rfa_kd = new_definition
 `rfa_kd (i:num) (j:num) = if i = j then &1 else &0`;;

let rfa_ric_a = new_definition
 `rfa_ric_a (G:real^N->real^N^N) (y:real^N) (S:real^N^N) =
    \i j. lric2 G y (rfa_ft S [i; j])`;;

let rfa_dr_a = new_definition
 `rfa_dr_a (G:real^N->real^N^N) (y:real^N) (S:real^N^N) =
    \i j k. lnabla 2 G (lric2 G) y (rfa_ft S [i; j; k])`;;

let rfa_ddr_a = new_definition
 `rfa_ddr_a (G:real^N->real^N^N) (y:real^N) (S:real^N^N) =
    \i j k l. lnabla 3 G (lnabla 2 G (lric2 G)) y (rfa_ft S [i; j; k; l])`;;

let rfa_arr_r = new_definition
 `rfa_arr_r (ric:num->num->real) a b c d =
    ric a d * rfa_kd b c + ric b c * rfa_kd a d - ric a c * rfa_kd b d - ric b d * rfa_kd a c -
    inv(&2) * sum(1..3) (\e. ric e e) * (rfa_kd a d * rfa_kd b c - rfa_kd a c * rfa_kd b d)`;;

let rfa_arr_p = new_definition
 `rfa_arr_p (dr:num->num->num->real) a b c = dr b c a - dr a c b`;;

let rfa_arr_m = new_definition
 `rfa_arr_m (ric:num->num->real) (ddr:num->num->num->num->real) tau a b =
    sum(1..3) (\e. ddr a b e e) - inv(&2) * sum(1..3) (\e. ddr e e a b) +
    (&3 * sum(1..3) (\e. ric e e) * ric a b -
     &4 * sum(1..3) (\e. ric a e * ric e b) +
     (&2 * sum(1..3) (\e. sum(1..3) (\f. ric e f * ric e f)) -
      sum(1..3) (\e. ric e e) * sum(1..3) (\e. ric e e)) * rfa_kd a b) -
    sum(1..3) (\e. ric a e * ric e b) + inv(&2 * tau) * ric a b`;;

(* The engine proof of a frame identity at numeral indices: both sides are  *)
(* evaluated (RFA_FRV_CONV with the 3D unfold tables of pc_rfa_h3d) and     *)
(* normalized (RFA_MPOLY with the metric evaluated).                        *)

let RFA_NUMERAL_FRAME_EQ mf h_y h_invS h_frame tm =
  let uu = rand(rator(concl mf)) and gg = rand(concl mf) in
  let yv = rand(rator(concl h_y)) in
  let sv = rand(rand(concl h_frame)) in
  let met_f = mk_comb(`lmetric2:(real^3->real^3^3)->real^3->(num->real^3)->real`, gg) in
  let h_all = end_itlist CONJ [mf; h_y; h_invS; h_frame] in
  let hook tm =
    match (try Some(dest_comb(rator tm), rand tm) with Failure _ -> None) with
      Some((f, yy), wt) when f = met_f && yy = yv ->
        let [i; j] = dest_list (rand wt) in
        MP (REWRITE_RULE[DIMINDEX_3; ARITH]
              (ISPECL [uu; gg; yv; sv; i; j] RFA_FT_METRIC)) h_all
    | _ -> failwith "atom" in
  let saved = RFA_ENGINE_SAVE () in
  RFA_ENGINE_RESET ();
  rfa_lnf_unfolds := [RFA_SC_CONTR; RFA_EQON_HRIC_3D; RFA_EQON_LRM4_3D; RFA_HRIC3_LAMBDA;
                      rfa_ric2sq; rfa_nric2; RFA_HDR_LAMBDA; RFA_EQON_HP];
  rfa_frv_unfolds := [RFA_EQON_HM; RFA_EQON_HP; RFA_HDR_LAMBDA; RFA_EQON_HRIC_3D;
                      RFA_EQON_LRM4_3D; RFA_HRIC3_LAMBDA; rfa_ric2sq; rfa_nric2; RFA_SC_CONTR;
                      rfa_ifld];
  rfa_mp_hook := (fun t -> try hook t with Failure s -> failwith s
                                          | Match_failure _ -> failwith "atom");
  let res =
    try
      let ev t = let th1 = RFA_FRV_CONV mf h_y h_frame t in
                 TRANS th1 (RFA_MPOLY (rand(concl th1))) in
      let thl = ev (lhs tm) in
      let th2 = (REWRITE_CONV[rfa_arr_r; rfa_arr_p; rfa_arr_m; rfa_kd; rfa_ric_a; rfa_dr_a;
                              rfa_ddr_a; rfa_i4] THENC DEPTH_CONV BETA_CONV) (rhs tm) in
      let thr = TRANS th2 (RFA_MPOLY (rand(concl th2))) in
      if aconv (rand(concl thl)) (rand(concl thr)) then TRANS thl (SYM thr)
      else failwith "RFA_NUMERAL_FRAME_EQ: normal forms"
    with e -> (RFA_ENGINE_RESTORE saved; raise e) in
  RFA_ENGINE_RESTORE saved; res;;

(* Case split on indices in 1..3, then the engine on each numeral goal.     *)

let RFA_INDEX_CASES_TAC vs =
  MAP_EVERY (fun v ->
    SUBGOAL_THEN (list_mk_disj (map (fun n -> mk_eq(v, mk_small_numeral n)) [1;2;3])) MP_TAC
    THENL [ASM_ARITH_TAC; DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)]) vs;;

let RFA_FRAME_NUM_TAC (asl, w) =
  let find p = snd(find (fun (_, th) -> p (concl th)) asl) in
  let mf = find (fun t -> try fst(dest_const(fst(strip_comb t))) = "metric_field"
                          with Failure _ -> false) in
  let h_y = find (fun t -> try fst(dest_const(rator(rator t))) = "IN" &&
                               rand t = rand(rator(concl mf)) with Failure _ -> false) in
  let h_invS = find (fun t -> try fst(dest_const(rator t)) = "invertible" with Failure _ -> false) in
  let h_frame = find (fun t -> try fst(dest_const(fst(strip_comb(lhs t)))) = "matrix_inv"
                               with Failure _ -> false) in
  ACCEPT_TAC (RFA_NUMERAL_FRAME_EQ mf h_y h_invS h_frame w) (asl, w);;

let RFA_LRM4_ARR = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) a b c d.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 /\ 1 <= d /\ d <= 3
     ==> lrm4 G y (rfa_ft S [a; b; d; c]) = rfa_arr_r (rfa_ric_a G y S) a b c d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RFA_INDEX_CASES_TAC [`a:num`; `b:num`; `c:num`; `d:num`] THEN RFA_FRAME_NUM_TAC);;

let RFA_HP_ARR = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) a b c.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3
     ==> rfa_hP G y (rfa_ft S [a; b; c]) = rfa_arr_p (rfa_dr_a G y S) a b c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RFA_INDEX_CASES_TAC [`a:num`; `b:num`; `c:num`] THEN RFA_FRAME_NUM_TAC);;

let RFA_HM_ARR = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t a b.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
     ==> rfa_hM s t G y (rfa_ft S [a; b]) =
         rfa_arr_m (rfa_ric_a G y S) (rfa_ddr_a G y S) (t - s) a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RFA_INDEX_CASES_TAC [`a:num`; `b:num`] THEN RFA_FRAME_NUM_TAC);;

(* ========================================================================= *)
(* Smoothness of the Harnack tensors and of the identity                     *)
(* 4-field (rfa_sf), constant-coefficient fields rfa_cf2 A, rfa_cf1 w with   *)
(* their frame components, the coordinate form rfa_zcc of the perturbed     *)
(* Harnack quadratic and the array form rfa_hza, and the bridge between      *)
(* them in any orthonormal frame (RFA_ZCC_FRAME).                           *)
(* ========================================================================= *)

let RFA_SF_EQON = prove
 (`!k U (f:real^N->(num->real^N)->real) g.
     rfa_eqon U f g /\ rfa_sf k U g ==> rfa_sf k U f`,
  REWRITE_TAC[rfa_eqon; rfa_sf; ltensor_field] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_SIMP_TAC[] THEN MESON_TAC[];
    X_GEN_TAC `u:num->real^N` THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\y. lift((g:real^N->(num->real^N)->real) y u)` THEN
    ASM_SIMP_TAC[]]);;

let RFA_SF_PROVE_WITH unfolds mf tm =
  let saved = RFA_ENGINE_SAVE () in
  RFA_ENGINE_RESET ();
  rfa_sf_bases := [RFA_SF_LRIC2; RFA_SF_LMETRIC2; RFA_SF_LRM4; RFA_SF_SC; RFA_SF_HRIC];
  rfa_sf_unfolds := unfolds;
  let res = try RFA_SF_PROVE mf tm with e -> (RFA_ENGINE_RESTORE saved; raise e) in
  RFA_ENGINE_RESTORE saved; res;;

let RFA_SF_HM = prove
 (`!U (G:real^N->real^N^N) s t. metric_field U G ==> rfa_sf 2 U (rfa_hM s t G)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun mf ->
    let eq = MP (ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `s:real`; `t:real`]
                        RFA_EQON_HM) mf in
    let sf = RFA_SF_PROVE_WITH [rfa_ric2sq] mf (rand(concl eq)) in
    ACCEPT_TAC (MATCH_MP RFA_SF_EQON (CONJ eq sf))));;

let RFA_SF_HP = prove
 (`!U (G:real^N->real^N^N). metric_field U G ==> rfa_sf 3 U (rfa_hP G)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun mf ->
    let eq = MP (ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_EQON_HP) mf in
    let sf = RFA_SF_PROVE_WITH [] mf (rand(concl eq)) in
    ACCEPT_TAC (MATCH_MP RFA_SF_EQON (CONJ eq sf))));;

let RFA_IFLD_LTPROD = prove
 (`!G:real^N->real^N^N.
     rfa_ifld G =
     \y u. inv(&2) *
           (ltperm (swap(2,3)) (ltprod 2 (lmetric2 G) (lmetric2 G)) y u -
            ltperm (\m. if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m)
                   (ltprod 2 (lmetric2 G) (lmetric2 G)) y u)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; rfa_ifld; ltperm; ltprod; swap; lmetric2] THEN
  REPEAT GEN_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFA_SF_IFLD = prove
 (`!U (G:real^N->real^N^N). metric_field U G ==> rfa_sf 4 U (rfa_ifld G)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[RFA_IFLD_LTPROD] THEN
  FIRST_ASSUM(fun mf -> ACCEPT_TAC (RFA_SF_PROVE_WITH [] mf
    (rand(concl(SPEC `G:real^N->real^N^N` RFA_IFLD_LTPROD))))));;

let rfa_cf2 = new_definition
 `rfa_cf2 (A:real^N^N) = \(y:real^N) (u:num->real^N). u 1 dot (A ** u 2)`;;

let rfa_cf1 = new_definition
 `rfa_cf1 (w:real^N) = \(y:real^N) (u:num->real^N). w dot u 1`;;

let RFA_SF_CF2 = prove
 (`!U (A:real^N^N). rfa_sf 2 U (rfa_cf2 A)`,
  REWRITE_TAC[rfa_sf; ltensor_field; rfa_cf2; SMOOTH_MAP_ON_CONST] THEN
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `(u:num->real^N) 1 = u' 1 /\ u 2 = u' 2` (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[ARITH] THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT];
    REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL; LINEAR_LIFT_DOT]]);;

let RFA_SF_CF1 = prove
 (`!U (w:real^N). rfa_sf 1 U (rfa_cf1 w)`,
  REWRITE_TAC[rfa_sf; ltensor_field; rfa_cf1; SMOOTH_MAP_ON_CONST] THEN
  REPEAT STRIP_TAC THENL
   [AP_TERM_TAC THEN ASM_SIMP_TAC[ARITH];
    SUBGOAL_THEN `i = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LINEAR_LIFT_DOT]]);;

let RFA_CF2_FRAME = prove
 (`!(A:real^N^N) (S:real^N^N) y i j.
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> rfa_cf2 A y (rfa_ft S [i; j]) = (S ** A ** transp S)$i$j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_cf2; rfa_ft] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; ARITH; DOT_MATRIX_TRANSP_LMUL] THEN
  ASM_SIMP_TAC[DOT_BASIS] THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]);;

let RFA_CF1_FRAME = prove
 (`!(w:real^N) (S:real^N^N) y i.
     1 <= i /\ i <= dimindex(:N)
     ==> rfa_cf1 w y (rfa_ft S [i]) = (S ** w)$i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_cf1; rfa_ft] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; ARITH] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
  ASM_SIMP_TAC[DOT_MATRIX_TRANSP_LMUL; DOT_BASIS]);;

let RFA_HZ_EQ = prove
 (`!n (R:num->num->num->num->real) P M (u:num->num->real) w R' P' M' u' w'.
     (!a b c d. 1 <= a /\ a <= n /\ 1 <= b /\ b <= n /\ 1 <= c /\ c <= n /\
                1 <= d /\ d <= n ==> R a b c d = R' a b c d) /\
     (!a b c. 1 <= a /\ a <= n /\ 1 <= b /\ b <= n /\ 1 <= c /\ c <= n
              ==> P a b c = P' a b c) /\
     (!a b. 1 <= a /\ a <= n /\ 1 <= b /\ b <= n ==> M a b = M' a b) /\
     (!a b. 1 <= a /\ a <= n /\ 1 <= b /\ b <= n ==> u a b = u' a b) /\
     (!a. 1 <= a /\ a <= n ==> w a = w' a)
     ==> rfa_hz n R P M u w = rfa_hz n R' P' M' u' w'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[rfa_hz] THEN
  let sum_tac = REPEAT(MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
                ASM_SIMP_TAC[] in
  BINOP_TAC THENL [sum_tac; BINOP_TAC THENL [AP_TERM_TAC THEN sum_tac; sum_tac]]);;

let rfa_zcc = new_definition
 `rfa_zcc (G:real^3->real^3^3) s t alpha beta (y:real^3) (A:real^3^3) (w:real^3) =
    rfa_qform G (\y u. rfa_hM s t G y u + beta * lmetric2 G y u) (rfa_hP G)
                (\y u. lrm4 G y u + alpha * rfa_ifld G y u) (rfa_cf2 A) (rfa_cf1 w) y
                (\m. vec 0)`;;

let rfa_hza = new_definition
 `rfa_hza (ric:num->num->real) (dr:num->num->num->real) (ddr:num->num->num->num->real)
          tau alpha beta (u:num->num->real) (w:num->real) =
    rfa_hz 3 (\a b c d. rfa_arr_r ric a b c d + alpha * rfa_i4 a b c d)
             (\a b c. rfa_arr_p dr a b c)
             (\a b. rfa_arr_m ric ddr tau a b + beta * rfa_kd a b) u w`;;

let RFA_ZCC_FRAME = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t alpha beta A w.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S
     ==> rfa_zcc G s t alpha beta y A w =
         rfa_hza (rfa_ric_a G y S) (rfa_dr_a G y S) (rfa_ddr_a G y S) (t - s) alpha beta
                 (\i j. (S ** A ** transp S)$i$j) (\i. (S ** w)$i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[rfa_zcc; rfa_hza] THEN
  W(fun (asl, w) ->
    let mf = ASSUME `metric_field U (G:real^3->real^3^3)` in
    let hs = map ASSUME [`(y:real^3) IN U`; `invertible (S:real^3^3)`;
                         `matrix_inv((G:real^3->real^3^3) y) = transp (S:real^3^3) ** S`] in
    let _, args = strip_comb (lhs w) in
    let [gg; mm; pp; rr; uf; wf; yy; uu] = args in
    let sfm = MP (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `s:real`; `t:real`]
                         RFA_SF_HM) mf
    and sfi = MP (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`] RFA_SF_IFLD) mf in
    let saved = RFA_ENGINE_SAVE () in
    RFA_ENGINE_RESET ();
    rfa_sf_bases := [sfm; sfi; RFA_SF_LRIC2; RFA_SF_LMETRIC2; RFA_SF_LRM4];
    rfa_sf_unfolds := [];
    let th1 = RFA_SF_PROVE mf mm and th2 = RFA_SF_PROVE mf rr in
    RFA_ENGINE_RESTORE saved;
    let thp = MP (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`] RFA_SF_HP) mf in
    let thu = ISPECL [`U:real^3->bool`; `A:real^3^3`] RFA_SF_CF2
    and thw = ISPECL [`U:real^3->bool`; `w:real^3`] RFA_SF_CF1 in
    let th = MP (ISPECL [`U:real^3->bool`; gg; yy; `S:real^3^3`; mm; pp; rr; uf; wf; uu]
                        RFA_QFORM_FRAME)
                (end_itlist CONJ ([mf] @ hs @ [th1; thp; th2; thu; thw])) in
    GEN_REWRITE_TAC LAND_CONV [th]) THEN
  MATCH_MP_TAC RFA_HZ_EQ THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MAP_EVERY (fun th -> MP_TAC th THEN ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_TAC)
    (map (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`])
       [RFA_LRM4_ARR; RFA_IFLD_FRAME; RFA_HP_ARR; RFA_FT_METRIC] @
     [ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
              `s:real`; `t:real`] RFA_HM_ARR]) THEN
  ASM_SIMP_TAC[RFA_CF2_FRAME; RFA_CF1_FRAME; DIMINDEX_3; rfa_kd]);;

(* ========================================================================= *)
(* Positive (semi)definiteness of the perturbed Harnack                      *)
(* quadratic, in coordinate form over constant-coefficient fields            *)
(* (rfa_hpsd_cc, rfa_hpd_cc) and in array form for a frame (rfa_hpsd_fr,     *)
(* rfa_hpd_fr), and their equivalence in any orthonormal frame               *)
(* (RFA_HPSD_CC_FR, RFA_HPD_CC_FR).                                          *)
(* ========================================================================= *)

let rfa_hpsd_fr = new_definition
 `rfa_hpsd_fr ric dr ddr tau alpha beta <=>
    !(u:num->num->real) (w:num->real).
      (!i j. u i j = --(u j i)) ==> &0 <= rfa_hza ric dr ddr tau alpha beta u w`;;

let rfa_hpd_fr = new_definition
 `rfa_hpd_fr ric dr ddr tau alpha beta <=>
    !(u:num->num->real) (w:num->real).
      (!i j. u i j = --(u j i)) /\
      ~((!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 ==> u i j = &0) /\
        (!i. 1 <= i /\ i <= 3 ==> w i = &0))
      ==> &0 < rfa_hza ric dr ddr tau alpha beta u w`;;

let rfa_hpsd_cc = new_definition
 `rfa_hpsd_cc (G:real^3->real^3^3) s t alpha beta y <=>
    !A w. transp A = --A ==> &0 <= rfa_zcc G s t alpha beta y A w`;;

let rfa_hpd_cc = new_definition
 `rfa_hpd_cc (G:real^3->real^3^3) s t alpha beta y <=>
    !A w. transp A = --A /\ ~(A = mat 0 /\ w = vec 0)
          ==> &0 < rfa_zcc G s t alpha beta y A w`;;

(* The array of an antisymmetric matrix, zero outside the index range.       *)

let rfa_marr = new_definition
 `rfa_marr (A:real^3^3) =
    \i j. if 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 then A$i$j else &0`;;

let rfa_varr = new_definition
 `rfa_varr (w:real^3) = \i. if 1 <= i /\ i <= 3 then w$i else &0`;;

let RFA_MARR_ANTI = prove
 (`!A:real^3^3. transp A = --A ==> !i j. rfa_marr A i j = --(rfa_marr A j i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_marr] THEN
  ASM_CASES_TAC `1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `1 <= j /\ j <= 3 /\ 1 <= i /\ i <= 3` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\M:real^3^3. M$j$i`) THEN
    ASM_SIMP_TAC[TRANSP_COMPONENT; MATRIX_NEG_COMPONENT; DIMINDEX_3] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `~(1 <= j /\ j <= 3 /\ 1 <= i /\ i <= 3)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; REAL_ARITH_TAC]]);;

(* The frame form of rfa_zcc with arrays restricted to 1..3.                 *)

let RFA_ZCC_FRAME_ARR = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t alpha beta A w.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S
     ==> rfa_zcc G s t alpha beta y A w =
         rfa_hza (rfa_ric_a G y S) (rfa_dr_a G y S) (rfa_ddr_a G y S) (t - s) alpha beta
                 (rfa_marr (S ** A ** transp S)) (rfa_varr (S ** w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                 `s:real`; `t:real`; `alpha:real`; `beta:real`; `A:real^3^3`; `w:real^3`]
         RFA_ZCC_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[rfa_hza] THEN MATCH_MP_TAC RFA_HZ_EQ THEN
  SIMP_TAC[rfa_marr; rfa_varr]);;

let RFA_LAMBDA_ANTI = prove
 (`!u:num->num->real.
     (!i j. u i j = --(u j i))
     ==> transp((lambda i j. u i j):real^3^3) = --(lambda i j. u i j)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; TRANSP_COMPONENT; MATRIX_NEG_COMPONENT] THEN
  ASM_MESON_TAC[]);;

let RFA_CONJ_ANTI = prove
 (`!(A:real^N^N) (B:real^N^N).
     transp A = --A ==> transp(B ** A ** transp B) = --(B ** A ** transp B)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_LNEG; MATRIX_MUL_RNEG;
                  MATRIX_MUL_ASSOC]);;

let RFA_CONJ_INV = prove
 (`!(S:real^N^N) (X:real^N^N).
     invertible S ==> S ** (matrix_inv S ** X ** transp(matrix_inv S)) ** transp S = X`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_LID] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
  ASM_SIMP_TAC[MATRIX_INV; TRANSP_MAT; MATRIX_MUL_RID]);;

let RFA_MARR_LAMBDA = prove
 (`!u:num->num->real.
     !i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
           ==> rfa_marr ((lambda i j. u i j):real^3^3) i j = u i j`,
  SIMP_TAC[rfa_marr; LAMBDA_BETA; DIMINDEX_3]);;

let RFA_VARR_LAMBDA = prove
 (`!w:num->real. !i. 1 <= i /\ i <= 3 ==> rfa_varr ((lambda i. w i):real^3) i = w i`,
  SIMP_TAC[rfa_varr; LAMBDA_BETA; DIMINDEX_3]);;

let RFA_HZA_EQ = prove
 (`!ric dr ddr tau alpha beta (u:num->num->real) (w:num->real) u' w'.
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 ==> u i j = u' i j) /\
     (!i. 1 <= i /\ i <= 3 ==> w i = w' i)
     ==> rfa_hza ric dr ddr tau alpha beta u w = rfa_hza ric dr ddr tau alpha beta u' w'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_hza] THEN MATCH_MP_TAC RFA_HZ_EQ THEN
  ASM_SIMP_TAC[]);;

let RFA_HPSD_CC_FR = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t alpha beta.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S
     ==> (rfa_hpsd_cc G s t alpha beta y <=>
          rfa_hpsd_fr (rfa_ric_a G y S) (rfa_dr_a G y S) (rfa_ddr_a G y S) (t - s)
                      alpha beta)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_hpsd_cc; rfa_hpsd_fr] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                RFA_ZCC_FRAME_ARR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:num->num->real`; `w:num->real`] THEN
    DISCH_THEN(fun anti ->
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`matrix_inv(S:real^3^3) ** ((lambda i j. u i j):real^3^3) ** transp(matrix_inv S)`;
       `matrix_inv(S:real^3^3) ** ((lambda i. w i):real^3)`]) THEN
    ASM_SIMP_TAC[RFA_CONJ_INV; MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC RFA_CONJ_ANTI THEN MATCH_MP_TAC RFA_LAMBDA_ANTI THEN ACCEPT_TAC anti;
      ALL_TAC]) THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> &0 <= a ==> &0 <= b`) THEN
    MATCH_MP_TAC RFA_HZA_EQ THEN SIMP_TAC[RFA_MARR_LAMBDA; RFA_VARR_LAMBDA];
    MAP_EVERY X_GEN_TAC [`A:real^3^3`; `w:real^3`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC RFA_MARR_ANTI THEN
    MATCH_MP_TAC RFA_CONJ_ANTI THEN ASM_REWRITE_TAC[]]);;

let RFA_HPD_CC_FR = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) s t alpha beta.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S
     ==> (rfa_hpd_cc G s t alpha beta y <=>
          rfa_hpd_fr (rfa_ric_a G y S) (rfa_dr_a G y S) (rfa_ddr_a G y S) (t - s)
                     alpha beta)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_hpd_cc; rfa_hpd_fr] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                RFA_ZCC_FRAME_ARR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:num->num->real`; `w:num->real`] THEN
    DISCH_THEN(fun th -> let anti, nz = CONJ_PAIR th in
    ASSUME_TAC nz THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`matrix_inv(S:real^3^3) ** ((lambda i j. u i j):real^3^3) ** transp(matrix_inv S)`;
       `matrix_inv(S:real^3^3) ** ((lambda i. w i):real^3)`]) THEN
    ASM_SIMP_TAC[RFA_CONJ_INV; MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC RFA_CONJ_ANTI THEN MATCH_MP_TAC RFA_LAMBDA_ANTI THEN ACCEPT_TAC anti;
        ALL_TAC] THEN
      DISCH_THEN(fun th -> let thA, thw = CONJ_PAIR th in
        MP_TAC (AP_TERM `\M:real^3^3. (S:real^3^3) ** M ** transp S` thA) THEN
        MP_TAC (AP_TERM `\v:real^3. (S:real^3^3) ** v` thw)) THEN
      ASM_SIMP_TAC[RFA_CONJ_INV; MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID;
                   MATRIX_MUL_LZERO; MATRIX_MUL_RZERO; MATRIX_VECTOR_MUL_RZERO] THEN
      SIMP_TAC[CART_EQ; LAMBDA_BETA; MAT_COMPONENT; VEC_COMPONENT; DIMINDEX_3] THEN
      REWRITE_TAC[COND_ID] THEN ASM_MESON_TAC[];
      ALL_TAC]) THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> &0 < a ==> &0 < b`) THEN
    MATCH_MP_TAC RFA_HZA_EQ THEN SIMP_TAC[RFA_MARR_LAMBDA; RFA_VARR_LAMBDA];
    MAP_EVERY X_GEN_TAC [`A:real^3^3`; `w:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_MARR_ANTI THEN MATCH_MP_TAC RFA_CONJ_ANTI THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[rfa_marr; rfa_varr] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((A:real^3^3) = mat 0 /\ (w:real^3) = vec 0)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(S:real^3^3) ** A ** transp S = mat 0 /\ S ** (w:real^3) = vec 0`
    MP_TAC THENL
     [SIMP_TAC[CART_EQ; MAT_COMPONENT; VEC_COMPONENT; DIMINDEX_3] THEN
      REWRITE_TAC[COND_ID] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (MP_TAC o AP_TERM `\M:real^3^3. matrix_inv (S:real^3^3) ** M ** transp(matrix_inv S)`)
      (MP_TAC o AP_TERM `\v:real^3. matrix_inv (S:real^3^3) ** v`)) THEN
    REWRITE_TAC[MATRIX_MUL_LZERO; MATRIX_MUL_RZERO; MATRIX_VECTOR_MUL_RZERO;
                MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_LID; MATRIX_VECTOR_MUL_LID] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
    ASM_SIMP_TAC[MATRIX_INV; TRANSP_MAT; MATRIX_MUL_RID] THEN MESON_TAC[]]);;

(* ========================================================================= *)
(* Chart independence.  Under a diffeomorphism h with                        *)
(* G = mpullback h G' on the source, Ric, nabla Ric and nabla^2 Ric of G are *)
(* the pullbacks of those of G', so their arrays in a frame S at y equal     *)
(* those of G' at h y in the frame S ** transp(Dh), which is orthonormal     *)
(* for G' (RFA_BASE_ARR_PULLBACK); hence the positive (semi)definiteness of *)
(* the perturbed Harnack quadratic is the same in the two charts            *)
(* (RFA_HPSD_CC_PULLBACK, RFA_HPD_CC_PULLBACK).                             *)
(* ========================================================================= *)

let RFA_PB_LRIC2 = prove
 (`!U U' (h:real^N->real^N) h' (G:real^N->real^N^N) G'.
     metric_field U G' /\ diffeomorphism_on U' U h h' /\
     (!z. z IN U' ==> G z = mpullback h G' z)
     ==> !z u. z IN U' ==> lric2 G z u = ltpullback h (lric2 G') z u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[lric2; ltpullback] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lricci (mpullback (h:real^N->real^N) G') z (u 1) (u 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `U':real^N->bool` THEN
    ASM_MESON_TAC[diffeomorphism_on];
    MATCH_MP_TAC LRICCI_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let RFA_PB_LNABLA = prove
 (`!k U U' (h:real^N->real^N) h' (G:real^N->real^N^N) G' tf tf'.
     metric_field U G' /\ diffeomorphism_on U' U h h' /\
     (!z. z IN U' ==> G z = mpullback h G' z) /\ rfa_sf k U tf' /\
     (!z u. z IN U' ==> tf z u = ltpullback h tf' z u)
     ==> !z u. z IN U' ==> lnabla k G tf z u = ltpullback h (lnabla k G' tf') z u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla k (mpullback (h:real^N->real^N) G') (ltpullback h tf') z u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U':real^N->bool` THEN
    ASM_MESON_TAC[diffeomorphism_on];
    MATCH_MP_TAC LNABLA_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
    ASM_MESON_TAC[rfa_sf]]);;

(* The pulled-back frame. *)

let RFA_PB_FRAME = prove
 (`!U U' (h:real^N->real^N) h' (G:real^N->real^N^N) G' y (S:real^N^N).
     metric_field U G' /\ diffeomorphism_on U' U h h' /\ y IN U' /\
     (!z. z IN U' ==> G z = mpullback h G' z) /\
     invertible S /\ matrix_inv(G y) = transp S ** S
     ==> invertible(S ** transp(matrix(frechet_derivative h (at y)))) /\
         matrix_inv(G' (h y)) =
         transp(S ** transp(matrix(frechet_derivative h (at y)))) **
         (S ** transp(matrix(frechet_derivative h (at y))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `J = matrix(frechet_derivative (h:real^N->real^N) (at y))` THEN
  SUBGOAL_THEN `invertible(J:real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
    EXISTS_TAC `matrix(frechet_derivative (h':real^N->real^N)
                                          (at ((h:real^N->real^N) y)))` THEN
    SUBGOAL_THEN `linear(frechet_derivative (h':real^N->real^N)
                                            (at ((h:real^N->real^N) y)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LRG_DIFFEO_INV_LINEAR THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM MATRIX_COMPOSE] THEN
    SUBGOAL_THEN
     `frechet_derivative (h':real^N->real^N) (at ((h:real^N->real^N) y)) o
      frechet_derivative h (at y) = (\x. x)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; REWRITE_TAC[MATRIX_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible((G':real^N->real^N^N) ((h:real^N->real^N) y))` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  ASM_SIMP_TAC[INVERTIBLE_MATRIX_MUL; INVERTIBLE_TRANSP] THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) y = transp (J:real^N^N) ** (G':real^N->real^N^N) ((h:real^N->real^N) y) ** J`
  ASSUME_TAC THENL [ASM_SIMP_TAC[mpullback]; ALL_TAC] THEN
  UNDISCH_TAC `matrix_inv((G:real^N->real^N^N) y) = transp (S:real^N^N) ** S` THEN
  ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_MATRIX_MUL; INVERTIBLE_TRANSP] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\M:real^N^N. (J:real^N^N) ** M ** transp J`) THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_LID] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; INVERTIBLE_TRANSP; MATRIX_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC]);;

let RFA_PB_FT = prove
 (`!(h:real^N->real^N) (tf:real^N->(num->real^N)->real) y (S:real^N^N) l.
     linear(frechet_derivative h (at y))
     ==> ltpullback h tf y (rfa_ft S l) =
         tf (h y) (rfa_ft (S ** transp(matrix(frechet_derivative h (at y)))) l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltpullback; rfa_ft] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let RFA_BASE_ARR_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' (G:real^N->real^N^N) G' y (S:real^N^N).
     metric_field U G' /\ diffeomorphism_on U' U h h' /\ y IN U' /\
     (!z. z IN U' ==> G z = mpullback h G' z)
     ==> rfa_ric_a G y S =
         rfa_ric_a G' (h y) (S ** transp(matrix(frechet_derivative h (at y)))) /\
         rfa_dr_a G y S =
         rfa_dr_a G' (h y) (S ** transp(matrix(frechet_derivative h (at y)))) /\
         rfa_ddr_a G y S =
         rfa_ddr_a G' (h y) (S ** transp(matrix(frechet_derivative h (at y))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G:real^N->real^N^N`; `G':real^N->real^N^N`]
         RFA_PB_LRIC2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `rfa_sf 2 U (lric2 (G':real^N->real^N^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFA_SF_LRIC2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G:real^N->real^N^N`; `G':real^N->real^N^N`;
                 `lric2 (G:real^N->real^N^N)`; `lric2 (G':real^N->real^N^N)`]
         RFA_PB_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `rfa_sf 3 U (lnabla 2 (G':real^N->real^N^N) (lric2 G'))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G':real^N->real^N^N`; `lric2 (G':real^N->real^N^N)`]
           RFA_SF_LNABLA) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`3`; `U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G:real^N->real^N^N`; `G':real^N->real^N^N`;
                 `lnabla 2 (G:real^N->real^N^N) (lric2 G)`;
                 `lnabla 2 (G':real^N->real^N^N) (lric2 G')`]
         RFA_PB_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[rfa_ric_a; rfa_dr_a; rfa_ddr_a; FUN_EQ_THM] THEN
  ASM_SIMP_TAC[RFA_PB_FT]);;

let RFA_HPSD_CC_PULLBACK = prove
 (`!U U' V (h:real^3->real^3) h' (G:real^3->real^3^3) G' y s t alpha beta.
     metric_field U G' /\ diffeomorphism_on U' U h h' /\ y IN U' /\
     (!z. z IN U' ==> G z = mpullback h G' z) /\ metric_field V G /\ y IN V
     ==> (rfa_hpsd_cc G s t alpha beta y <=> rfa_hpsd_cc G' s t alpha beta (h y)) /\
         (rfa_hpd_cc G s t alpha beta y <=> rfa_hpd_cc G' s t alpha beta (h y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `U':real^3->bool`; `h:real^3->real^3`;
                 `h':real^3->real^3`; `G:real^3->real^3^3`; `G':real^3->real^3^3`;
                 `y:real^3`; `S:real^3^3`] RFA_PB_FRAME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `U':real^3->bool`; `h:real^3->real^3`;
                 `h':real^3->real^3`; `G:real^3->real^3^3`; `G':real^3->real^3^3`;
                 `y:real^3`; `S:real^3^3`] RFA_BASE_ARR_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `U':real^3->bool`; `h:real^3->real^3`;
                 `h':real^3->real^3`; `y:real^3`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                 `s:real`; `t:real`; `alpha:real`; `beta:real`] RFA_HPSD_CC_FR) THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                 `s:real`; `t:real`; `alpha:real`; `beta:real`] RFA_HPD_CC_FR) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G':real^3->real^3^3`; `(h:real^3->real^3) y`;
                 `(S:real^3^3) ** transp(matrix(frechet_derivative (h:real^3->real^3) (at y)))`;
                 `s:real`; `t:real`; `alpha:real`; `beta:real`] RFA_HPSD_CC_FR) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G':real^3->real^3^3`; `(h:real^3->real^3) y`;
                 `(S:real^3^3) ** transp(matrix(frechet_derivative (h:real^3->real^3) (at y)))`;
                 `s:real`; `t:real`; `alpha:real`; `beta:real`] RFA_HPD_CC_FR) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[]);;

let RFA_HPSD_CC_CHARTS = prove
 (`!top atlas (g:A->real^3^3) c c' x s t alpha beta.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     c IN atlas /\ c' IN atlas /\ x IN FST c /\ x IN FST c'
     ==> (rfa_hpsd_cc (metric_local atlas c g) s t alpha beta (SND c x) <=>
          rfa_hpsd_cc (metric_local atlas c' g) s t alpha beta (SND c' x)) /\
         (rfa_hpd_cc (metric_local atlas c g) s t alpha beta (SND c x) <=>
          rfa_hpd_cc (metric_local atlas c' g) s t alpha beta (SND c' x))`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `U:A->bool`; `phi:A->real^3`;
                       `V:A->bool`; `psi:A->real^3`; `x:A`; `s:real`; `t:real`;
                       `alpha:real`; `beta:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ open_in top (V:A->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `U:A->bool`; `phi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `V:A->bool`; `psi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^3) (U INTER V)) /\
                open(IMAGE (psi:A->real^3) (U INTER V))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THENL
     [EXISTS_TAC `U:A->bool`; EXISTS_TAC `V:A->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (psi:A->real^3) (U INTER V)`; `IMAGE (phi:A->real^3) (U INTER V)`;
                 `IMAGE (phi:A->real^3) U`;
                 `chart_trans (U:A->bool,phi:A->real^3) (V,psi)`;
                 `chart_trans (V:A->bool,psi:A->real^3) (U,phi)`;
                 `metric_local atlas (U:A->bool,phi:A->real^3) (g:A->real^3^3)`;
                 `metric_local atlas (V:A->bool,psi:A->real^3) (g:A->real^3^3)`;
                 `(phi:A->real^3) x`; `s:real`; `t:real`; `alpha:real`; `beta:real`]
         RFA_HPSD_CC_PULLBACK) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `IMAGE (psi:A->real^3) V` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool)
                                       (g:A->real^3^3)` THEN
        REWRITE_TAC[riemannian_metric] THEN
        DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^3)`) THEN
        ASM_REWRITE_TAC[FST; SND];
        SET_TAC[]];
      MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x':A` THEN STRIP_TAC THEN
      MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[IN_INTER];
      UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool)
                                     (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN
      ASM_REWRITE_TAC[FST; SND];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`; `V:A->bool`; `psi:A->real^3`; `x:A`]
         CHART_TRANS_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* ========================================================================= *)
(* The quadratic structure.  rfa_pol F: F on real^6 is the                   *)
(* quadratic form of its polarization coefficients; closure rules; the       *)
(* parametrization of (antisymmetric A, w) by v in real^6 (rfa_avec,         *)
(* rfa_wvec) and the polarization of rfa_zv (RFA_ZV_POL).                   *)
(* ========================================================================= *)

let rfa_pol = new_definition
 `rfa_pol (ff:real^6->real) <=>
    !v. ff v = sum(1..6) (\i. sum(1..6) (\j. v$i * v$j *
                (ff(basis i + basis j) - ff(basis i - basis j)) / &4))`;;

let RFA_POL_ADD = prove
 (`!ff gg. rfa_pol ff /\ rfa_pol gg ==> rfa_pol (\v. ff v + gg v)`,
  REWRITE_TAC[rfa_pol] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

let RFA_POL_CMUL = prove
 (`!ff c. rfa_pol ff ==> rfa_pol (\v. c * ff v)`,
  REWRITE_TAC[rfa_pol] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

let RFA_POL_ZERO = prove
 (`rfa_pol (\v:real^6. &0)`,
  REWRITE_TAC[rfa_pol; REAL_SUB_REFL; real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0]);;

let RFA_POL_SUM = prove
 (`!(ff:num->real^6->real) m n.
     (!k. m <= k /\ k <= n ==> rfa_pol (ff k)) ==> rfa_pol (\v. sum(m..n) (\k. ff k v))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN ASM_CASES_TAC `m = 0` THEN
    ASM_REWRITE_TAC[RFA_POL_ZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_REFL; ETA_AX];
    DISCH_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN
    ASM_CASES_TAC `m <= SUC n` THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC RFA_POL_ADD THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_ARITH_TAC;
        REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC]]);;

let RFA_ADDITIVE_VSUM = prove
 (`!(f:real^6->real).
     (!x y. f(x + y) = f x + f y) /\ (!c x. f(c % x) = c * f x)
     ==> !n g. f(vsum(1..n) g) = sum(1..n) (\i. f(g i))`,
  GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[VSUM_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG; ARITH_EQ] THEN REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `vec 0:real^6`]) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; REAL_MUL_LZERO];
    ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`]]);;

let RFA_DIMINDEX_6 = prove
 (`dimindex (:6) = 6`,
  DIMINDEX_TAC THEN REFL_TAC);;

let RFA_ADDITIVE_EXPAND = prove
 (`!(f:real^6->real).
     (!x y. f(x + y) = f x + f y) /\ (!c x. f(c % x) = c * f x)
     ==> !v. f v = sum(1..6) (\i. v$i * f(basis i))`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  REWRITE_TAC[RFA_DIMINDEX_6] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RFA_ADDITIVE_VSUM th]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT2 th]));;

let RFA_POL_MUL = prove
 (`!(f:real^6->real) g.
     (!x y. f(x + y) = f x + f y) /\ (!c x. f(c % x) = c * f x) /\
     (!x y. g(x + y) = g x + g y) /\ (!c x. g(c % x) = c * g x)
     ==> rfa_pol (\v. f v * g v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[rfa_pol] THEN GEN_TAC THEN
  SUBGOAL_THEN `!x y:real^6. f(x - y) = f x - (f:real^6->real) y /\ g(x - y) = g x - g y`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[VECTOR_SUB; VECTOR_NEG_MINUS1] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `f:real^6->real` RFA_ADDITIVE_EXPAND) THEN
  MP_TAC(SPEC `g:real^6->real` RFA_ADDITIVE_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun ge -> DISCH_THEN(fun fe ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ge] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [fe])) THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  SUBGOAL_THEN
   `!i j. (v:real^6)$i * v$j *
          (((f:real^6->real)(basis i) + f(basis j)) * ((g:real^6->real)(basis i) + g(basis j)) -
           (f(basis i) - f(basis j)) * (g(basis i) - g(basis j))) / &4 =
          inv(&2) * (v$i * f(basis i)) * (v$j * g(basis j)) +
          inv(&2) * (v$j * f(basis j)) * (v$i * g(basis i))`
  (fun th -> REWRITE_TAC[th]) THENL [REPEAT GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN
  SUBGOAL_THEN
   `sum(1..6) (\i. sum(1..6) (\j. ((v:real^6)$j * (f:real^6->real)(basis j)) *
                                  v$i * (g:real^6->real)(basis i))) =
    sum(1..6) (\i. (v$i * f(basis i)) * sum(1..6) (\j. v$j * g(basis j)))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[SUM_LMUL];
    REWRITE_TAC[REAL_ARITH `inv(&2) * x + inv(&2) * x = x`]]);;

(* The parametrization of (antisymmetric A, w) by v in real^6. *)

let rfa_avec = new_definition
 `rfa_avec (v:real^6) = (lambda i j.
     if i = 1 /\ j = 2 then v$1 else if i = 2 /\ j = 1 then --(v$1) else
     if i = 1 /\ j = 3 then v$2 else if i = 3 /\ j = 1 then --(v$2) else
     if i = 2 /\ j = 3 then v$3 else if i = 3 /\ j = 2 then --(v$3) else &0):real^3^3`;;

let rfa_wvec = new_definition
 `rfa_wvec (v:real^6) = (lambda i. v$(i + 3)):real^3`;;

let rfa_zv = new_definition
 `rfa_zv (G:real^3->real^3^3) s t alpha beta y v =
    rfa_zcc G s t alpha beta y (rfa_avec v) (rfa_wvec v)`;;

let RFA_AVEC_ADD = prove
 (`!x y:real^6. rfa_avec(x + y) = rfa_avec x + rfa_avec y`,
  SIMP_TAC[rfa_avec; CART_EQ; LAMBDA_BETA; MATRIX_ADD_COMPONENT; VECTOR_ADD_COMPONENT;
           DIMINDEX_3; RFA_DIMINDEX_6; ARITH] THEN
  REPEAT STRIP_TAC THEN RFA_INDEX_CASES_TAC [`i:num`; `i':num`] THEN
  REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC);;

let RFA_AVEC_CMUL = prove
 (`!c (x:real^6). rfa_avec(c % x) = c %% rfa_avec x`,
  SIMP_TAC[rfa_avec; CART_EQ; LAMBDA_BETA; MATRIX_CMUL_COMPONENT; VECTOR_MUL_COMPONENT;
           DIMINDEX_3; RFA_DIMINDEX_6; ARITH] THEN
  REPEAT STRIP_TAC THEN RFA_INDEX_CASES_TAC [`i:num`; `i':num`] THEN
  REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC);;

let RFA_WVEC_ADD = prove
 (`!x y:real^6. rfa_wvec(x + y) = rfa_wvec x + rfa_wvec y`,
  SIMP_TAC[rfa_wvec; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT; DIMINDEX_3;
           RFA_DIMINDEX_6; ARITH_RULE `1 <= i /\ i <= 3 ==> 1 <= i + 3 /\ i + 3 <= 6`]);;

let RFA_WVEC_CMUL = prove
 (`!c (x:real^6). rfa_wvec(c % x) = c % rfa_wvec x`,
  SIMP_TAC[rfa_wvec; CART_EQ; LAMBDA_BETA; VECTOR_MUL_COMPONENT; DIMINDEX_3;
           RFA_DIMINDEX_6; ARITH_RULE `1 <= i /\ i <= 3 ==> 1 <= i + 3 /\ i + 3 <= 6`]);;

let RFA_AVEC_ANTI = prove
 (`!v:real^6. transp(rfa_avec v) = --(rfa_avec v)`,
  SIMP_TAC[rfa_avec; CART_EQ; LAMBDA_BETA; TRANSP_COMPONENT; MATRIX_NEG_COMPONENT;
           DIMINDEX_3] THEN
  REPEAT STRIP_TAC THEN RFA_INDEX_CASES_TAC [`i:num`; `i':num`] THEN
  ASM_SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

let RFA_UV_LIN = prove
 (`!(S:real^3^3) a b.
     (!x y. rfa_marr (S ** rfa_avec(x + y) ** transp S) a b =
            rfa_marr (S ** rfa_avec x ** transp S) a b +
            rfa_marr (S ** rfa_avec y ** transp S) a b) /\
     (!c x. rfa_marr (S ** rfa_avec(c % x) ** transp S) a b =
            c * rfa_marr (S ** rfa_avec x ** transp S) a b)`,
  REWRITE_TAC[RFA_AVEC_ADD; RFA_AVEC_CMUL; MATRIX_ADD_LDISTRIB; MATRIX_ADD_RDISTRIB;
              MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; rfa_marr] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT; DIMINDEX_3] THEN REAL_ARITH_TAC);;

let RFA_WV_LIN = prove
 (`!(S:real^3^3) a.
     (!x y. rfa_varr (S ** rfa_wvec(x + y)) a =
            rfa_varr (S ** rfa_wvec x) a + rfa_varr (S ** rfa_wvec y) a) /\
     (!c x. rfa_varr (S ** rfa_wvec(c % x)) a = c * rfa_varr (S ** rfa_wvec x) a)`,
  REWRITE_TAC[RFA_WVEC_ADD; RFA_WVEC_CMUL; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              MATRIX_VECTOR_MUL_RMUL; rfa_varr] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; DIMINDEX_3] THEN REAL_ARITH_TAC);;

let rec RFA_POL_TAC (asl, w) =
  (FIRST [MATCH_MP_TAC RFA_POL_ADD THEN CONJ_TAC THEN RFA_POL_TAC;
          MATCH_MP_TAC RFA_POL_SUM THEN REPEAT STRIP_TAC THEN BETA_TAC THEN RFA_POL_TAC;
          MATCH_MP_TAC RFA_POL_CMUL THEN RFA_POL_TAC;
          MATCH_MP_TAC RFA_POL_MUL THEN BETA_TAC THEN REWRITE_TAC[RFA_UV_LIN; RFA_WV_LIN]])
  (asl, w);;

let RFA_ZV_POL = prove
 (`!U (G:real^3->real^3^3) y s t alpha beta.
     metric_field U G /\ y IN U ==> rfa_pol (rfa_zv G s t alpha beta y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `rfa_zv (G:real^3->real^3^3) s t alpha beta y =
    \v. rfa_hza (rfa_ric_a G y S) (rfa_dr_a G y S) (rfa_ddr_a G y S) (t - s) alpha beta
                (rfa_marr (S ** rfa_avec v ** transp S)) (rfa_varr (S ** rfa_wvec v))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rfa_zv] THEN GEN_TAC THEN MATCH_MP_TAC RFA_ZCC_FRAME_ARR THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_hza; rfa_hz] THEN RFA_POL_TAC);;

(* ========================================================================= *)
(* Joint smoothness in (t,y) of the coordinate form along a                  *)
(* chart Ricci flow (RFA_ZCC_SMOOTH), through the heat-defect calculus: the  *)
(* identity 4-field family (RFA_HEAT_IFLD), the perturbed families and       *)
(* RFA_HEAT_QUAD.                                                           *)
(* ========================================================================= *)

let RFA_SIGI_PERMUTES = prove
 (`(\m. if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m) permutes 1..4`,
  ACCEPT_TAC(RFA_PERMUTES_PROVE
   `(\m. if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m) permutes 1..4`));;

let RFA_HEAT_IFLD = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G ==> ?H. rfa_heat 4 U a b G (\t. rfa_ifld (G t)) H`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  (fun g ->
    let flow = ASSUME `lricci_flow U a b (G:real->real^N->real^N^N)` in
    let thg = MATCH_MP RFA_HEAT_METRIC flow in
    let thgg = RFA_HPROD_RULE flow thg thg in
    let th1 = RFA_HPERM_RULE flow `swap(2,3)` RFA_SWAP23_PERMUTES4 thgg in
    let th2 = RFA_HPERM_RULE flow
      `\m. if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m`
      RFA_SIGI_PERMUTES thgg in
    let th = RFA_HLIN_RULE flow `inv(&2)` `--inv(&2)` th1 th2 in
    let args = rfa_heat_args th in
    (EXISTS_TAC (el 6 args) THEN MATCH_MP_TAC RFA_HEAT_CONG THEN
     MAP_EVERY EXISTS_TAC [el 5 args; el 6 args] THEN ASM_REWRITE_TAC[th]) g) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_IFLD_LTPROD] THEN REAL_ARITH_TAC);;

let RFA_ZCC_SMOOTH = prove
 (`!U a b (G:real->real^3->real^3^3) s alpha beta A w.
     lricci_flow U a b G /\ s <= a
     ==> smooth_map_on (interval(lift a,lift b) PCROSS U)
           (\z. lift(rfa_zcc (G(drop(fstcart z))) s (drop(fstcart z)) alpha beta
                             (sndcart z) A w))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `HI:real->real^3->(num->real^3)->real` o
              MATCH_MP RFA_HEAT_IFLD) THEN
  (fun g ->
    let flow = ASSUME `lricci_flow U a b (G:real->real^3->real^3^3)` in
    let thM = MATCH_MP RFA_HEAT_HM3 (CONJ flow (ASSUME `s <= a:real`)) in
    let thg = MATCH_MP RFA_HEAT_METRIC flow in
    let thMh = RFA_HLIN_RULE flow `&1` `beta:real` thM thg in
    let thP = MATCH_MP RFA_HEAT_HP flow in
    let thR = MATCH_MP RFA_HEAT_RM3 flow in
    let thI = ASSUME `rfa_heat 4 U a b (G:real->real^3->real^3^3) (\t. rfa_ifld (G t)) HI` in
    let thRh = RFA_HLIN_RULE flow `&1` `alpha:real` thR thI in
    let sfu = REWRITE_RULE[rfa_sf] (ISPECL [`U:real^3->bool`; `A:real^3^3`] RFA_SF_CF2)
    and sfw = REWRITE_RULE[rfa_sf] (ISPECL [`U:real^3->bool`; `w:real^3`] RFA_SF_CF1) in
    let thU = MATCH_MP (ISPEC `2` RFA_HEAT_STATIC) (CONJ flow sfu)
    and thW = MATCH_MP (ISPEC `1` RFA_HEAT_STATIC) (CONJ flow sfw) in
    let thQ = MATCH_MP RFA_HEAT_QUAD
                (end_itlist CONJ [flow; thMh; thP; thRh; thU; thW]) in
    let sm = CONJUNCT1(CONJUNCT2(REWRITE_RULE[rfa_heat] thQ)) in
    MP_TAC (SPEC `(\m. vec 0):num->real^3` sm) g) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SMOOTH_MAP_ON_EQ) THEN
  REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_zcc] THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[ETA_AX]);;

(* ========================================================================= *)
(* Positive (semi)definiteness through rfa_zv (RFA_HPD_ZV,                   *)
(* RFA_HPSD_ZV) and the affine dependence on the perturbation parameters    *)
(* (RFA_HZA_SPLIT, RFA_ZCC_AFFINE).                                          *)
(* ========================================================================= *)

let RFA_VECTOR6_COMPONENT = prove
 (`!x1 x2 x3 x4 x5 x6 i.
     1 <= i /\ i <= 6
     ==> (vector[x1;x2;x3;x4;x5;x6]:real^6)$i =
         EL (i - 1) [x1;x2;x3;x4;x5;x6]`,
  SIMP_TAC[vector; LAMBDA_BETA; RFA_DIMINDEX_6]);;

let RFA_ANTI_ENTRIES = prove
 (`!A:real^3^3.
     transp A = --A
     ==> A$1$1 = &0 /\ A$2$2 = &0 /\ A$3$3 = &0 /\
         A$2$1 = --(A$1$2) /\ A$3$1 = --(A$1$3) /\ A$3$2 = --(A$2$3)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 ==> (A:real^3^3)$j$i = --(A$i$j)`
  (fun th -> MP_TAC(SPECL [`1`;`1`] th) THEN MP_TAC(SPECL [`2`;`2`] th) THEN
             MP_TAC(SPECL [`3`;`3`] th) THEN MP_TAC(SPECL [`1`;`2`] th) THEN
             MP_TAC(SPECL [`1`;`3`] th) THEN MP_TAC(SPECL [`2`;`3`] th)) THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\M:real^3^3. M$i$j`) THEN
    ASM_SIMP_TAC[TRANSP_COMPONENT; MATRIX_NEG_COMPONENT; DIMINDEX_3];
    REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC]);;

let RFA_AVEC_SURJ = prove
 (`!(A:real^3^3) (w:real^3).
     transp A = --A
     ==> rfa_avec(vector[A$1$2; A$1$3; A$2$3; w$1; w$2; w$3]) = A /\
         rfa_wvec(vector[A$1$2; A$1$3; A$2$3; w$1; w$2; w$3]) = w`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP RFA_ANTI_ENTRIES) THEN
  SIMP_TAC[rfa_avec; rfa_wvec; CART_EQ; LAMBDA_BETA; DIMINDEX_3] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [RFA_INDEX_CASES_TAC [`i:num`; `i':num`]; RFA_INDEX_CASES_TAC [`i:num`]] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SIMP_TAC[RFA_VECTOR6_COMPONENT; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(CHANGED_TAC(REWRITE_TAC[EL_CONS] THEN CONV_TAC NUM_REDUCE_CONV THEN
                     REWRITE_TAC[])) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG]);;

let RFA_VEC6_EQ_TAC =
  SIMP_TAC[CART_EQ; RFA_DIMINDEX_6] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  SIMP_TAC[RFA_VECTOR6_COMPONENT; VEC_COMPONENT; RFA_DIMINDEX_6; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(CHANGED_TAC(REWRITE_TAC[EL_CONS] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]));;

let RFA_AVEC_RECOVER = prove
 (`!v:real^6. vector[(rfa_avec v)$1$2; (rfa_avec v)$1$3; (rfa_avec v)$2$3;
                     (rfa_wvec v)$1; (rfa_wvec v)$2; (rfa_wvec v)$3] = v`,
  GEN_TAC THEN RFA_VEC6_EQ_TAC THEN
  SIMP_TAC[rfa_avec; rfa_wvec; LAMBDA_BETA; DIMINDEX_3; ARITH]);;

let RFA_AVEC_ZERO = prove
 (`!v:real^6. rfa_avec v = mat 0 /\ rfa_wvec v = vec 0 <=> v = vec 0`,
  GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM RFA_AVEC_RECOVER] THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[MAT_COMPONENT; VEC_COMPONENT; DIMINDEX_3; ARITH] THEN RFA_VEC6_EQ_TAC;
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[rfa_avec; rfa_wvec; CART_EQ; LAMBDA_BETA; MAT_COMPONENT; VEC_COMPONENT;
             DIMINDEX_3; RFA_DIMINDEX_6;
             ARITH_RULE `1 <= i /\ i <= 3 ==> 1 <= i + 3 /\ i + 3 <= 6`] THEN
    REWRITE_TAC[REAL_NEG_0; COND_ID]]);;

let RFA_HPD_ZV = prove
 (`!(G:real^3->real^3^3) s t alpha beta y.
     rfa_hpd_cc G s t alpha beta y <=>
     !v. ~(v = vec 0) ==> &0 < rfa_zv G s t alpha beta y v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_hpd_cc; rfa_zv] THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[RFA_AVEC_ANTI; RFA_AVEC_ZERO];
    MAP_EVERY X_GEN_TAC [`A:real^3^3`; `w:real^3`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`A:real^3^3`; `w:real^3`] RFA_AVEC_SURJ) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vector[(A:real^3^3)$1$2; A$1$3; A$2$3;
                                        (w:real^3)$1; w$2; w$3]:real^6`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    DISCH_TAC THEN UNDISCH_TAC `~((A:real^3^3) = mat 0 /\ (w:real^3) = vec 0)` THEN
    REWRITE_TAC[] THEN ASM_MESON_TAC[RFA_AVEC_ZERO]]);;

let RFA_HPSD_ZV = prove
 (`!(G:real^3->real^3^3) s t alpha beta y.
     rfa_hpsd_cc G s t alpha beta y <=> !v. &0 <= rfa_zv G s t alpha beta y v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_hpsd_cc; rfa_zv] THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[RFA_AVEC_ANTI];
    MAP_EVERY X_GEN_TAC [`A:real^3^3`; `w:real^3`] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`A:real^3^3`; `w:real^3`] RFA_AVEC_SURJ) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vector[(A:real^3^3)$1$2; A$1$3; A$2$3;
                                        (w:real^3)$1; w$2; w$3]:real^6`) THEN
    ASM_REWRITE_TAC[]]);;

let RFA_HZA_SPLIT = prove
 (`!ric dr ddr tau alpha beta (u:num->num->real) (w:num->real).
     rfa_hza ric dr ddr tau alpha beta u w =
     rfa_hza ric dr ddr tau (&0) (&0) u w +
     alpha * sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
               rfa_i4 a b c d * u a b * u d c)))) +
     beta * sum(1..3) (\a. sum(1..3) (\b. rfa_kd a b * w a * w b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_hza; rfa_hz] THEN
  REWRITE_TAC[REAL_ARITH `(m + b * k) * x * y = m * x * y + b * (k * x * y)`] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN
  REWRITE_TAC[REAL_MUL_LZERO; SUM_0; REAL_ADD_RID] THEN REAL_ARITH_TAC);;

let RFA_ZCC_AFFINE = prove
 (`!U (G:real^3->real^3^3) y s t alpha beta A w.
     metric_field U G /\ y IN U
     ==> rfa_zcc G s t alpha beta y A w =
         rfa_zcc G s t (&0) (&0) y A w +
         alpha * (rfa_zcc G s t (&1) (&0) y A w - rfa_zcc G s t (&0) (&0) y A w) +
         beta * (rfa_zcc G s t (&0) (&1) y A w - rfa_zcc G s t (&0) (&0) y A w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
         RFA_ZCC_FRAME_ARR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ONCE_REWRITE_TAC[RFA_HZA_SPLIT] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The 6x6 matrix of the quadratic (rfa_zm), its symmetry and                *)
(* RFA_HPD_ZM (positive definiteness = positive_definite rfa_zm), and the    *)
(* openness of positive definiteness along a chart flow with continuous      *)
(* perturbation parameters (RFA_HPD_OPEN), from POSITIVE_DEFINITE_NEARBY.    *)
(* ========================================================================= *)

let rfa_zm = new_definition
 `rfa_zm (G:real^3->real^3^3) s t alpha beta y =
    (lambda i j. (rfa_zv G s t alpha beta y (basis i + basis j) -
                  rfa_zv G s t alpha beta y (basis i - basis j)) / &4):real^6^6`;;

let RFA_POL_NEG = prove
 (`!ff:real^6->real. rfa_pol ff ==> !x. ff(--x) = ff x`,
  REWRITE_TAC[rfa_pol] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

let RFA_ZV_ZM = prove
 (`!U (G:real^3->real^3^3) y s t alpha beta.
     metric_field U G /\ y IN U
     ==> (!v. rfa_zv G s t alpha beta y v = v dot (rfa_zm G s t alpha beta y ** v)) /\
         symmetric_matrix (rfa_zm G s t alpha beta y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RFA_ZV_POL) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SPECL [`s:real`; `t:real`; `alpha:real`; `beta:real`]) THEN
  CONJ_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [REWRITE_RULE[rfa_pol] th]) THEN
    SIMP_TAC[dot; matrix_vector_mul; rfa_zm; LAMBDA_BETA; RFA_DIMINDEX_6] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
    SIMP_TAC[symmetric_matrix; CART_EQ; TRANSP_COMPONENT; rfa_zm; LAMBDA_BETA;
             RFA_DIMINDEX_6] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `basis i' - basis i:real^6 = --(basis i - basis i')` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RFA_POL_NEG th]) THEN
    REWRITE_TAC[VECTOR_ADD_SYM]]);;

let RFA_HPD_ZM = prove
 (`!U (G:real^3->real^3^3) y s t alpha beta.
     metric_field U G /\ y IN U
     ==> (rfa_hpd_cc G s t alpha beta y <=>
          positive_definite (rfa_zm G s t alpha beta y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `s:real`; `t:real`;
                 `alpha:real`; `beta:real`] RFA_ZV_ZM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[RFA_HPD_ZV; positive_definite]);;

let RFA_PD_OPEN_GEN = prove
 (`!(Q:real^M->real^6^6) D z1.
     z1 IN D /\ (!z. z IN D ==> symmetric_matrix (Q z)) /\
     (!i j. 1 <= i /\ i <= 6 /\ 1 <= j /\ j <= 6
            ==> (\z. lift((Q z)$i$j)) continuous (at z1 within D)) /\
     positive_definite (Q z1)
     ==> ?d. &0 < d /\ !z. z IN D /\ norm(z - z1) < d ==> positive_definite (Q z)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC o MATCH_MP POSITIVE_DEFINITE_NEARBY) THEN
  SUBGOAL_THEN
   `(\z. lift(sum(1..6) (\i. sum(1..6) (\j. abs(((Q:real^M->real^6^6) z)$i$j -
                                                (Q z1)$i$j)))))
    continuous (at z1 within D)`
  MP_TAC THENL
   [REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_LIFT_ABS THEN REWRITE_TAC[LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN REWRITE_TAC[CONTINUOUS_CONST] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_within] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; SUM_0; DIST_LIFT; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^M` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[dist] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> abs b < e ==> a < e`) THEN
  MP_TAC(ISPEC `(Q:real^M->real^6^6) z - Q z1` ONORM_LE_MATRIX_COMPONENT_SUM) THEN
  MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[RFA_DIMINDEX_6] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[MATRIX_SUB_COMPONENT; RFA_DIMINDEX_6]);;

let RFA_PCROSS_INTERVAL_MEM = prove
 (`!a b (U:real^N->bool) (z:real^(1,N)finite_sum).
     z IN interval(lift a,lift b) PCROSS U
     ==> a < drop(fstcart z) /\ drop(fstcart z) < b /\ sndcart z IN U`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[]);;

let RFA_ZV_CONT = prove
 (`!U a b (G:real->real^3->real^3^3) s (al:real^(1,3)finite_sum->real) be z1 v.
     lricci_flow U a b G /\ s <= a /\ z1 IN interval(lift a,lift b) PCROSS U /\
     (\z. lift(al z)) continuous (at z1 within interval(lift a,lift b) PCROSS U) /\
     (\z. lift(be z)) continuous (at z1 within interval(lift a,lift b) PCROSS U)
     ==> (\z. lift(rfa_zv (G(drop(fstcart z))) s (drop(fstcart z)) (al z) (be z)
                          (sndcart z) v))
         continuous (at z1 within interval(lift a,lift b) PCROSS U)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  ABBREV_TAC `D = interval(lift a,lift b) PCROSS (U:real^3->bool)` THEN
  SUBGOAL_THEN
   `!alpha beta. (\z:real^(1,3)finite_sum.
                    lift(rfa_zcc ((G:real->real^3->real^3^3)(drop(fstcart z))) s
                                 (drop(fstcart z)) alpha beta
                                 (sndcart z) (rfa_avec (v:real^6)) (rfa_wvec v)))
                 continuous (at z1 within D)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`;
                   `s:real`; `alpha:real`; `beta:real`; `rfa_avec v`; `rfa_wvec v`]
           RFA_ZCC_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
  EXISTS_TAC
   `\z:real^(1,3)finite_sum.
        lift(rfa_zcc ((G:real->real^3->real^3^3)(drop(fstcart z))) s (drop(fstcart z)) (&0) (&0) (sndcart z)
                     (rfa_avec (v:real^6)) (rfa_wvec v)) +
        (al:real^(1,3)finite_sum->real) z % (lift(rfa_zcc (G(drop(fstcart z))) s (drop(fstcart z)) (&1) (&0) (sndcart z)
                             (rfa_avec v) (rfa_wvec v)) -
                lift(rfa_zcc (G(drop(fstcart z))) s (drop(fstcart z)) (&0) (&0) (sndcart z)
                             (rfa_avec v) (rfa_wvec v))) +
        (be:real^(1,3)finite_sum->real) z % (lift(rfa_zcc (G(drop(fstcart z))) s (drop(fstcart z)) (&0) (&1) (sndcart z)
                             (rfa_avec v) (rfa_wvec v)) -
                lift(rfa_zcc (G(drop(fstcart z))) s (drop(fstcart z)) (&0) (&0) (sndcart z)
                             (rfa_avec v) (rfa_wvec v)))` THEN
  EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^(1,3)finite_sum` THEN EXPAND_TAC "D" THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_PCROSS_INTERVAL_MEM) THEN
    REWRITE_TAC[rfa_zv] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) (drop(fstcart(z:real^(1,3)finite_sum)))`;
                   `sndcart(z:real^(1,3)finite_sum)`; `s:real`; `drop(fstcart(z:real^(1,3)finite_sum))`;
                   `(al:real^(1,3)finite_sum->real) z`; `(be:real^(1,3)finite_sum->real) z`;
                   `rfa_avec v`; `rfa_wvec v`] RFA_ZCC_AFFINE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_SUB; LIFT_CMUL];
    MATCH_MP_TAC CONTINUOUS_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_MUL THEN ASM_REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN ASM_REWRITE_TAC[]]);;

let RFA_HPD_OPEN = prove
 (`!U a b (G:real->real^3->real^3^3) s (al:real^(1,3)finite_sum->real) be z1.
     lricci_flow U a b G /\ s <= a /\ z1 IN interval(lift a,lift b) PCROSS U /\
     (\z. lift(al z)) continuous (at z1 within interval(lift a,lift b) PCROSS U) /\
     (\z. lift(be z)) continuous (at z1 within interval(lift a,lift b) PCROSS U) /\
     rfa_hpd_cc (G(drop(fstcart z1))) s (drop(fstcart z1)) (al z1) (be z1) (sndcart z1)
     ==> ?d. &0 < d /\
             !z. z IN interval(lift a,lift b) PCROSS U /\ norm(z - z1) < d
                 ==> rfa_hpd_cc (G(drop(fstcart z))) s (drop(fstcart z)) (al z) (be z)
                                (sndcart z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  SUBGOAL_THEN
   `!z:real^(1,3)finite_sum. z IN interval(lift a,lift b) PCROSS (U:real^3->bool)
        ==> (rfa_hpd_cc ((G:real->real^3->real^3^3)(drop(fstcart z))) s (drop(fstcart z)) ((al:real^(1,3)finite_sum->real) z) ((be:real^(1,3)finite_sum->real) z) (sndcart z) <=>
             positive_definite
               (rfa_zm (G(drop(fstcart z))) s (drop(fstcart z)) (al z) (be z) (sndcart z))) /\
            symmetric_matrix
               (rfa_zm (G(drop(fstcart z))) s (drop(fstcart z)) (al z) (be z) (sndcart z))`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(1,3)finite_sum` THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_PCROSS_INTERVAL_MEM) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_HPD_ZM THEN EXISTS_TAC `U:real^3->bool` THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) (drop(fstcart(z:real^(1,3)finite_sum)))`;
                     `sndcart(z:real^(1,3)finite_sum)`; `s:real`; `drop(fstcart(z:real^(1,3)finite_sum))`;
                     `(al:real^(1,3)finite_sum->real) z`;
                     `(be:real^(1,3)finite_sum->real) z`] RFA_ZV_ZM) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. rfa_zm ((G:real->real^3->real^3^3)(drop(fstcart z))) s (drop(fstcart z))
                ((al:real^(1,3)finite_sum->real) z) ((be:real^(1,3)finite_sum->real) z)
                (sndcart z)`;
    `interval(lift a,lift b) PCROSS (U:real^3->bool)`; `z1:real^(1,3)finite_sum`]
   RFA_PD_OPEN_GEN) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REPEAT STRIP_TAC THEN SIMP_TAC[rfa_zm; LAMBDA_BETA; RFA_DIMINDEX_6] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; RFA_DIMINDEX_6] THEN
    REWRITE_TAC[REAL_ARITH `x / &4 = inv(&4) * x`; LIFT_CMUL; LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_CMUL THEN MATCH_MP_TAC CONTINUOUS_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC RFA_ZV_CONT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[]);;

let RFA_HPSD_CLOSED = prove
 (`!U a b (G:real->real^3->real^3^3) s (al:real^(1,3)finite_sum->real) be z1.
     lricci_flow U a b G /\ s <= a /\ z1 IN interval(lift a,lift b) PCROSS U /\
     (\z. lift(al z)) continuous (at z1 within interval(lift a,lift b) PCROSS U) /\
     (\z. lift(be z)) continuous (at z1 within interval(lift a,lift b) PCROSS U) /\
     (!e. &0 < e
          ==> ?z. z IN interval(lift a,lift b) PCROSS U /\ norm(z - z1) < e /\
                  rfa_hpsd_cc (G(drop(fstcart z))) s (drop(fstcart z)) (al z) (be z)
                              (sndcart z))
     ==> rfa_hpsd_cc (G(drop(fstcart z1))) s (drop(fstcart z1)) (al z1) (be z1)
                     (sndcart z1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[RFA_HPSD_ZV] THEN
  X_GEN_TAC `v:real^6` THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`; `s:real`;
                 `al:real^(1,3)finite_sum->real`; `be:real^(1,3)finite_sum->real`;
                 `z1:real^(1,3)finite_sum`; `v:real^6`] RFA_ZV_CONT) THEN
  ASM_REWRITE_TAC[continuous_within] THEN
  DISCH_THEN(MP_TAC o SPEC
    `--(rfa_zv ((G:real->real^3->real^3^3) (drop(fstcart(z1:real^(1,3)finite_sum)))) s
        (drop(fstcart z1)) ((al:real^(1,3)finite_sum->real) z1)
        ((be:real^(1,3)finite_sum->real) z1) (sndcart z1) v)`) THEN
  ASM_REWRITE_TAC[REAL_NEG_GT0] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^(1,3)finite_sum` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(1,3)finite_sum`) THEN
  ASM_REWRITE_TAC[dist; DIST_LIFT] THEN
  UNDISCH_TAC `rfa_hpsd_cc ((G:real->real^3->real^3^3) (drop(fstcart(z:real^(1,3)finite_sum))))
                 s (drop(fstcart z)) ((al:real^(1,3)finite_sum->real) z)
                 ((be:real^(1,3)finite_sum->real) z) (sndcart z)` THEN
  REWRITE_TAC[RFA_HPSD_ZV] THEN DISCH_THEN(MP_TAC o SPEC `v:real^6`) THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Unit pc_rfa_hext: the touching point of the perturbed Harnack quadratic.  *)
(* Extension fields with a prescribed 1-jet at a point, the heat defect of   *)
(* the perturbed quadratic at the point in a frame                           *)
(* (RFA_HARNACK_DEFECT_3D_PERT), and the time and space tests at the         *)
(* touching point (RFA_TOUCH_INEQ).                                          *)
(* ========================================================================= *)

needs "src/pc_rfa_hpsd.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Extension fields with a prescribed 1-jet at a point y0.                   *)
(* rfa_xw G y0 w0: the 1-form w0 corrected so that nabla W = 0 at y0;       *)
(* rfa_xu G y0 A0 w0 tau: the 2-form A0 (antisymmetric) corrected so that   *)
(* nabla U at y0 is rfa_xform, the tensor form of CLN (10.59).  Values,     *)
(* antisymmetry, smoothness and covariant derivatives at y0.                *)
(* ========================================================================= *)

let rfa_xform = new_definition
 `rfa_xform (G:real^N->real^N^N) y0 (w0:real^N) tau (h:real^N) (a:real^N) (b:real^N) =
    inv(&2) * (lricci G y0 h a * (w0 dot b) - lricci G y0 h b * (w0 dot a)) +
    inv(&4 * tau) * ((h dot (G y0 ** a)) * (w0 dot b) - (h dot (G y0 ** b)) * (w0 dot a))`;;

let rfa_xw = new_definition
 `rfa_xw (G:real^N->real^N^N) (y0:real^N) (w0:real^N) =
    \(z:real^N) (u:num->real^N). w0 dot (u 1) + w0 dot christoffel G y0 (z - y0) (u 1)`;;

let rfa_xu = new_definition
 `rfa_xu (G:real^N->real^N^N) (y0:real^N) (A0:real^N^N) (w0:real^N) tau =
    \(z:real^N) (u:num->real^N).
      u 1 dot (A0 ** u 2) + christoffel G y0 (z - y0) (u 1) dot (A0 ** u 2) +
      u 1 dot (A0 ** christoffel G y0 (z - y0) (u 2)) +
      rfa_xform G y0 w0 tau (z - y0) (u 1) (u 2)`;;

let RFA_AFFINE_FDERIV = prove
 (`!(L:real^N->real^1) c (y0:real^N) y.
     linear L ==> frechet_derivative (\z. c + L(z - y0)) (at y) = L`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  SUBGOAL_THEN `(\z. c + (L:real^N->real^1)(z - y0)) = (\z. c + (L z - L y0))`
  SUBST1_TAC THENL [ASM_SIMP_TAC[FUN_EQ_THM; LINEAR_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN `(L:real^N->real^1) = \h. vec 0 + (L h - vec 0)`
  (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_LID; VECTOR_SUB_RZERO]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
  ASM_SIMP_TAC[REWRITE_RULE[ETA_AX] (ISPEC `L:real^N->real^1` HAS_DERIVATIVE_LINEAR);
               HAS_DERIVATIVE_CONST]);;

let RFA_CHRISTOFFEL_ZERO = prove
 (`!U (G:real^N->real^N^N) y v.
     metric_field U G /\ y IN U ==> christoffel G y (vec 0) v = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0) THEN REWRITE_TAC[]);;

let RFA_LRICCI_ZERO = prove
 (`!U (G:real^N->real^N^N) y v.
     metric_field U G /\ y IN U ==> lricci G y (vec 0) v = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0) THEN BETA_TAC THEN
  REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; DROP_VEC]);;

let RFA_XW_AT = prove
 (`!U (G:real^N->real^N^N) y0 w0 u.
     metric_field U G /\ y0 IN U ==> rfa_xw G y0 w0 y0 u = w0 dot (u 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_xw; VECTOR_SUB_REFL] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `(u:num->real^N) 1`]
         RFA_CHRISTOFFEL_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DOT_RZERO; REAL_ADD_RID]);;

let RFA_XU_AT = prove
 (`!U (G:real^N->real^N^N) y0 A0 w0 tau u.
     metric_field U G /\ y0 IN U ==> rfa_xu G y0 A0 w0 tau y0 u = u 1 dot (A0 ** u 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_xu; rfa_xform; VECTOR_SUB_REFL] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`] RFA_CHRISTOFFEL_ZERO) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`] RFA_LRICCI_ZERO) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[DOT_LZERO; DOT_RZERO; MATRIX_VECTOR_MUL_RZERO] THEN REAL_ARITH_TAC);;

let RFA_CHRISTOFFEL_LIN = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> (!x x' v. christoffel G y (x + x') v = christoffel G y x v + christoffel G y x' v) /\
         (!c x v. christoffel G y (c % x) v = c % christoffel G y x v) /\
         (!x v v'. christoffel G y x (v + v') = christoffel G y x v + christoffel G y x v') /\
         (!c x v. christoffel G y x (c % v) = c % christoffel G y x v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LRG_CHRISTOFFEL_LINEAR) THEN
  SIMP_TAC[linear]);;

let RFA_LRICCI_LIN = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> (!x x' v. lricci G y (x + x') v = lricci G y x v + lricci G y x' v) /\
         (!c x v. lricci G y (c % x) v = c * lricci G y x v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP LRG_LRICCI_LINEAR) THEN
  REWRITE_TAC[linear; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN SIMP_TAC[]);;

let RFA_XW_NABLA = prove
 (`!U (G:real^N->real^N^N) y0 w0 u.
     metric_field U G /\ y0 IN U ==> lnabla 1 G (rfa_xw G y0 w0) y0 u = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla; SUM_1; ARITH] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `w0:real^N`]
         RFA_XW_AT) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `(\z. lift(rfa_xw (G:real^N->real^N^N) y0 w0 z u)) =
    (\z. lift(w0 dot u 1) + (\h. lift(w0 dot christoffel G y0 h (u 1))) (z - y0))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rfa_xw; LIFT_ADD]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\h. lift((w0:real^N) dot christoffel (G:real^N->real^N^N) y0 h (u 1))`;
                 `lift((w0:real^N) dot u 1)`; `y0:real^N`; `y0:real^N`]
         RFA_AFFINE_FDERIV) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`]
           RFA_CHRISTOFFEL_LIN) THEN
    ASM_SIMP_TAC[linear; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP; ARITH] THEN REAL_ARITH_TAC);;

let RFA_XU_NABLA = prove
 (`!U (G:real^N->real^N^N) y0 A0 w0 tau u.
     metric_field U G /\ y0 IN U
     ==> lnabla 2 G (rfa_xu G y0 A0 w0 tau) y0 u = rfa_xform G y0 w0 tau (u 3) (u 1) (u 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla; SUM_2; ARITH] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `A0:real^N^N`;
                 `w0:real^N`; `tau:real`] RFA_XU_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `(\z. lift(rfa_xu (G:real^N->real^N^N) y0 A0 w0 tau z u)) =
    (\z. lift(u 1 dot (A0 ** u 2)) +
         (\h. lift(christoffel G y0 h (u 1) dot (A0 ** u 2) +
                   u 1 dot (A0 ** christoffel G y0 h (u 2)) +
                   rfa_xform G y0 w0 tau h (u 1) (u 2))) (z - y0))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rfa_xu; GSYM LIFT_ADD] THEN REPEAT GEN_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\h. lift(christoffel (G:real^N->real^N^N) y0 h (u 1) dot (A0 ** u 2) +
                           u 1 dot (A0 ** christoffel G y0 h (u 2)) +
                           rfa_xform G y0 w0 tau h (u 1) (u 2))`;
                 `lift(u 1 dot ((A0:real^N^N) ** u 2))`; `y0:real^N`; `y0:real^N`]
         RFA_AFFINE_FDERIV) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`]
           RFA_CHRISTOFFEL_LIN) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`] RFA_LRICCI_LIN) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[linear; rfa_xform; DOT_LADD; DOT_LMUL; DOT_RADD; DOT_RMUL;
                    MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                    GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP; ARITH] THEN REAL_ARITH_TAC);;

let RFA_AFFINE_SMOOTH = prove
 (`!s (L:real^N->real^1) c (y0:real^N).
     open s /\ linear L ==> smooth_map_on s (\z. c + L(z - y0))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
  SUBGOAL_THEN `(\z. (L:real^N->real^1)(z - y0)) = L o (\z. z - y0)` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

let RFA_ANTI_DOT = prove
 (`!(A:real^N^N) x y. transp A = --A ==> x dot (A ** y) = --(y dot (A ** x))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LNEG; DOT_LNEG] THEN REWRITE_TAC[DOT_SYM]);;

let RFA_XU_ANTI = prove
 (`!(G:real^N->real^N^N) y0 A0 w0 tau z a b.
     transp A0 = --A0
     ==> rfa_xu G y0 A0 w0 tau z (\m. if m = 1 then a else b) =
         --(rfa_xu G y0 A0 w0 tau z (\m. if m = 1 then b else a))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_xu; rfa_xform; ARITH] THEN
  FIRST_ASSUM(fun th -> let lem = MATCH_MP RFA_ANTI_DOT th in
    MP_TAC(ISPECL [`b:real^N`; `a:real^N`] lem) THEN
    MP_TAC(ISPECL [`christoffel (G:real^N->real^N^N) y0 (z - y0) b`; `a:real^N`] lem) THEN
    MP_TAC(ISPECL [`b:real^N`; `christoffel (G:real^N->real^N^N) y0 (z - y0) a`] lem)) THEN
  REAL_ARITH_TAC);;

let RFA_SF_XW = prove
 (`!U (G:real^N->real^N^N) y0 w0.
     metric_field U G /\ y0 IN U ==> rfa_sf 1 U (rfa_xw G y0 w0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`]
         RFA_CHRISTOFFEL_LIN) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[rfa_sf; ltensor_field] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[rfa_xw] THEN ASM_SIMP_TAC[LE_REFL; ARITH];
    SUBGOAL_THEN `i = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[rfa_xw; linear; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    SUBGOAL_THEN
     `(\z. lift(rfa_xw (G:real^N->real^N^N) y0 w0 z u)) =
      (\z. lift(w0 dot u 1) + (\h. lift(w0 dot christoffel G y0 h (u 1))) (z - y0))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; rfa_xw; LIFT_ADD]; ALL_TAC] THEN
    MATCH_MP_TAC RFA_AFFINE_SMOOTH THEN
    ASM_SIMP_TAC[linear; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL]]);;

let RFA_SF_XU = prove
 (`!U (G:real^N->real^N^N) y0 A0 w0 tau.
     metric_field U G /\ y0 IN U ==> rfa_sf 2 U (rfa_xu G y0 A0 w0 tau)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`]
         RFA_CHRISTOFFEL_LIN) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`] RFA_LRICCI_LIN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `!z b c. lricci (G:real^N->real^N^N) y0 z (b + c) = lricci G y0 z b + lricci G y0 z c /\
                        !k. lricci G y0 z (k % b) = k * lricci G y0 z b`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`] LRG_LRICCI_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[linear; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_sf; ltensor_field] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[rfa_xu] THEN
    SUBGOAL_THEN `(u:num->real^N) 1 = u' 1 /\ u 2 = u' 2` (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM_REWRITE_TAC[rfa_xu; rfa_xform; linear; ARITH; DOT_LADD; DOT_LMUL; DOT_RADD; DOT_RMUL;
                    MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                    GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    SUBGOAL_THEN
     `(\z. lift(rfa_xu (G:real^N->real^N^N) y0 A0 w0 tau z u)) =
      (\z. lift(u 1 dot (A0 ** u 2)) +
           (\h. lift(christoffel G y0 h (u 1) dot (A0 ** u 2) +
                     u 1 dot (A0 ** christoffel G y0 h (u 2)) +
                     rfa_xform G y0 w0 tau h (u 1) (u 2))) (z - y0))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; rfa_xu; GSYM LIFT_ADD] THEN REPEAT GEN_TAC THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC RFA_AFFINE_SMOOTH THEN
    ASM_REWRITE_TAC[linear; rfa_xform; DOT_LADD; DOT_LMUL; DOT_RADD; DOT_RMUL;
                    MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                    GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The heat defect of the perturbed Harnack quadratic at a                   *)
(* point in a frame (RFA_HARNACK_DEFECT_3D_PERT): M + pb g with defect      *)
(* HM + pb' g, Rm + pa I with defect HRm + pa' I; the identity of           *)
(* RFA_HARNACK_DEFECT_3D plus pa'|U|^2 + 2 pa (<HU,U> - |nabla U|^2) +       *)
(* pb'|W|^2 + 2 pb <HW,W>.  Same engine proof as RFA_HDEF_DERIVE.  The      *)
(* 1-jet (10.59) is stated with g(e_e, e_i) instead of the Kronecker delta of  *)
(* RFA_HARNACK_DEFECT_3D, so that it holds at every index (frame vectors     *)
(* with an index outside 1..3 are 0); with the delta it fails there when     *)
(* W is not 0.                                                               *)
(* ========================================================================= *)

let RFA_HDEFP_DERIVE asm w =
  let hs = map ASSUME (conjuncts asm) in
  let h k = el k hs in
  let h_flow = h 0 and h_sa = h 1 and h_at = h 2 and h_tb = h 3 and h_y = h 4
  and h_invS = h 5 and h_frame = h 6 and h_sfU = h 7 and h_sfHU = h 8 and h_sfW = h 9
  and h_sfHW = h 10 and h_anti = h 11 and h_dW = h 12 and h_dU = h 13 in
  let b_flow = MATCH_MP LRG_FLOW_BASIC h_flow in
  let b_open = CONJUNCT1 b_flow in
  let mf = MP (SPEC `t:real` (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 b_flow))))))
              (CONJ h_at h_tb) in
  let sfat th = MATCH_MP RFA_HEAT_SF_AT (CONJ th (CONJ b_open (CONJ h_at h_tb))) in
  let s_HM = sfat (MATCH_MP RFA_HEAT_HM3 (CONJ h_flow h_sa)) in
  let s_HP = sfat (MATCH_MP RFA_HEAT_HP h_flow) in
  let s_RM = sfat (MATCH_MP RFA_HEAT_RM3 h_flow) in
  let s_bases = map BETA_RULE (CONJUNCTS s_HM @ CONJUNCTS s_HP @ CONJUNCTS s_RM) @
                [h_sfU; h_sfHU; h_sfW; h_sfHW; MATCH_MP RFA_SF_IFLD mf] in
  let saved = (!rfa_sf_bases, !rfa_sf_unfolds, !rfa_lnf_unfolds, !rfa_frv_unfolds, !rfa_mp_hook) in
  Hashtbl.reset rfa_sf_cache; Hashtbl.reset rfa_lnf_cache;
  Hashtbl.reset rfa_atom_cache; Hashtbl.reset rfa_mp_cache;
  (* phase 1: the skeleton, with M, P, R and their defects as atoms *)
  rfa_sf_bases := s_bases @ [RFA_SF_LRIC2; RFA_SF_LMETRIC2; RFA_SF_LRM4; RFA_SF_SC; RFA_SF_HRIC];
  rfa_sf_unfolds := [RFA_HDDR_LAMBDA; RFA_HDR_LAMBDA; rfa_hprod; RFA_HRIC3_LAMBDA; rfa_ric2sq;
                     rfa_nric2; RFA_SC_CONTR; RFA_HHRIC3_LAMBDA; rfa_hsc; rfa_hnric2; rfa_hric2sq];
  rfa_lnf_unfolds := [RFA_IFLD_LTPROD];
  rfa_frv_unfolds := [rfa_hqform; rfa_hprod];
  let p1 = RFA_FRV_CONV mf h_y h_frame (lhs w) in
  let p1 = CONV_RULE (RAND_CONV (REWRITE_CONV[h_dW; h_dU; REAL_MUL_LZERO; REAL_MUL_RZERO;
             REAL_ADD_LID; REAL_ADD_RID; REAL_SUB_RZERO; SUM_0])) p1 in
  (* phase 2: the atoms at symbolic frame indices *)
  Hashtbl.reset rfa_lnf_cache;
  rfa_lnf_unfolds := [RFA_SC_CONTR; RFA_EQON_HRIC_3D; RFA_EQON_LRM4_3D; RFA_HRIC3_LAMBDA;
                      rfa_ric2sq; rfa_nric2; RFA_HDR_LAMBDA; RFA_EQON_HP; RFA_IFLD_LTPROD];
  rfa_frv_unfolds := [RFA_EQON_HHM; RFA_EQON_HM; RFA_HDDR_LAMBDA; RFA_HHRIC3_LAMBDA; rfa_hsc;
                      rfa_hnric2; rfa_hric2sq; RFA_EQON_HP; RFA_HDR_LAMBDA; RFA_EQON_HRIC_3D;
                      RFA_EQON_LRM4_3D; RFA_HRIC3_LAMBDA; rfa_ric2sq; rfa_nric2; RFA_SC_CONTR;
                      rfa_ifld];
  let evc tm = RFA_FRV_CONV mf h_y h_frame tm in
  let comps = map evc
   [`rfa_hhM s t ((G:real->real^3->real^3^3) t) y (rfa_ft (S:real^3^3) [i1; i2])`;
    `rfa_hM s t ((G:real->real^3->real^3^3) t) y (rfa_ft (S:real^3^3) [i1; i2])`;
    `rfa_hdr ((G:real->real^3->real^3^3) t) y (rfa_ft (S:real^3^3) [i1; i2; i3])`;
    `rfa_hP ((G:real->real^3->real^3^3) t) y (rfa_ft (S:real^3^3) [i1; i2; i3])`;
    `lnabla 3 ((G:real->real^3->real^3^3) t) (rfa_hP (G t)) y (rfa_ft (S:real^3^3) [i1; i2; i3; i4])`;
    `lrm4 ((G:real->real^3->real^3^3) t) y (rfa_ft (S:real^3^3) [i1; i2; i3; i4])`;
    `lnabla 4 ((G:real->real^3->real^3^3) t) (lrm4 (G t)) y (rfa_ft (S:real^3^3) [i1; i2; i3; i4; i5])`;
    `rfa_hric ((G:real->real^3->real^3^3) t) y (rfa_ft (S:real^3^3) [i1; i2])`;
    `rfa_ifld ((G:real->real^3->real^3^3) t) y (rfa_ft (S:real^3^3) [i1; i2; i3; i4])`] in
  let comp_list = map (fun th -> (rator(rator(lhs(concl th))), th)) comps in
  (* phase 3: the normalizer hook *)
  let ric_f = `lric2 ((G:real->real^3->real^3^3) t)`
  and dr_f = `lnabla 2 ((G:real->real^3->real^3^3) t) (lric2 (G t))`
  and ddr_f = `lnabla 3 ((G:real->real^3->real^3^3) t) (lnabla 2 (G t) (lric2 (G t)))`
  and met_f = `lmetric2 ((G:real->real^3->real^3^3) t)`
  and u_f = `Uf:real^3->(num->real^3)->real`
  and yv = `y:real^3` and uu = `U:real^3->bool` and gt = `(G:real->real^3->real^3^3) t`
  and sv = `S:real^3^3`
  and ivars = [`i1:num`; `i2:num`; `i3:num`; `i4:num`; `i5:num`] in
  let nm = mk_small_numeral in
  let h_mfy = CONJ mf h_y and h_all = end_itlist CONJ [mf; h_y; h_invS; h_frame] in
  let met_th i j =
    MP (REWRITE_RULE[DIMINDEX_3; ARITH] (ISPECL [uu; gt; yv; sv; nm i; nm j] RFA_FT_METRIC)) h_all in
  let dest_fatom tm = match (try Some(dest_comb(rator tm), rand tm) with Failure _ -> None) with
      Some((f, yy), wt) when yy = yv && rfa_is_ft wt ->
        (f, map dest_small_numeral (dest_list (rand wt)))
    | _ -> failwith "dest_fatom" in
  let pivots_on = ref false and pivot_tbl = ref [] in
  let pivot tm = if !pivots_on then assoc tm !pivot_tbl else failwith "canonical" in
  let anti_th i j = ISPECL [nm i; nm j] h_anti in
  let hook_raw tm =
    let f, l = dest_fatom tm in
    if f = met_f then (match l with [i;j] -> met_th i j | _ -> failwith "met")
    else if f = ric_f then
      (match l with
         [i;j] when i > j -> MP (ISPECL [uu; gt; yv; sv; nm i; nm j] RFA_FT_RIC_SYM) h_mfy
       | _ -> failwith "canonical")
    else if f = dr_f then
      (match l with
         [i;j;k] when i > j -> MP (ISPECL [uu; gt; yv; sv; nm i; nm j; nm k] RFA_FT_DRIC_SYM) h_mfy
       | _ -> pivot tm)
    else if f = ddr_f then
      (match l with
         [i;j;k;l4] when i > j ->
           MP (ISPECL [uu; gt; yv; sv; nm i; nm j; nm k; nm l4] RFA_FT_DDRIC_SYM) h_mfy
       | [i;j;k;l4] when k > l4 ->
           CONV_RULE (REWR_CONV REAL_EQ_SUB_RADD)
             (MP (ISPECL [uu; gt; yv; sv; nm i; nm j; nm k; nm l4] RFA_FT_RICCI_ID) h_all)
       | _ -> pivot tm)
    else if f = u_f then
      (match l with
         [i;j] when i > j -> anti_th i j
       | [i;j] when i = j -> MP (ISPEC tm RFA_UDIAG) (anti_th i j)
       | _ -> failwith "canonical")
    else
      let th = assoc f comp_list in
      INST (map2 (fun n v -> (nm n, v)) l (fst(chop_list (length l) ivars))) th in
  rfa_mp_hook := (fun tm -> try hook_raw tm with Failure s -> failwith s
                                               | Not_found -> failwith "rfa_mp_hook"
                                               | Bind ->  (* Candle: CakeML raises Bind where OCaml raises Match_failure *) failwith "rfa_mp_hook");
  Hashtbl.reset rfa_mp_cache;
  (* the contracted Bianchi identity at [j] and its derivative at [j; l] *)
  let mk_ft l = list_mk_comb(`rfa_ft:real^3^3->num list->num->real^3`,
                             [sv; mk_list(map nm l, `:num`)]) in
  let mk_at f l = mk_comb(mk_comb(f, yv), mk_ft l) in
  let bth = MATCH_MP RFA_CBIANCHI_EQON mf in
  let openU = CONJUNCT1(REWRITE_RULE[metric_field] mf) in
  let bth1 = MATCH_MP (ISPECL [`1`; uu; gt] RFA_EQON_LNABLA) (CONJ openU bth) in
  let app_rel eqth l =
    let a = rand(rator(concl eqth)) and b = rand(concl eqth) in
    let th = MP (ISPECL [uu; a; b; yv; mk_ft l] RFA_EQON_APP) (CONJ eqth h_y) in
    let th1 = CONV_RULE (RAND_CONV (TRY_CONV (RATOR_CONV BETA_CONV THENC BETA_CONV))) th in
    CONV_RULE (BINOP_CONV (RFA_FRV_CONV mf h_y h_frame)) th1 in
  let piv_ddr (j,l) =
    if j = l then mk_at ddr_f [j;j;j;j] else
    let c = 6 - j - l in mk_at ddr_f [min c j; max c j; min c l; max c l] in
  let pv1 = map (fun j -> let p = mk_at dr_f [j;j;j] in
                          (p, RFA_SOLVE_PIVOT (app_rel bth [j]) p)) (1--3) in
  let pv2 = map (fun (j,l) -> let p = piv_ddr (j,l) in
                              (p, RFA_SOLVE_PIVOT (app_rel bth1 [j;l]) p))
                (allpairs (fun j l -> (j,l)) (1--3) (1--3)) in
  pivot_tbl := pv1 @ pv2; pivots_on := true;
  Hashtbl.reset rfa_mp_cache;
  (* phase 4: normal forms of both sides *)
  let nfL = RFA_MPOLY (rand(concl p1)) in
  let rhs_unf = (REWRITE_CONV[rfa_hj] THENC DEPTH_CONV BETA_CONV THENC
                 REWRITE_CONV[h_dU]) (rhs w) in
  let nfR = RFA_MPOLY (rand(concl rhs_unf)) in
  let (b1, b2, b3, b4, b5) = saved in
  rfa_sf_bases := b1; rfa_sf_unfolds := b2; rfa_lnf_unfolds := b3; rfa_frv_unfolds := b4;
  rfa_mp_hook := b5;
  Hashtbl.reset rfa_sf_cache; Hashtbl.reset rfa_lnf_cache;
  Hashtbl.reset rfa_atom_cache; Hashtbl.reset rfa_mp_cache;
  if not (aconv (rand(concl nfL)) (rand(concl nfR))) then failwith "RFA_HDEFP_DERIVE: normal forms"
  else itlist PROVE_HYP (CONJUNCTS (ASSUME asm))
         (TRANS p1 (TRANS nfL (SYM (TRANS rhs_unf nfR))));;


let RFA_HARNACK_DEFECT_3D_PERT = prove
 (`!U a b (G:real->real^3->real^3^3) s t y (S:real^3^3) Uf HUf Wf HWf (u:num->real^3) pa pa' pb pb'.
     lricci_flow U a b G /\ s <= a /\ a < t /\ t < b /\ y IN U /\
     invertible S /\ matrix_inv(G t y) = transp S ** S /\
     rfa_sf 2 U Uf /\ rfa_sf 2 U HUf /\ rfa_sf 1 U Wf /\ rfa_sf 1 U HWf /\
     (!i j. Uf y (rfa_ft S [i; j]) = --(Uf y (rfa_ft S [j; i]))) /\
     (!w. lnabla 1 (G t) Wf y w = &0) /\
     (!i j e. lnabla 2 (G t) Uf y (rfa_ft S [i; j; e]) =
              inv(&2) * (lric2 (G t) y (rfa_ft S [e; i]) * Wf y (rfa_ft S [j]) -
                         lric2 (G t) y (rfa_ft S [e; j]) * Wf y (rfa_ft S [i])) +
              inv(&4 * (t - s)) * (lmetric2 (G t) y (rfa_ft S [e; i]) * Wf y (rfa_ft S [j]) -
                                   lmetric2 (G t) y (rfa_ft S [e; j]) * Wf y (rfa_ft S [i])))
     ==> rfa_hqform (G t) (\y u. rfa_hM s t (G t) y u + pb * lmetric2 (G t) y u)
           (\y u. rfa_hhM s t (G t) y u + pb' * lmetric2 (G t) y u) (rfa_hP (G t))
           (\y u. rfa_hdr (G t) y (\m. if m = 1 then u 2 else if m = 2 then u 3 else u 1) -
                  rfa_hdr (G t) y (\m. if m = 1 then u 1 else if m = 2 then u 3 else u 2))
           (\y u. lrm4 (G t) y u + pa * rfa_ifld (G t) y u)
           (\y u. rfa_h3 (G t) (rfa_hric (G t)) y u + pa' * rfa_ifld (G t) y u)
           Uf HUf Wf HWf y u =
         rfa_hj 3 (\a b c d. lrm4 (G t) y (rfa_ft S [a; b; d; c]))
                  (\a b c. rfa_hP (G t) y (rfa_ft S [a; b; c]))
                  (\a b. rfa_hM s t (G t) y (rfa_ft S [a; b]))
                  (\a b. Uf y (rfa_ft S [a; b])) (\a. Wf y (rfa_ft S [a])) +
         sum(1..3) (\a. sum(1..3) (\b.
           (sum(1..3) (\c. rfa_hP (G t) y (rfa_ft S [a; b; c]) * Wf y (rfa_ft S [c])) +
            sum(1..3) (\c. sum(1..3) (\d. lrm4 (G t) y (rfa_ft S [a; b; c; d]) *
                                         Uf y (rfa_ft S [c; d])))) pow 2)) -
         &2 / (t - s) *
         (sum(1..3) (\a. sum(1..3) (\b. rfa_hM s t (G t) y (rfa_ft S [a; b]) *
                                      Wf y (rfa_ft S [a]) * Wf y (rfa_ft S [b]))) +
          sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. rfa_hP (G t) y (rfa_ft S [a; b; c]) *
                                      Uf y (rfa_ft S [a; b]) * Wf y (rfa_ft S [c]))))) +
         &2 * (sum(1..3) (\a. sum(1..3) (\b. rfa_hM s t (G t) y (rfa_ft S [a; b]) *
                                            HWf y (rfa_ft S [a]) * Wf y (rfa_ft S [b]))) +
               sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. rfa_hP (G t) y (rfa_ft S [a; b; c]) *
                    (HUf y (rfa_ft S [a; b]) * Wf y (rfa_ft S [c]) +
                     Uf y (rfa_ft S [a; b]) * HWf y (rfa_ft S [c]))))) +
               sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. sum(1..3) (\d.
                    lrm4 (G t) y (rfa_ft S [a; b; c; d]) * HUf y (rfa_ft S [a; b]) *
                    Uf y (rfa_ft S [c; d])))))) +
         pa' * sum(1..3) (\a. sum(1..3) (\b. Uf y (rfa_ft S [a; b]) pow 2)) +
         &2 * pa * (sum(1..3) (\a. sum(1..3) (\b. HUf y (rfa_ft S [a; b]) *
                                                  Uf y (rfa_ft S [a; b]))) -
                    sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\e.
                      lnabla 2 (G t) Uf y (rfa_ft S [a; b; e]) pow 2)))) +
         pb' * sum(1..3) (\a. Wf y (rfa_ft S [a]) pow 2) +
         &2 * pb * sum(1..3) (\a. HWf y (rfa_ft S [a]) * Wf y (rfa_ft S [a]))`,
  REPEAT GEN_TAC THEN
  W(fun (_, w) -> let a, c = dest_imp w in ACCEPT_TAC (DISCH a (RFA_HDEFP_DERIVE a c))));;

(* ========================================================================= *)
(* The norm N = |U|^2 + |W|^2 of a pair of fields (rfa_nrm2)                 *)
(* and its heat-defect form (rfa_hnrm2); in a frame at a point: the value    *)
(* (RFA_NRM2_FRAME), the defect with nabla W = 0 and nabla U antisymmetric  *)
(* (RFA_NRM2_DEFECT_3D) and the gradient (RFA_NRM2_GRAD_3D).                *)
(* ========================================================================= *)

let rfa_nrm2 = new_definition
 `rfa_nrm2 (G:real^N->real^N^N) (Uf:real^N->(num->real^N)->real) Wf =
    \y u. ltcontr G (ltcontr G (ltperm (swap(2,3)) (ltprod 2 Uf Uf))) y u +
          ltcontr G (ltprod 1 Wf Wf) y u`;;

let rfa_hnrm2 = new_definition
 `rfa_hnrm2 (G:real^N->real^N^N) (Uf:real^N->(num->real^N)->real) HUf Wf HWf =
    \y u. ltcontr G (ltcontr G (ltperm (swap(2,3)) (rfa_hprod 2 2 G Uf HUf Uf HUf))) y u +
          ltcontr G (rfa_hprod 1 1 G Wf HWf Wf HWf) y u`;;

let RFA_XGRAD_ZERO_L = prove
 (`!p q (G:real^N->real^N^N) B. rfa_xgrad p q G (\y u. &0) B = (\y u. &0)`,
  REWRITE_TAC[FUN_EQ_THM; rfa_xgrad; RFA_LNABLA_ZERO; REAL_MUL_LZERO; REAL_MUL_RZERO;
              SUM_0]);;

let RFA_XGRAD_ZERO_R = prove
 (`!p q (G:real^N->real^N^N) A. rfa_xgrad p q G A (\y u. &0) = (\y u. &0)`,
  REWRITE_TAC[FUN_EQ_THM; rfa_xgrad; RFA_LNABLA_ZERO; REAL_MUL_LZERO; REAL_MUL_RZERO;
              SUM_0]);;

let RFA_NRM2_DERIVE mode asm w =
  let hs = map ASSUME (conjuncts asm) in
  let h k = el k hs in
  let mf = h 0 and h_y = h 1 and h_invS = h 2 and h_frame = h 3 in
  let sfs = [h 4; h 5; h 6; h 7] in
  let h_anti = h 8 in
  let saved = RFA_ENGINE_SAVE () in
  RFA_ENGINE_RESET ();
  rfa_sf_bases := sfs @ [MATCH_MP RFA_SF_IFLD mf; RFA_SF_LRIC2; RFA_SF_LMETRIC2; RFA_SF_LRM4];
  rfa_sf_unfolds := [rfa_hprod];
  rfa_lnf_unfolds := [rfa_nrm2];
  rfa_frv_unfolds := [rfa_nrm2; rfa_hnrm2; rfa_hprod];
  let gg = rand(concl mf) and uu = rand(rator(concl mf)) in
  let yv = rand(rator(concl h_y)) and sv = rand(rand(concl h_frame)) in
  let met_f = mk_comb(`lmetric2:(real^3->real^3^3)->real^3->(num->real^3)->real`, gg) in
  let u_f = lhs(snd(strip_forall(concl h_anti))) in
  let u_f = rator(rator u_f) in
  let h_danti = h 10 in
  let du_f = rator(rator(lhs(snd(strip_forall(concl h_danti))))) in
  let h_all = end_itlist CONJ [mf; h_y; h_invS; h_frame] in
  let nm = mk_small_numeral in
  let hook tm =
    match (try Some(dest_comb(rator tm), rand tm) with Failure _ -> None) with
      Some((f, yy), wt) when yy = yv && rfa_is_ft wt ->
        let l = map dest_small_numeral (dest_list (rand wt)) in
        if f = met_f then
          (match l with [i;j] -> MP (REWRITE_RULE[DIMINDEX_3; ARITH]
                                   (ISPECL [uu; gg; yv; sv; nm i; nm j] RFA_FT_METRIC)) h_all
           | _ -> failwith "met")
        else if f = u_f then
          (match l with
             [i;j] when i > j -> ISPECL [nm i; nm j] h_anti
           | [i;j] when i = j -> MP (ISPEC tm RFA_UDIAG) (ISPECL [nm i; nm j] h_anti)
           | _ -> failwith "canonical")
        else if f = du_f then
          (match l with
             [i;j;e] when i > j -> ISPECL [nm i; nm j; nm e] h_danti
           | [i;j;e] when i = j -> MP (ISPEC tm RFA_UDIAG) (ISPECL [nm i; nm j; nm e] h_danti)
           | _ -> failwith "canonical")
        else failwith "atom"
    | _ -> failwith "atom" in
  rfa_mp_hook := (fun t -> try hook t with Failure s -> failwith s
                                          | Bind ->  (* Candle: CakeML raises Bind where OCaml raises Match_failure *) failwith "atom");
  let res =
    try
      let th1 = RFA_FRV_CONV mf h_y h_frame (lhs w) in
      let th1 = if mode = 0 then CONV_RULE (RAND_CONV (REWRITE_CONV[h 9])) th1 else th1 in
      let nfl = TRANS th1 (RFA_MPOLY (rand(concl th1))) in
      let th2 = (REWRITE_CONV[] THENC DEPTH_CONV BETA_CONV) (rhs w) in
      let nfr = TRANS th2 (RFA_MPOLY (rand(concl th2))) in
      if aconv (rand(concl nfl)) (rand(concl nfr)) then TRANS nfl (SYM nfr)
      else failwith "RFA_NRM2_DERIVE: normal forms"
    with e -> (RFA_ENGINE_RESTORE saved; raise e) in
  RFA_ENGINE_RESTORE saved;
  itlist PROVE_HYP (CONJUNCTS (ASSUME asm)) res;;

let RFA_NRM2_DEFECT_3D = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) Uf HUf Wf HWf (u:num->real^3).
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     rfa_sf 2 U Uf /\ rfa_sf 2 U HUf /\ rfa_sf 1 U Wf /\ rfa_sf 1 U HWf /\
     (!i j. Uf y (rfa_ft S [i; j]) = --(Uf y (rfa_ft S [j; i]))) /\
     (!w. lnabla 1 G Wf y w = &0) /\
     (!i j e. lnabla 2 G Uf y (rfa_ft S [i; j; e]) = --(lnabla 2 G Uf y (rfa_ft S [j; i; e])))
     ==> rfa_hnrm2 G Uf HUf Wf HWf y u =
         &2 * (sum(1..3) (\a. sum(1..3) (\b. HUf y (rfa_ft S [a; b]) * Uf y (rfa_ft S [a; b]))) -
               sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\e.
                 lnabla 2 G Uf y (rfa_ft S [a; b; e]) pow 2)))) +
         &2 * sum(1..3) (\a. HWf y (rfa_ft S [a]) * Wf y (rfa_ft S [a]))`,
  REPEAT GEN_TAC THEN
  W(fun (_, w) -> let a, c = dest_imp w in ACCEPT_TAC (DISCH a (RFA_NRM2_DERIVE 0 a c))));;

let RFA_NRM2_FRAME = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) Uf HUf Wf HWf (u:num->real^3).
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     rfa_sf 2 U Uf /\ rfa_sf 2 U HUf /\ rfa_sf 1 U Wf /\ rfa_sf 1 U HWf /\
     (!i j. Uf y (rfa_ft S [i; j]) = --(Uf y (rfa_ft S [j; i]))) /\
     (!w. lnabla 1 G Wf y w = &0) /\
     (!i j e. lnabla 2 G Uf y (rfa_ft S [i; j; e]) = --(lnabla 2 G Uf y (rfa_ft S [j; i; e])))
     ==> rfa_nrm2 G Uf Wf y u =
         sum(1..3) (\a. sum(1..3) (\b. Uf y (rfa_ft S [a; b]) pow 2)) +
         sum(1..3) (\a. Wf y (rfa_ft S [a]) pow 2)`,
  REPEAT GEN_TAC THEN
  W(fun (_, w) -> let a, c = dest_imp w in ACCEPT_TAC (DISCH a (RFA_NRM2_DERIVE 1 a c))));;

let RFA_NRM2_GRAD_3D = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) Uf HUf Wf HWf e.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     rfa_sf 2 U Uf /\ rfa_sf 2 U HUf /\ rfa_sf 1 U Wf /\ rfa_sf 1 U HWf /\
     (!i j. Uf y (rfa_ft S [i; j]) = --(Uf y (rfa_ft S [j; i]))) /\
     (!w. lnabla 1 G Wf y w = &0) /\
     (!i j e. lnabla 2 G Uf y (rfa_ft S [i; j; e]) = --(lnabla 2 G Uf y (rfa_ft S [j; i; e]))) /\
     1 <= e /\ e <= 3
     ==> lnabla 0 G (rfa_nrm2 G Uf Wf) y (rfa_ft S [e]) =
         &2 * sum(1..3) (\a. sum(1..3) (\b. Uf y (rfa_ft S [a; b]) *
                                          lnabla 2 G Uf y (rfa_ft S [a; b; e]))) +
         &2 * sum(1..3) (\a. Wf y (rfa_ft S [a]) * lnabla 1 G Wf y (rfa_ft S [a; e]))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o el 11 o CONJUNCTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o el 12 o CONJUNCTS) THEN
  RFA_INDEX_CASES_TAC [`e:num`] THEN
  W(fun (asl, w) ->
    let a = fst(find (fun (_, th) -> length(conjuncts(concl th)) > 10) asl) in
    let ath = snd(find (fun (_, th) -> length(conjuncts(concl th)) > 10) asl) in
    ACCEPT_TAC (PROVE_HYP ath (RFA_NRM2_DERIVE 1 (concl ath) w))));;

let RFA_HEAT_NRM2 = prove
 (`!U a b (G:real->real^N->real^N^N) Uf HUf Wf HWf.
     lricci_flow U a b G /\ rfa_heat 2 U a b G Uf HUf /\ rfa_heat 1 U a b G Wf HWf
     ==> rfa_heat 0 U a b G (\t. rfa_nrm2 (G t) (Uf t) (Wf t))
                            (\t. rfa_hnrm2 (G t) (Uf t) (HUf t) (Wf t) (HWf t))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  (fun g ->
    let flow = ASSUME `lricci_flow U a b (G:real->real^N->real^N^N)`
    and thU = ASSUME `rfa_heat 2 U a b (G:real->real^N->real^N^N) Uf HUf`
    and thW = ASSUME `rfa_heat 1 U a b (G:real->real^N->real^N^N) Wf HWf` in
    let thUU = RFA_HPROD_RULE flow thU thU in
    let thUp = RFA_HPERM_RULE flow `swap(2,3)` RFA_SWAP23_PERMUTES4 thUU in
    let thUc = RFA_HCONTR_RULE flow (RFA_HCONTR_RULE flow thUp) in
    let thWW = RFA_HPROD_RULE flow thW thW in
    let thWc = RFA_HCONTR_RULE flow thWW in
    let thAll = RFA_HLIN_RULE flow `&1` `&1` thUc thWc in
    let args = rfa_heat_args thAll in
    (MATCH_MP_TAC RFA_HEAT_CONG THEN MAP_EVERY EXISTS_TAC [el 5 args; el 6 args] THEN
     ASM_REWRITE_TAC[thAll]) g) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_nrm2; rfa_hnrm2] THEN REAL_ARITH_TAC);;

let RFA_HEAT_IFLD0 = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G ==> rfa_heat 4 U a b G (\t. rfa_ifld (G t)) (\t y u. &0)`,
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
    (MATCH_MP_TAC RFA_HEAT_CONG THEN MAP_EVERY EXISTS_TAC [el 5 args; el 6 args] THEN
     ASM_REWRITE_TAC[th]) g) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[RFA_IFLD_LTPROD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!u. lnabla 2 ((G:real->real^N->real^N^N) t) (lmetric2 (G t)) y u = &0`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LNABLA_METRIC THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ltperm; rfa_hprod; ltprod; rfa_xgrad] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0] THEN
  REAL_ARITH_TAC);;

(* The heat family of the smoothly perturbed Harnack quadratic: M + pb(t) g,  *)
(* Rm + pa(t) I with time coefficients pa, pb.                                *)

let RFA_HEAT_PQUAD = prove
 (`!U a b (G:real->real^3->real^3^3) s (pa:real->real) pa' (pb:real->real) pb'
    Uf HUf Wf HWf.
     lricci_flow U a b G /\ s <= a /\
     (!t. a < t /\ t < b ==> (pa has_real_derivative pa' t) (atreal t)) /\
     smooth_map_on (interval(lift a,lift b)) (\x. lift(pa(drop x))) /\
     (!t. a < t /\ t < b ==> (pb has_real_derivative pb' t) (atreal t)) /\
     smooth_map_on (interval(lift a,lift b)) (\x. lift(pb(drop x))) /\
     rfa_heat 2 U a b G Uf HUf /\ rfa_heat 1 U a b G Wf HWf
     ==> rfa_heat 0 U a b G
           (\t. rfa_qform (G t) (\y u. rfa_hM s t (G t) y u + pb t * lmetric2 (G t) y u)
                  (rfa_hP (G t)) (\y u. lrm4 (G t) y u + pa t * rfa_ifld (G t) y u)
                  (Uf t) (Wf t))
           (\t. rfa_hqform (G t) (\y u. rfa_hM s t (G t) y u + pb t * lmetric2 (G t) y u)
                  (\y u. rfa_hhM s t (G t) y u + pb' t * lmetric2 (G t) y u)
                  (rfa_hP (G t))
                  (\y u. rfa_hdr (G t) y (\m. if m = 1 then u 2 else if m = 2 then u 3 else u 1) -
                         rfa_hdr (G t) y (\m. if m = 1 then u 1 else if m = 2 then u 3 else u 2))
                  (\y u. lrm4 (G t) y u + pa t * rfa_ifld (G t) y u)
                  (\y u. rfa_h3 (G t) (rfa_hric (G t)) y u + pa' t * rfa_ifld (G t) y u)
                  (Uf t) (HUf t) (Wf t) (HWf t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  (fun g ->
    let flow = ASSUME `lricci_flow U a b (G:real->real^3->real^3^3)` in
    let thM = MATCH_MP RFA_HEAT_HM3 (CONJ flow (ASSUME `s <= a:real`)) in
    let thg = MATCH_MP RFA_HEAT_METRIC flow in
    let thbg = MATCH_MP (ISPECL [`2`; `U:real^3->bool`; `a:real`; `b:real`;
                                 `G:real->real^3->real^3^3`; `\t:real. lmetric2((G:real->real^3->real^3^3) t)`;
                                 `\t:real. \y:real^3. \u:num->real^3. &0`;
                                 `pb:real->real`; `pb':real->real`] RFA_HEAT_TMUL)
                 (end_itlist CONJ [flow; thg;
                   ASSUME `!t. a < t /\ t < b ==> ((pb:real->real) has_real_derivative pb' t) (atreal t)`;
                   ASSUME `smooth_map_on (interval(lift a,lift b)) (\x. lift((pb:real->real)(drop x)))`]) in
    let thMh = RFA_HLIN_RULE flow `&1` `&1` thM (BETA_RULE thbg) in
    let thP = MATCH_MP RFA_HEAT_HP flow in
    let thR = MATCH_MP RFA_HEAT_RM3 flow in
    let thI = MATCH_MP RFA_HEAT_IFLD0 flow in
    let thaI = MATCH_MP (ISPECL [`4`; `U:real^3->bool`; `a:real`; `b:real`;
                                 `G:real->real^3->real^3^3`; `\t:real. rfa_ifld((G:real->real^3->real^3^3) t)`;
                                 `\t:real. \y:real^3. \u:num->real^3. &0`;
                                 `pa:real->real`; `pa':real->real`] RFA_HEAT_TMUL)
                 (end_itlist CONJ [flow; thI;
                   ASSUME `!t. a < t /\ t < b ==> ((pa:real->real) has_real_derivative pa' t) (atreal t)`;
                   ASSUME `smooth_map_on (interval(lift a,lift b)) (\x. lift((pa:real->real)(drop x)))`]) in
    let thRh = RFA_HLIN_RULE flow `&1` `&1` thR (BETA_RULE thaI) in
    let thMh' = MATCH_MP RFA_HEAT_CONG
      (CONJ thMh (CONJ (ASSUME `open(U:real^3->bool)`)
        (prove(`!t y u. a < t /\ t < b /\ y IN U
                ==> (\t y u. rfa_hM s t ((G:real->real^3->real^3^3) t) y u + pb t * lmetric2 (G t) y u)
                      t y u =
                    (\t y u. &1 * rfa_hM s t (G t) y u + &1 * pb t * lmetric2 (G t) y u) t y u /\
                    (\t y u. rfa_hhM s t (G t) y u + pb' t * lmetric2 (G t) y u) t y u =
                    (\t y u. &1 * rfa_hhM s t (G t) y u + &1 * (pb' t * lmetric2 (G t) y u + pb t * &0))
                      t y u`, REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC)))) in
    let thRh' = MATCH_MP RFA_HEAT_CONG
      (CONJ thRh (CONJ (ASSUME `open(U:real^3->bool)`)
        (prove(`!t y u. a < t /\ t < b /\ y IN U
                ==> (\t y u. lrm4 ((G:real->real^3->real^3^3) t) y u + pa t * rfa_ifld (G t) y u)
                      t y u =
                    (\t y u. &1 * lrm4 (G t) y u + &1 * pa t * rfa_ifld (G t) y u) t y u /\
                    (\t y u. rfa_h3 (G t) (rfa_hric (G t)) y u + pa' t * rfa_ifld (G t) y u) t y u =
                    (\t y u. &1 * rfa_h3 (G t) (rfa_hric (G t)) y u +
                             &1 * (pa' t * rfa_ifld (G t) y u + pa t * &0)) t y u`,
                REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC)))) in
    let thQ = MATCH_MP RFA_HEAT_QUAD
      (end_itlist CONJ [flow; BETA_RULE thMh'; thP; BETA_RULE thRh';
                        ASSUME `rfa_heat 2 U a b (G:real->real^3->real^3^3) Uf HUf`;
                        ASSUME `rfa_heat 1 U a b (G:real->real^3->real^3^3) Wf HWf`]) in
    ACCEPT_TAC (BETA_RULE thQ) g));;

(* ========================================================================= *)
(* The tests at a touching point.  RFA_HEAT0_AT (time                        *)
(* derivative of a scalar heat family = Laplacian + defect),                 *)
(* RFA_LEFT_DERIV_NONPOS, and RFA_TOUCH_INEQ: if F + c q N >= 0 near y0 at   *)
(* time T, F + c psi0 (1 + C(T - t)) N >= 0 at y0 before T, and both vanish  *)
(* at (T,y0), then the defects satisfy                                       *)
(*   HF + (c' - C c) psi0 N + c psi0 HN - c (N Lap q + 2 <grad q, grad N>)   *)
(*   <= 0 at (T,y0).                                                         *)
(* ========================================================================= *)

let RFA_HEAT0_AT = prove
 (`!U a b (G:real->real^N->real^N^N) Tf Hf t y u.
     lricci_flow U a b G /\ rfa_heat 0 U a b G Tf Hf /\ a < t /\ t < b /\ y IN U
     ==> ((\s. Tf s y u) has_real_derivative
          (llap (G t) (\x. Tf t x u) y + Hf t y u)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field 0 U ((Tf:real->real^N->(num->real^N)->real) t) /\
    ((\s. Tf s y u) has_real_derivative
      ltlap 0 ((G:real->real^N->real^N^N) t) (Tf t) y u - rfa_rcact 0 (G t) (Tf t) y u +
      Hf t y u) (atreal t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfa_heat]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\x. lift((Tf:real->real^N->(num->real^N)->real) t x u))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`0`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                   `Tf:real->real^N->(num->real^N)->real`;
                   `Hf:real->real^N->(num->real^N)->real`; `t:real`] RFA_HEAT_SLICE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltlap 0 ((G:real->real^N->real^N^N) t) (Tf t) y u = llap (G t) (\x. Tf t x u) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ltlap 0 ((G:real->real^N->real^N^N) t)
                  (\x w. (Tf:real->real^N->(num->real^N)->real) t x u) y u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTLAP_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ltensor_field 0 U ((Tf:real->real^N->(num->real^N)->real) t)` THEN
      REWRITE_TAC[ltensor_field] THEN MESON_TAC[ARITH_RULE `~(1 <= m /\ m <= 0)`];
      MATCH_MP_TAC RFA_LTLAP_0 THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC
   `((\s. (Tf:real->real^N->(num->real^N)->real) s y u) has_real_derivative
      ltlap 0 ((G:real->real^N->real^N^N) t) (Tf t) y u - rfa_rcact 0 (G t) (Tf t) y u +
      (Hf:real->real^N->(num->real^N)->real) t y u) (atreal t)` THEN
  ASM_REWRITE_TAC[rfa_rcact; SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO]);;

let RFA_LEFT_DERIV_NONPOS = prove
 (`!(f:real->real) D t0 d.
     (f has_real_derivative D) (atreal t0) /\ &0 < d /\ f t0 = &0 /\
     (!t. t0 - d < t /\ t < t0 ==> &0 <= f t)
     ==> D <= &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pos")))) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `D:real`; `t0:real`; `(:real)`; `D / &2`]
         RFA_LEFT_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[WITHINREAL_UNIV; IN_UNIV; REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))) THEN
  ABBREV_TAC `h = min (e / &2) (d / &2)` THEN
  SUBGOAL_THEN `&0 < h /\ h < e /\ h < d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "bd" (MP_TAC o SPEC `h:real`) THEN
  REMOVE_THEN "pos" (MP_TAC o SPEC `t0 - h`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `v = (f:real->real) (t0 - h)` THEN
  SUBGOAL_THEN `&0 < h * D` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RFA_TEST_DERIV = prove
 (`!(f:real->real) f' (n:real->real) n' (ce:real->real) ce' psi0 C t0.
     (f has_real_derivative f') (atreal t0) /\ (n has_real_derivative n') (atreal t0) /\
     (ce has_real_derivative ce') (atreal t0)
     ==> ((\t. f t + ce t * (psi0 * (&1 + C * (t0 - t))) * n t) has_real_derivative
          (f' + ce t0 * (psi0 * n' - psi0 * C * n t0) + ce' * psi0 * n t0)) (atreal t0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\t. psi0 * (&1 + C * (t0 - t))) has_real_derivative (psi0 * --C))
                (atreal t0)` ASSUME_TAC THENL
   [REAL_DIFF_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun dphi -> FIRST_ASSUM(fun dn ->
    if not (can (find_term ((=) `n:real->real`)) (concl dn)) then failwith "dn" else
    let drest = BETA_RULE (MATCH_MP HAS_REAL_DERIVATIVE_MUL_ATREAL (CONJ dphi dn)) in
    let dce = ASSUME `((ce:real->real) has_real_derivative ce') (atreal t0)` in
    let dprod = BETA_RULE (MATCH_MP HAS_REAL_DERIVATIVE_MUL_ATREAL (CONJ dce drest)) in
    let df = ASSUME `((f:real->real) has_real_derivative f') (atreal t0)` in
    let dh = BETA_RULE (MATCH_MP HAS_REAL_DERIVATIVE_ADD (CONJ df dprod)) in
    MP_TAC dh)) THEN
  MATCH_MP_TAC(MESON[] `f' = g' ==> (f has_real_derivative f') net
                                    ==> (f has_real_derivative g') net`) THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
  REAL_ARITH_TAC);;

let RFA_TOUCH_INEQ = prove
 (`!U a b (G:real->real^N->real^N^N) Ff HFf Nf HNf (ce:real->real) ce' C psi0 W q t0 y0
    u d.
     lricci_flow U a b G /\ a < t0 /\ t0 < b /\ y0 IN W /\ open W /\ W SUBSET U /\
     rfa_heat 0 U a b G Ff HFf /\ rfa_heat 0 U a b G Nf HNf /\
     (ce has_real_derivative ce') (atreal t0) /\
     smooth_map_on W (\y. lift(q y)) /\ q y0 = psi0 /\
     (!y. y IN W ==> &0 <= Ff t0 y u + ce t0 * q y * Nf t0 y u) /\
     &0 < d /\
     (!t. t0 - d < t /\ t < t0
          ==> &0 <= Ff t y0 u + ce t * (psi0 * (&1 + C * (t0 - t))) * Nf t y0 u) /\
     Ff t0 y0 u + ce t0 * psi0 * Nf t0 y0 u = &0
     ==> HFf t0 y0 u + (ce' - C * ce t0) * psi0 * Nf t0 y0 u + ce t0 * psi0 * HNf t0 y0 u -
         ce t0 * (Nf t0 y0 u * llap (G t0) q y0 +
                  &2 * rfa_lginner (G t0) q (\x. Nf t0 x u) y0) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t0) /\ (y0:real^N) IN U`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field W ((G:real->real^N->real^N^N) t0)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `Ff:real->real^N->(num->real^N)->real`; `HFf:real->real^N->(num->real^N)->real`;
                 `t0:real`; `y0:real^N`; `u:num->real^N`] RFA_HEAT0_AT) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `Nf:real->real^N->(num->real^N)->real`; `HNf:real->real^N->(num->real^N)->real`;
                 `t0:real`; `y0:real^N`; `u:num->real^N`] RFA_HEAT0_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `LF = llap ((G:real->real^N->real^N^N) t0)
                    (\x. (Ff:real->real^N->(num->real^N)->real) t0 x u) y0` THEN
  ABBREV_TAC `LN = llap ((G:real->real^N->real^N^N) t0)
                    (\x. (Nf:real->real^N->(num->real^N)->real) t0 x u) y0` THEN
  REPEAT DISCH_TAC THEN
  (* the time test *)
  MP_TAC(ISPECL [`\s. (Ff:real->real^N->(num->real^N)->real) s y0 u`;
                 `LF + (HFf:real->real^N->(num->real^N)->real) t0 y0 u`;
                 `\s. (Nf:real->real^N->(num->real^N)->real) s y0 u`;
                 `LN + (HNf:real->real^N->(num->real^N)->real) t0 y0 u`;
                 `ce:real->real`; `ce':real`; `psi0:real`; `C:real`; `t0:real`]
         RFA_TEST_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\t. (Ff:real->real^N->(num->real^N)->real) t y0 u +
         (ce:real->real) t * (psi0 * (&1 + C * (t0 - t))) *
         (Nf:real->real^N->(num->real^N)->real) t y0 u`;
    `(LF + (HFf:real->real^N->(num->real^N)->real) t0 y0 u) +
     (ce:real->real) t0 * (psi0 * (LN + (HNf:real->real^N->(num->real^N)->real) t0 y0 u) -
                           psi0 * C * (Nf:real->real^N->(num->real^N)->real) t0 y0 u) +
     ce' * psi0 * Nf t0 y0 u`; `t0:real`; `d:real`] RFA_LEFT_DERIV_NONPOS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN BETA_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  (* the space test *)
  SUBGOAL_THEN `smooth_map_on W (\x. lift((Ff:real->real^N->(num->real^N)->real) t0 x u)) /\
                smooth_map_on W (\x. lift((Nf:real->real^N->(num->real^N)->real) t0 x u))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`0`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                     `Ff:real->real^N->(num->real^N)->real`;
                     `HFf:real->real^N->(num->real^N)->real`; `t0:real`] RFA_HEAT_SLICE);
      MP_TAC(ISPECL [`0`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                     `Nf:real->real^N->(num->real^N)->real`;
                     `HNf:real->real^N->(num->real^N)->real`; `t0:real`] RFA_HEAT_SLICE)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `W:real^N->bool`; `(G:real->real^N->real^N^N) t0`;
                 `\y. (Ff:real->real^N->(num->real^N)->real) t0 y u +
                      (ce:real->real) t0 * q y * (Nf:real->real^N->(num->real^N)->real) t0 y u`;
                 `y0:real^N`] RFA_LLAP_LOCAL_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[LIFT_ADD] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `(G:real->real^N->real^N^N) t0`;
                 `\x. (Ff:real->real^N->(num->real^N)->real) t0 x u`;
                 `\y. (ce:real->real) t0 * q y * (Nf:real->real^N->(num->real^N)->real) t0 y u`;
                 `y0:real^N`] RFA_LLAP_ADD) THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `(G:real->real^N->real^N^N) t0`;
                 `\y. q y * (Nf:real->real^N->(num->real^N)->real) t0 y u`;
                 `(ce:real->real) t0`; `y0:real^N`] RFA_LLAP_CMUL) THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `(G:real->real^N->real^N^N) t0`; `q:real^N->real`;
                 `\x. (Nf:real->real^N->(num->real^N)->real) t0 x u`; `y0:real^N`]
         RFA_LLAP_MUL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `smooth_map_on W (\y. lift(q y * (Nf:real->real^N->(num->real^N)->real) t0 y u)) /\
                smooth_map_on W (\y. lift((ce:real->real) t0 * q y * Nf t0 y u))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[LIFT_CMUL] THEN
                    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 <= llap ((G:real->real^N->real^N^N) t0)
                 (\y. (Ff:real->real^N->(num->real^N)->real) t0 y u +
                      (ce:real->real) t0 * q y * (Nf:real->real^N->(num->real^N)->real) t0 y u) y0` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `ce':real`)) (concl th) &&
                                          is_binary "real_le" (concl th))) THEN
  REAL_ARITH_TAC);;


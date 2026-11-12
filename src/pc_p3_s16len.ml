(* ========================================================================= *)
(* Unit pc_p3_s16len (Part 3 proofs; MT Ch 16): MT Prop 16.13 with the       *)
(* energy integrand integrable and a free start time Tp.  The cylinder       *)
(* radial bound (P3N_NC_RADIAL), the quadratic-form chain (P3N_QF_CHAIN),    *)
(* the scalar stability (P3N_LEN_SCALAR), the energy inequalities of the top *)
(* and side cases (P3N_ENERGY_TOP, P3N_ENERGY_SIDE), the parametrized curve  *)
(* derivative (P3N_PARAM_CURVE_DERIV), the closeness on the whole slab       *)
(* (P3N_1613_CLOSE), the scalar bound (P3N_1613_RBOUND), the radial          *)
(* derivative along the curve (P3N_1613_DERIV), the two cases (P3N_1613_TOP, *)
(* P3N_1613_SIDE) and the assembly P3N_PROP_16_13_FIX from the Prop 16.5     *)
(* body with a cutoff time, Props 12.31 and 12.7 and Thm 12.5.               *)
(* ========================================================================= *)

needs "src/pc_p3_s16prop5.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The radial distance function of the standard initial metric              *)
(* in the shrinking cylinder.  The quadratic form of cylinder_flow           *)
(* (P3N_CYL_QF), and the gradient bound of d = p3_std_dist g0 for the       *)
(* cylinder metrics in the neck coordinates p3_std_nc: (Dd(x) w)^2 is at     *)
(* most the cylinder quadratic form at every time t <= 1 (P3N_NC_RADIAL).   *)
(* ========================================================================= *)

let P3N_CYL_QF = prove
 (`!t (y:real^3) v.
     v dot (cylinder_flow t y ** v) =
     &2 / norm y pow 2 * ((&1 - t) * (v dot v) + t / norm y pow 2 * (y dot v) pow 2)`,
  REWRITE_TAC[cylinder_flow; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              MATRIX_VECTOR_MUL_LID; P3N_OUTER_MUL] THEN
  REWRITE_TAC[DOT_RMUL; DOT_RADD] THEN REWRITE_TAC[DOT_SYM] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let P3N_MPULLBACK_QF = prove
 (`!(h:real^N->real^N) h' (G:real^N->real^N^N) z v.
     (h has_derivative h') (at z)
     ==> v dot (mpullback h G z ** v) = h' v dot (G(h z) ** h' v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[has_derivative]) THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_REWRITE_TAC[mpullback; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let P3N_NC_RADIAL = prove
 (`!g0 A0 (x:real^3) t w.
     p3_std_initial g0 A0 /\ ~(x = vec 0) /\ t <= &1
     ==> (sqrt(p3s_rad_a g0 (norm x)) * (w dot x) / norm x) pow 2 <=
         w dot (mpullback (p3_std_nc g0 A0) (cylinder_flow t) x ** w)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `r = norm(x:real^3)` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `M = \q. exp((A0 + &4 - p3s_rad_rho g0 q) / sqrt(&2))` THEN
  SUBGOAL_THEN `p3_std_nc g0 A0 = (\z:real^3. ((M:real->real)(norm z) * inv(norm z)) % z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p3_std_nc] THEN X_GEN_TAC `z:real^3` THEN
    EXPAND_TAC "M" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`] P3S_ROT_DIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `sa = sqrt(p3s_rad_a g0 r)` THEN
  ABBREV_TAC `m = (M:real->real) r` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN EXPAND_TAC "M" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `((M:real->real) has_real_derivative (m * --(sa / sqrt(&2)))) (atreal r)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(M:real->real) = exp o (\q. (A0 + &4 - p3s_rad_rho g0 q) / sqrt(&2))`
    SUBST1_TAC THENL
     [EXPAND_TAC "M" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `m = exp((A0 + &4 - p3s_rad_rho g0 r) / sqrt(&2))` SUBST1_TAC THENL
     [EXPAND_TAC "m" THEN EXPAND_TAC "M" THEN REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_EXP] THEN
    REWRITE_TAC[real_div] THEN
    SUBGOAL_THEN `--(sa * inv(sqrt(&2))) = (&0 + (&0 - sa)) * inv(sqrt(&2))` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
    REWRITE_TAC[ETA_AX] THEN EXPAND_TAC "sa" THEN MATCH_MP_TAC P3S_RHO_DERIV THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`M:real->real`; `m * --(sa / sqrt(&2))`; `x:real^3`]
                P3S_RADMAP_GEN_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP P3N_MPULLBACK_QF th]) o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "has_derivative" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[P3N_CYL_QF] THEN
  SUBGOAL_THEN `norm((m * inv r) % (x:real^3)) = m` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
    UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[DOT_LMUL; DOT_RMUL; DOT_LADD; DOT_RADD] THEN
  SUBGOAL_THEN `(x:real^3) dot x = r pow 2 /\ (w:real^3) dot x = x dot w` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[DOT_SQUARE_NORM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[DOT_SYM]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((x:real^3) dot w) pow 2 <= r pow 2 * (w dot w)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x:real^3`; `w:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM DOT_SQUARE_NORM] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN
    SUBGOAL_THEN `r pow 2 * ((w:real^3) dot w) = (r * norm w) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL; NORM_POW_2]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = (x:real^3) dot w` THEN ABBREV_TAC `H = (w:real^3) dot w` THEN
  SUBGOAL_THEN `sqrt(&2) pow 2 = &2 /\ ~(sqrt(&2) = &0)` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POW_2; REAL_POS; SQRT_EQ_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!c. b - a = c /\ &0 <= c ==> a <= b`) THEN
  EXISTS_TAC `&2 * (&1 - t) * (H - (X / r) pow 2) / r pow 2` THEN CONJ_TAC THENL
   [UNDISCH_TAC `sqrt(&2) pow 2 = &2` THEN UNDISCH_TAC `~(sqrt(&2) = &0)` THEN
    UNDISCH_TAC `&0 < m` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REWRITE_TAC[REAL_SUB_LE; REAL_POW_DIV] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The radial gradient bound for metrics close to the                       *)
(* shrinking cylinder.  The cylinder metrics in the neck coordinates are    *)
(* metric fields on the punctured balls of the standard initial metric      *)
(* (P3N_NC_CYL_FIELD); quadratic forms pass along two closeness steps with  *)
(* a factor (P3N_QF_CHAIN); hence (Dd(y) w)^2 <= 25/16 w.P(y)w for P close  *)
(* to a metric G close to the cylinder (P3N_SHELL_GRAD).                    *)
(* ========================================================================= *)

let P3N_NC_CYL_FIELD = prove
 (`!g0 A0 Am t.
     p3_std_initial g0 A0 /\ &0 < Am /\ t < &1
     ==> metric_field {x:real^3 | &0 < p3_std_dist g0 x /\ p3_std_dist g0 x < Am}
                      (mpullback (p3_std_nc g0 A0) (cylinder_flow t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:real^3 | &0 < p3_std_dist g0 x /\ p3_std_dist g0 x < Am} =
                {x | A0 + &4 - Am < A0 + &4 - p3_std_dist g0 x /\
                     A0 + &4 - p3_std_dist g0 x < A0 + &4}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
  MAP_EVERY EXISTS_TAC
   [`{y:real^3 | exp((A0 + &4 - Am) / sqrt(&2)) < norm y /\ norm y < exp((A0 + &4) / sqrt(&2))}`;
    `p3s_ncinv g0 A0`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{y:real^3 | exp((A0 + &4 - Am) / sqrt(&2)) < norm y /\
                               norm y < exp((A0 + &4) / sqrt(&2))} =
                    ball(vec 0,exp((A0 + &4) / sqrt(&2))) DIFF
                    cball(vec 0,exp((A0 + &4 - Am) / sqrt(&2)))` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_BALL_0; IN_CBALL_0] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_BALL; CLOSED_CBALL]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `exp((A0 + &4 - Am) / sqrt(&2)) < norm(vec 0:real^3)` THEN
      REWRITE_TAC[NORM_0] THEN MP_TAC(SPEC `(A0 + &4 - Am) / sqrt(&2)` REAL_EXP_POS_LT) THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC P3S_NC_DIFFEO THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P3N_QF_CHAIN = prove
 (`!s (G0:real^3->real^3^3) G P y w k1 k2 ep dl q.
     metric_field s G0 /\ metric_field s G /\ metric_field s P /\ y IN s /\
     lck_dist2 k1 G0 G y < ep pow 2 /\ lck_dist2 k2 G P y < dl pow 2 /\
     &0 < ep /\ ep <= &1 / &10 /\ &0 < dl /\ dl <= &1 / &10 /\
     &0 <= q /\ q <= w dot (G0 y ** w)
     ==> q <= &25 / &16 * (w dot (P y ** w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= lck_dist2 k1 (G0:real^3->real^3^3) G y /\
                &0 <= lck_dist2 k2 (G:real^3->real^3^3) P y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[lck_dist2] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 k1 (G0:real^3->real^3^3) G y) <= ep /\
                sqrt(lck_dist2 k2 (G:real^3->real^3^3) P y) <= dl` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k1:num`; `s:real^3->bool`; `G0:real^3->real^3^3`; `G:real^3->real^3^3`;
                 `y:real^3`; `w:real^3`] LCK_DIST_C0) THEN
  MP_TAC(ISPECL [`k2:num`; `s:real^3->bool`; `G:real^3->real^3^3`; `P:real^3->real^3^3`;
                 `y:real^3`; `w:real^3`] LCK_DIST_C0) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a0 = (w:real^3) dot ((G0:real^3->real^3^3) y ** w)` THEN
  ABBREV_TAC `a1 = (w:real^3) dot ((G:real^3->real^3^3) y ** w)` THEN
  ABBREV_TAC `a2 = (w:real^3) dot ((P:real^3->real^3^3) y ** w)` THEN
  ABBREV_TAC `e1 = sqrt(lck_dist2 k1 (G0:real^3->real^3^3) G y)` THEN
  ABBREV_TAC `e2 = sqrt(lck_dist2 k2 (G:real^3->real^3^3) P y)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(&1 - ep) * a0 <= a1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs(a1 - a0) <= e1 * a0 /\ e1 * a0 <= ep * a0
                             ==> (&1 - ep) * a0 <= a1`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - dl) * a1 <= a2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs(a2 - a1) <= e2 * a1 /\ e2 * a1 <= dl * a1
                             ==> (&1 - dl) * a1 <= a2`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - ep) * a0` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&81 / &100 * a0 <= a2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - dl) * (&1 - ep) * a0` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&9 / &10) * (&9 / &10)` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - dl) * a1` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The closeness of Prop 16.5 in coordinates, and the scalar                *)
(* curvature of the evolving cap region.  P3N_VIEW_CLOSE_ELIM: the view     *)
(* closeness to a standard flow G gives, at each normalized time s, the     *)
(* parametrization and lck closeness of the rescaled coordinate flow.       *)
(* P3N_LEN_SCALAR: if G has R >= c/(1-t) and nonnegative sectional          *)
(* curvature, a close coordinate flow has R >= c/(2(1-s)) in rescaled       *)
(* units (MT Def 16.12 with Prop 12.31; |Rm| <= C R from sec >= 0).        *)
(* ========================================================================= *)

let P3N_VIEW_CLOSE_ELIM = prove
 (`!(hs:(A)rfs_history) Phi ts Q (G:real->real^3->real^3^3) W J dcl s.
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) W (rfs_view hs) ts Q Phi J dcl /\
     s IN J /\ &0 <= s /\ s < &1
     ==> &0 < Q /\
         (?psi'. mfd_diffeo euclidean (open_set_atlas (:real^3)) W
                   (rfs_vtop (rfs_view hs) (ts + s / Q)) (rfs_vatlas (rfs_view hs) (ts + s / Q))
                   (IMAGE Phi W) Phi psi') /\
         (?d. d < dcl pow 2 /\
              !x. x IN W ==> lck_dist2 (rfs_kreg dcl) (G s) (p3n_cfl hs Phi ts Q s) x <= d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_view_close] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; REAL_DIV_1; REAL_ADD_LID;
              IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[rfs_mclose; GEOL_EUCLID_FACTS; P2C_OPEN_SET_METRIC_LOCAL_UNIV] THEN
  REWRITE_TAC[MATRIX_CMUL_LID; ETA_AX; P3N_PULLBACK_OSA; p3n_cfl] THEN SIMP_TAC[]);;

let P3N_LEN_SCALAR = prove
 (`!c. &0 < c
       ==> ?dl0. &0 < dl0 /\ dl0 <= &1 / &10 /\
           !(G:real^3->real^3^3) H W y dl.
             metric_field W G /\ metric_field W H /\ y IN W /\
             c <= lscalar G y /\
             (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v) /\
             &0 < dl /\ dl <= dl0 /\ lck_dist2 (rfs_kreg dl) G H y < dl pow 2
             ==> lscalar G y / &2 <= lscalar H y`,
  GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC (INST_TYPE [`:3`,`:N`] RFA_LRM_SECTIONAL_BOUND) THEN
  ABBREV_TAC `s0 = sqrt C0` THEN
  SUBGOAL_THEN `&0 <= s0 /\ s0 pow 2 = C0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2]; ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &10) (min (c / &288) (inv(&144 * (s0 + &1))))` THEN
  SUBGOAL_THEN `&0 < inv(&144 * (s0 + &1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = lscalar (G:real^3->real^3^3) y` THEN
  SUBGOAL_THEN `!u v. ~collinear {vec 0,u,v}
                      ==> abs(lsectional (G:real^3->real^3^3) y u v) <= R / &2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`W:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`;
                   `v:real^3`; `&0`] P3N_LSEC_UPPER) THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "lsectional" with Failure _ -> false))
          (concl th) &&
      not (can (find_term (fun t -> try fst(dest_const t) = "abs" with Failure _ -> false))
               (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lrm_deriv_norm2 0 (G:real^3->real^3^3) y <= (s0 * R / &2) pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C0 * (R / &2) pow 2` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `W:real^3->bool` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `s0 pow 2 = C0`)) THEN
      REWRITE_TAC[REAL_POW_MUL; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lck_dist2 2 (G:real^3->real^3^3) H y /\
                lck_dist2 2 G H y <= lck_dist2 (rfs_kreg dl) G H y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[lck_dist2] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
      EXISTS_TAC `W:real^3->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `W:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(lck_dist2 2 (G:real^3->real^3^3) H y) /\
                sqrt(lck_dist2 2 G H y) <= dl` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `e = sqrt(lck_dist2 2 (G:real^3->real^3^3) H y)` THEN
  MP_TAC(ISPECL [`s0 * R / &2`; `W:real^3->bool`; `G:real^3->real^3^3`; `H:real^3->real^3^3`;
                 `y:real^3`] APX_SCALAR_STABILITY_LIP) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(s0 * R / &2) = s0 * R / &2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&72 * e <= R / &4 /\ &36 * s0 * e <= &1 / &4` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&72 * c / &288` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&36 * (s0 + &1) * e` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `(s0 + &1) * e <= (s0 + &1) * inv(&144 * (s0 + &1))` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(s0 + &1) * inv(&144 * (s0 + &1)) = inv(&144)` SUBST1_TAC THENL
         [REWRITE_TAC[REAL_INV_MUL] THEN
          SUBGOAL_THEN `~(s0 + &1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          CONV_TAC REAL_FIELD;
          REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&36 * s0 * e) * R <= R / &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &4 * R` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&8 * &3 pow 2 * (&1 + s0 * R / &2) * e = &72 * e + (&36 * s0 * e) * R`
  ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The two integral estimates of MT Prop 16.13.  Top case                   *)
(* (P3N_ENERGY_TOP): an integrand at least inv(h^2) c / (2(1 - sigma)) with  *)
(* sigma = th0 - tau/h^2 has integral at least c/2 (log(1/2) - log(1-th0)) *)
(* when sigma <= 1/2 at the end.  Side case (P3N_ENERGY_SIDE): a function   *)
(* f from A down to below A/2 with |f'|^2 <= K^2 X off a countable set,    *)
(* X <= E, E integrable with integral I, has A/2 <= K/2 (lam b + I/lam).    *)
(* ========================================================================= *)

let P3N_ENERGY_TOP = prove
 (`!c th0 h b (E:real->real) en.
     &0 < c /\ &0 < h /\ th0 < &1 /\ &0 <= b /\ th0 - b / h pow 2 <= &1 / &2 /\
     (E has_real_integral en) (real_interval[&0,b]) /\
     (!tau. tau IN real_interval[&0,b]
            ==> inv(h pow 2) * c / (&2 * (&1 - (th0 - tau / h pow 2))) <= E tau)
     ==> c / &2 * (log(&1 / &2) - log(&1 - th0)) <= en`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < h pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau. tau IN real_interval[&0,b] ==> &0 < (&1 - th0) + tau * inv(h pow 2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> &0 < a + b`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\tau. c / &2 * log((&1 - th0) + tau * inv(h pow 2))`;
                 `\tau. inv(h pow 2) * c / (&2 * (&1 - (th0 - tau / h pow 2)))`;
                 `&0`; `b:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    SUBGOAL_THEN `inv(h pow 2) * c / (&2 * (&1 - (th0 - tau / h pow 2))) =
                  c / &2 * (inv((&1 - th0) + tau * inv(h pow 2)) * (&0 + &1 * inv(h pow 2)))`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `tau:real`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < h pow 2` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    MP_TAC(ISPECL [`\tau. (&1 - th0) + tau * inv(h pow 2)`; `log`;
                   `&0 + &1 * inv(h pow 2)`; `inv((&1 - th0) + tau * inv(h pow 2))`;
                   `tau:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_ID];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\tau. inv(h pow 2) * c / (&2 * (&1 - (th0 - tau / h pow 2)))`;
                 `E:real->real`; `real_interval[&0,b]`;
                 `(\tau. c / &2 * log((&1 - th0) + tau * inv(h pow 2))) b -
                  (\tau. c / &2 * log((&1 - th0) + tau * inv(h pow 2))) (&0)`;
                 `en:real`] HAS_REAL_INTEGRAL_LE) THEN
  ASM_SIMP_TAC[] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= x ==> x <= i ==> y <= i`) THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> a - c <= b - c`) THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `b * inv(h pow 2) = b / h pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[real_div]; ASM_REAL_ARITH_TAC]);;

let P3N_FIRST_DROP = prove
 (`!(f:real->real) b A.
     &0 < b /\ &0 < A /\ f real_continuous_on real_interval[&0,b] /\
     f(&0) = A /\ f b < A / &2
     ==> ?t2. &0 < t2 /\ t2 <= b /\ f t2 = A / &2 /\
              !t. &0 <= t /\ t < t2 ==> A / &2 < f t`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `St = {t | t IN real_interval[&0,b] /\ (f:real->real) t <= A / &2}` THEN
  SUBGOAL_THEN `b IN St /\ (!x. x IN St ==> &0 <= x /\ x <= b)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "St" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(St:real->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `St:real->bool` INF) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `t2 = inf St` THEN
  SUBGOAL_THEN `&0 <= t2 /\ t2 <= b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < t2 ==> A / &2 < (f:real->real) t` (LABEL_TAC "before") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(t:real) IN St` MP_TAC THENL
     [EXPAND_TAC "St" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `t2:real`)) (concl th)))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,b]
                    ==> !e. &0 < e
                            ==> ?d. &0 < d /\
                                    !x. x IN real_interval[&0,b] /\ abs(x - t) < d
                                        ==> abs((f:real->real) x - f t) < e`
  (LABEL_TAC "cont") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(f:real->real) real_continuous_on real_interval[&0,b]` THEN
    REWRITE_TAC[real_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t2:real) IN real_interval[&0,b]` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) t2 <= A / &2` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "cont" (MP_TAC o SPEC `f(t2:real) - A / &2` o C MP (ASSUME
      `(t2:real) IN real_interval[&0,b]`) o SPEC `t2:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `t2 + d <= t2` MP_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(ASSUME `!b. (!x. x IN St ==> b <= x) ==> b <= t2`) THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `t2 <= x /\ x IN real_interval[&0,b] /\ (f:real->real) x <= A / &2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real) IN St` THEN EXPAND_TAC "St" THEN REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `d:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `(f:real->real) (&0) <= A / &2` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `A / &2 <= (f:real->real) t2` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "cont" (MP_TAC o SPEC `A / &2 - f(t2:real)` o C MP (ASSUME
      `(t2:real) IN real_interval[&0,b]`) o SPEC `t2:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `max (&0) (t2 - d / &2)`) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "before" (MP_TAC o SPEC `max (&0) (t2 - d / &2)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `t2:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P3N_ENERGY_SIDE = prove
 (`!(f:real->real) (X:real->real) (E:real->real) S en b A K lam.
     &0 < b /\ &0 < A /\ &0 < K /\ &0 < lam /\ COUNTABLE S /\
     f real_continuous_on real_interval[&0,b] /\ f(&0) = A /\ f b < A / &2 /\
     (E has_real_integral en) (real_interval[&0,b]) /\
     (!tau. tau IN real_interval[&0,b] ==> &0 <= X tau /\ X tau <= E tau) /\
     (!tau. tau IN real_interval(&0,b) /\ ~(tau IN S) /\ A / &2 <= f tau
            ==> ?f'. (f has_real_derivative f') (atreal tau) /\ f' pow 2 <= K pow 2 * X tau)
     ==> A / &2 <= K / &2 * (lam * b + en / lam)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast cs) THEN LABEL_TAC "der" (last cs)) THEN
  MP_TAC(SPECL [`f:real->real`; `b:real`; `A:real`] P3N_FIRST_DROP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "before"))))) THEN
  ABBREV_TAC `Sx = (&0) INSERT t2 INSERT (S:real->bool)` THEN
  ABBREV_TAC `D = \x. if x IN Sx then &0
                      else @f'. ((f:real->real) has_real_derivative f') (atreal x) /\
                                f' pow 2 <= K pow 2 * (X:real->real) x` THEN
  SUBGOAL_THEN
   `!x. x IN real_interval[&0,t2] /\ ~(x IN Sx)
        ==> ((f:real->real) has_real_derivative D x) (atreal x) /\
            D x pow 2 <= K pow 2 * (X:real->real) x`
  (LABEL_TAC "Dprop") THENL
   [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(x = &0) /\ ~(x = t2) /\ ~((x:real) IN S)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~((x:real) IN Sx)` THEN EXPAND_TAC "Sx" THEN
      REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?f'. ((f:real->real) has_real_derivative f') (atreal x) /\
                       f' pow 2 <= K pow 2 * (X:real->real) x` MP_TAC THENL
     [USE_THEN "der" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real) IN real_interval[&0,t2]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "before" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN EXPAND_TAC "D" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `D:real->real`; `Sx:real->bool`; `&0`; `t2:real`]
                REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Sx" THEN ASM_REWRITE_TAC[COUNTABLE_INSERT];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[&0,b]` THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      USE_THEN "Dprop" (MP_TAC o SPEC `x:real`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_NEG) THEN
  SUBGOAL_THEN `--(A / &2 - A) = A / &2` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  ABBREV_TAC `u = \x. K / &2 * (lam + (E:real->real) x / lam)` THEN
  SUBGOAL_THEN `((u:real->real) has_real_integral K / &2 * (lam * b + en / lam))
                (real_interval[&0,b])` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`&0`; `b:real`; `lam:real`] HAS_REAL_INTEGRAL_CONST) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_SUB_RZERO];
      REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN real_interval[&0,b] ==> &0 <= (u:real->real) x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real` THEN DISCH_TAC THEN EXPAND_TAC "u" THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(X:real->real) x` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real->real) real_integrable_on real_interval[&0,t2]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN
    CONJ_TAC THENL [REWRITE_TAC[real_integrable_on] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,t2]) (u:real->real)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_LE THEN
    MAP_EVERY EXISTS_TAC [`\x. --((D:real->real) x)`; `u:real->real`;
                          `real_interval[&0,t2]`] THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(x:real) IN real_interval[&0,b]` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real) IN real_interval[&0,t2]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:real) IN Sx` THENL
     [SUBGOAL_THEN `(D:real->real) x = &0` SUBST1_TAC THENL
       [EXPAND_TAC "D" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_NEG_0] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "Dprop" (MP_TAC o SPEC `x:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ABBREV_TAC `d = (D:real->real) x` THEN
    SUBGOAL_THEN `&0 <= (X:real->real) x /\ X x <= (E:real->real) x` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "u" THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K / &2 * (lam + (X:real->real) x / lam)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_LE_LADD] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ]] THEN
    SUBGOAL_THEN `&0 < &2 * K * lam` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_RMUL_EQ th)]) THEN
    SUBGOAL_THEN `(K / &2 * (lam + (X:real->real) x / lam)) * (&2 * K * lam) =
                  K pow 2 * lam pow 2 + K pow 2 * X x` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (K * lam + d) pow 2` MP_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    UNDISCH_TAC `d pow 2 <= K pow 2 * (X:real->real) x` THEN
    CONV_TAC REAL_ARITH;
    MATCH_MP_TAC HAS_REAL_INTEGRAL_SUBSET_LE THEN
    MAP_EVERY EXISTS_TAC [`u:real->real`; `real_interval[&0,t2]`; `real_interval[&0,b]`] THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL] THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Velocities of a curve through a parametrization.  If a curve              *)
(* gamma = Phi o beta has velocity v in the preferred chart at gamma t0 and *)
(* beta is continuous at t0, then beta has a velocity w at t0 and the       *)
(* pulled-back metric gives w the same length as v (P3N_PARAM_CURVE_DERIV). *)
(* ========================================================================= *)

let P3N_PARAM_CURVE_DERIV = prove
 (`!top atlas (g:A->real^3^3) W (Phi:real^3->A) (gamma:real->A) (beta:real->real^3) t0 v d1.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas W Phi /\ beta t0 IN W /\
     (!e. &0 < e ==> ?d. &0 < d /\ !s. abs(s - t0) < d ==> dist(beta s,beta t0) < e) /\
     &0 < d1 /\ (!s. abs(s - t0) < d1 ==> gamma s = Phi(beta s)) /\
     ((\s. SND(chart_at atlas (Phi(beta t0))) (gamma(drop s))) has_vector_derivative v)
       (at (lift t0))
     ==> ?w. ((\s. beta(drop s)) has_vector_derivative w) (at (lift t0)) /\
             w dot (rfs_pullback atlas Phi g (beta t0) ** w) = v dot (g(Phi(beta t0)) ** v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC [el 0 cs; el 1 cs; el 2 cs; el 3 cs; el 5 cs] THEN
    LABEL_TAC "cont" (el 4 cs) THEN LABEL_TAC "eq" (el 6 cs) THEN
    LABEL_TAC "vd" (el 7 cs)) THEN
  ABBREV_TAC `y0 = (beta:real->real^3) t0` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `W:real^3->bool`; `Phi:real^3->A`; `y0:real^3`] APX_PARAM_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `N':real^3->bool`
    (X_CHOOSE_THEN `h':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `psi = SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((Phi:real^3->A) y0)) o Phi` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "diffeomorphism_on" with Failure _ -> false))
        (concl th))) THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(y0:real^3,r) SUBSET N` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(N:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "cont" (MP_TAC o C MP (ASSUME `&0 < r`) o SPEC `r:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `ch = SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((Phi:real^3->A) y0))` THEN
  SUBGOAL_THEN `!s. abs(s - t0) < min d d1
                    ==> (beta:real->real^3) s IN N /\
                        (ch:A->real^3) ((gamma:real->A) s) = (psi:real^3->real^3) (beta s) /\
                        (h':real^3->real^3) (ch (gamma s)) = beta s` (LABEL_TAC "near") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(beta:real->real^3) s IN N` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> t = `ball(y0:real^3,r)`)) (concl th))) THEN
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(ch:A->real^3) ((gamma:real->A) s) = (psi:real^3->real^3) (beta s)`
    ASSUME_TAC THENL
     [USE_THEN "eq" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "psi" THEN EXPAND_TAC "ch" THEN REWRITE_TAC[o_THM];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^3->real^3) y0 IN N'` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `IMAGE (psi:real^3->real^3) N = N'`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h':real^3->real^3) differentiable at ((psi:real^3->real^3) y0) /\
                (psi:real^3->real^3) differentiable at y0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Dh = frechet_derivative (h':real^3->real^3) (at ((psi:real^3->real^3) y0))` THEN
  ABBREV_TAC `Dp = frechet_derivative (psi:real^3->real^3) (at (y0:real^3))` THEN
  SUBGOAL_THEN `((h':real^3->real^3) has_derivative Dh) (at ((psi:real^3->real^3) y0)) /\
                ((psi:real^3->real^3) has_derivative Dp) (at y0)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Dh"; "Dp"] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h':real^3->real^3) ((psi:real^3->real^3) y0) = y0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t0 = Phi y0 /\ (ch:A->real^3) (Phi y0) = (psi:real^3->real^3) y0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `(beta:real->real^3) t0 = y0`)) THEN USE_THEN "eq" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
      EXPAND_TAC "psi" THEN REWRITE_TAC[o_THM]];
    ALL_TAC] THEN
  EXISTS_TAC `(Dh:real^3->real^3) v` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`(h':real^3->real^3) o (\s. (ch:A->real^3) ((gamma:real->A) (drop s)))`;
                          `min d d1`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x':real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP; o_THM] THEN
      DISCH_TAC THEN USE_THEN "near" (MP_TAC o SPEC `drop x'`) THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`\s. (ch:A->real^3) ((gamma:real->A) (drop s))`; `h':real^3->real^3`;
                     `v:real^3`; `Dh:real^3->real^3`; `lift t0`; `(:real^1)`]
                    GRGD_VECTOR_DERIVATIVE_CHAIN) THEN
      REWRITE_TAC[WITHIN_UNIV; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "vd" MP_TAC THEN EXPAND_TAC "ch" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Dp:real^3->real^3) ((Dh:real^3->real^3) v) = v` ASSUME_TAC THENL
   [SUBGOAL_THEN `(Dp:real^3->real^3) o (Dh:real^3->real^3) = (\h. h)` MP_TAC THENL
     [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
      EXISTS_TAC `(psi:real^3->real^3) o (h':real^3->real^3)` THEN
      EXISTS_TAC `(psi:real^3->real^3) y0` THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `?r'. &0 < r' /\ ball((psi:real^3->real^3) y0,r') SUBSET N'`
        STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `open(N':real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
        MAP_EVERY EXISTS_TAC [`\z:real^3. z`; `r':real`] THEN
        ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; o_THM] THEN X_GEN_TAC `z:real^3` THEN
        DISCH_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          can (find_term (fun t -> t = `r':real`)) (concl th))) THEN
        REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(MP_TAC o C AP_THM `v:real^3`) THEN REWRITE_TAC[o_THM]];
    ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y0:real^3) IN N`)]) o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "rfs_pullback" with Failure _ -> false))
        (concl th))) THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `Dp:real^3->real^3`;
                 `metric_local atlas (chart_at atlas ((Phi:real^3->A) y0)) (g:A->real^3^3)`;
                 `y0:real^3`; `(Dh:real^3->real^3) v`] P3N_MPULLBACK_QF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(ch:A->real^3) (Phi y0) = (psi:real^3->real^3) y0`)) THEN
  EXPAND_TAC "ch" THEN
  SUBGOAL_THEN `(Phi:real^3->A) y0 IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `W:real^3->bool`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `(Phi:real^3->A) y0`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let P3N_PARAM_INV_CONT = prove
 (`!top atlas W (Phi:real^3->A) (gamma:real->A) (beta:real->real^3) S t0.
     smooth_manifold_atlas top atlas /\ mfd_param top atlas W Phi /\
     (!s. s IN S ==> beta s IN W /\ gamma s = Phi(beta s)) /\ t0 IN S /\
     (!O. open_in top O /\ gamma t0 IN O
          ==> ?d. &0 < d /\ !s. s IN S /\ abs(s - t0) < d ==> gamma s IN O)
     ==> !e. &0 < e
             ==> ?d. &0 < d /\ !s. s IN S /\ abs(s - t0) < d ==> dist(beta s,beta t0) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast cs) THEN LABEL_TAC "cont" (last cs)) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:real^3->bool`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(beta:real->real^3) t0 IN W /\ (gamma:real->A) t0 = Phi(beta t0)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `U = ball((beta:real->real^3) t0,e) INTER W` THEN
  SUBGOAL_THEN `open_in top (IMAGE (Phi:real^3->A) U)` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (Phi:real^3->A) U =
                  {z | z IN IMAGE Phi W /\ (e':A->real^3) z IN U}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN
      EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(x:real^3) IN W` ASSUME_TAC THENL
         [UNDISCH_TAC `(x:real^3) IN U` THEN EXPAND_TAC "U" THEN SIMP_TAC[IN_INTER];
          ALL_TAC] THEN
        CONJ_TAC THENL [EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
        EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(e':A->real^3) z IN U` THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `IMAGE (Phi:real^3->A) W` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `continuous_map (subtopology top (IMAGE (Phi:real^3->A) W),
                                 subtopology euclidean W) (e':A->real^3)` THEN
    REWRITE_TAC[CONTINUOUS_MAP] THEN DISCH_THEN(MP_TAC o SPEC `U:real^3->bool` o CONJUNCT2) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `open_in (subtopology euclidean W) (U:real^3->bool)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `ball((beta:real->real^3) t0,e)` THEN
      EXPAND_TAC "U" THEN REWRITE_TAC[OPEN_IN_EUCLIDEAN; OPEN_BALL];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    SUBGOAL_THEN `IMAGE (Phi:real^3->A) W SUBSET topspace top` MP_TAC THENL
     [ASM_REWRITE_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "cont" (MP_TAC o SPEC `IMAGE (Phi:real^3->A) U`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN EXPAND_TAC "U" THEN
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd")) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "dd" (MP_TAC o C MP (CONJ (ASSUME `(s:real) IN S`) (ASSUME `abs(s - t0) < d`)) o
                 SPEC `s:real`) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(beta:real->real^3) s IN W /\ (gamma:real->A) s = Phi(beta s)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(ASSUME `!s. s IN S ==> (beta:real->real^3) s IN W /\
                                        (gamma:real->A) s = Phi(beta s)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN W /\ x IN ball((beta:real->real^3) t0,e)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN U` THEN EXPAND_TAC "U" THEN SIMP_TAC[IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `(beta:real->real^3) s = x` SUBST1_TAC THENL
   [SUBGOAL_THEN `(e':A->real^3) (Phi((beta:real->real^3) s)) = e'(Phi x)` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^3) IN ball((beta:real->real^3) t0,e)` THEN
  REWRITE_TAC[IN_BALL] THEN MESON_TAC[DIST_SYM]);;

(* ========================================================================= *)
(* The evolving cap region of Prop 16.13 in the coordinates of               *)
(* Prop 16.5.  P3N_1613_CLOSE: either alternative of Prop 16.5 gives the    *)
(* view closeness at every normalized time s with ts + s h^2 <= Tp, when    *)
(* the closed ball persists up to Tp (an event removing the ball before Tp  *)
(* would contradict the persistence).  P3N_1613_RBOUND: there the scalar     *)
(* curvature of the history at Phi y is at least h^-2 c / (2(1 - s)).       *)
(* ========================================================================= *)

let P3N_1613_CLOSE = prove
 (`!(hs:(A)rfs_history) k Phi ts h Tp g0 A W (G:real->real^3->real^3^3) theta theta0 dcl.
     rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs /\ ts = hs_time hs k /\ &0 < h /\
     theta0 < theta /\ Tp <= ts + theta0 * h pow 2 /\
     (!s. ts <= s /\ s <= Tp
          ==> IMAGE Phi {x | p3_std_dist g0 x <= A} SUBSET topspace(rfs_top_at hs s)) /\
     ts <= Tp /\ ~({x:real^3 | p3_std_dist g0 x <= A} = {}) /\
     {x | p3_std_dist g0 x <= A} SUBSET W /\
     (p3_view_close
        (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
        (&0) (&1) W (rfs_view hs) ts (inv(h pow 2)) Phi
        {s | &0 <= s /\ s < theta /\ ts + s * h pow 2 <= rfs_horizon hs /\
             ts + s * h pow 2 < rfs_horizon hs} dcl \/
      ?k'. k < k' /\ k' <= hs_count hs /\ hs_time hs k' <= rfs_horizon hs /\
           hs_time hs k' < ts + theta * h pow 2 /\
           p3_view_close
             (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
             (&0) (&1) W (rfs_view hs) ts (inv(h pow 2)) Phi
             {s | &0 <= s /\ ts + s * h pow 2 < hs_time hs k'} dcl /\
           DISJOINT (IMAGE Phi W) (topspace(hs_top hs k')))
     ==> ?J. p3_view_close
               (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
               (&0) (&1) W (rfs_view hs) ts (inv(h pow 2)) Phi J dcl /\
             !s. &0 <= s /\ ts + s * h pow 2 <= Tp ==> s IN J`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast cs) THEN ASSUME_TAC (last cs)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `ts:real`)) THEN
  SUBGOAL_THEN `&0 < h pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. hs_time (hs:(A)rfs_history) k <= s /\ s <= Tp ==> s < rfs_horizon hs`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "rfs_top_at" with Failure _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[rfs_top_at] THEN
    COND_CASES_TAC THENL
     [UNDISCH_TAC `rfs_live (hs:(A)rfs_history) s` THEN REWRITE_TAC[rfs_live; rfs_horizon] THEN
      SIMP_TAC[];
      REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; SUBSET_EMPTY; IMAGE_EQ_EMPTY] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k':num` STRIP_ASSUME_TAC) o
    check (fun th -> is_disj(concl th))) THENL
   [EXISTS_TAC `{s | &0 <= s /\ s < theta /\ hs_time hs k + s * h pow 2 <= rfs_horizon hs /\
                     hs_time hs k + s * h pow 2 < rfs_horizon (hs:(A)rfs_history)}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `hs_time hs k + s * h pow 2 < rfs_horizon (hs:(A)rfs_history)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a <= a + b`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `s * h pow 2 < theta * h pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `theta0 * h pow 2` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RMUL_EQ]];
      ASM_SIMP_TAC[REAL_LT_RMUL_EQ]];
    EXISTS_TAC `{s | &0 <= s /\ hs_time hs k + s * h pow 2 < hs_time (hs:(A)rfs_history) k'}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `Tp < hs_time (hs:(A)rfs_history) k'` MP_TAC THENL
     [GEN_REWRITE_TAC I [GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `hs_time hs k < hs_time (hs:(A)rfs_history) k'` ASSUME_TAC THENL
       [MATCH_MP_TAC APX_HS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `hs_time (hs:(A)rfs_history) k'` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "rfs_top_at" with Failure _ -> false))
            (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `k':num`] P3N_VIEW_AT_EVENT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[rfs_view; rfs_vtop] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      UNDISCH_TAC `DISJOINT (IMAGE (Phi:real^3->A) W) (topspace(hs_top (hs:(A)rfs_history) k'))` THEN
      UNDISCH_TAC `~({x:real^3 | p3_std_dist g0 x <= A} = {})` THEN
      UNDISCH_TAC `{x:real^3 | p3_std_dist g0 x <= A} SUBSET W` THEN SET_TAC[];
      DISCH_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC]]);;

let P3N_1613_RBOUND = prove
 (`!c dl0 (hs:(A)rfs_history) Phi ts h (G:real->real^3->real^3^3) g0 W J dcl s y.
     (!(G0:real^3->real^3^3) H V z dl.
        metric_field V G0 /\ metric_field V H /\ z IN V /\ c <= lscalar G0 z /\
        (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G0 z u v) /\
        &0 < dl /\ dl <= dl0 /\ lck_dist2 (rfs_kreg dl) G0 H z < dl pow 2
        ==> lscalar G0 z / &2 <= lscalar H z) /\
     &0 < c /\ p3_std_flow g0 (&1) G /\
     (!t x. &0 <= t /\ t < &1 ==> c / (&1 - t) <= lscalar (G t) x) /\
     (!t x u v. &0 <= t /\ t < &1 /\ ~collinear {vec 0,u,v}
                ==> &0 <= lsectional (G t) x u v) /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) W (rfs_view hs) ts (inv(h pow 2)) Phi J dcl /\
     s IN J /\ &0 <= s /\ s < &1 /\ open W /\ y IN W /\ &0 < h /\ &0 < dcl /\ dcl <= dl0 /\
     smooth_manifold_atlas (rfs_vtop (rfs_view hs) (ts + s * h pow 2))
                           (rfs_vatlas (rfs_view hs) (ts + s * h pow 2)) /\
     riemannian_metric (rfs_vatlas (rfs_view hs) (ts + s * h pow 2))
                       (rfs_vmetric (rfs_view hs) (ts + s * h pow 2))
     ==> inv(h pow 2) * c / (&2 * (&1 - s)) <=
         mfd_scalar (rfs_vatlas (rfs_view hs) (ts + s * h pow 2))
                    (rfs_vmetric (rfs_view hs) (ts + s * h pow 2)) (Phi y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "LS" (hd cs) THEN MAP_EVERY ASSUME_TAC (tl cs)) THEN
  SUBGOAL_THEN `&0 < inv(h pow 2) /\ !q. q / inv(h pow 2) = q * h pow 2`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[real_div; REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV THEN
    ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`; `inv(h pow 2)`;
                 `G:real->real^3->real^3^3`; `W:real^3->bool`; `J:real->bool`; `dcl:real`;
                 `s:real`] P3N_VIEW_CLOSE_ELIM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi':A->real^3`)
    (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `mfd_param (rfs_vtop (rfs_view (hs:(A)rfs_history)) (ts + s * h pow 2))
                  (rfs_vatlas (rfs_view hs) (ts + s * h pow 2)) W Phi` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_param] THEN EXISTS_TAC `psi':A->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field W ((G:real->real^3->real^3^3) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[p3_std_flow; p3_partial_std];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field W (p3n_cfl (hs:(A)rfs_history) Phi ts (inv(h pow 2)) s)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p3n_cfl] THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `rfs_vtop (rfs_view (hs:(A)rfs_history)) (ts + s * h pow 2)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c <= lscalar ((G:real->real^3->real^3^3) s) y /\
                c / (&1 - s) <= lscalar (G s) y` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> y <= z ==> x <= z`) THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= c * s ==> c * (&1 - s) <= c`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "LS" (MP_TAC o SPECL [`(G:real->real^3->real^3^3) s`;
    `p3n_cfl (hs:(A)rfs_history) Phi ts (inv(h pow 2)) s`; `W:real^3->bool`; `y:real^3`;
    `dcl:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (rfs_view (hs:(A)rfs_history)) (ts + s * h pow 2)`;
                 `rfs_vatlas (rfs_view (hs:(A)rfs_history)) (ts + s * h pow 2)`;
                 `rfs_vmetric (rfs_view (hs:(A)rfs_history)) (ts + s * h pow 2)`;
                 `W:real^3->bool`; `Phi:real^3->A`; `inv(h pow 2)`; `y:real^3`]
                P2B9_PARAM_LSCALAR_SCALED) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM p3n_cfl] THEN
  SUBGOAL_THEN `(\z. inv(h pow 2) %% rfs_pullback (rfs_vatlas (rfs_view (hs:(A)rfs_history))
                       (ts + s * h pow 2)) Phi (rfs_vmetric (rfs_view hs) (ts + s * h pow 2)) z) =
                p3n_cfl hs Phi ts (inv(h pow 2)) s` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[p3n_cfl]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `R = mfd_scalar (rfs_vatlas (rfs_view (hs:(A)rfs_history)) (ts + s * h pow 2))
                    (rfs_vmetric (rfs_view hs) (ts + s * h pow 2)) ((Phi:real^3->A) y)` THEN
  ABBREV_TAC `q = inv(h pow 2)` THEN
  SUBGOAL_THEN `R = q * (R / q)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lscalar ((G:real->real^3->real^3^3) s) y / &2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `c / (&2 * (&1 - s)) = (c / (&1 - s)) / &2` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> a / &2 <= b / &2`) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The radial derivative along a curve in the evolving cap                  *)
(* region (P3N_1613_DERIV).  At a backward time tau inside (0,b) that is    *)
(* not an event time, with gamma = Phi o beta in the closed A-ball and beta *)
(* tau in the shell where the model is close to the cylinder, the function   *)
(* d o beta has a derivative f' with f'^2 <= 25/16 h^-2 |X|^2, |X| the      *)
(* speed of gamma in the history metric at time Tp - tau.                   *)
(* ========================================================================= *)

let P3N_1613_DERIV = prove
 (`!(hs:(A)rfs_history) Phi ts h Tp b (gamma:real->A) (beta:real->real^3) g0 A0 A
    (G:real->real^3->real^3^3) J dcl sg tau.
     rfs_history_ok hs /\ p3_std_initial g0 A0 /\ p3_std_flow g0 (&1) G /\
     &0 < h /\ &0 < A /\ &0 < tau /\ tau < b /\ &0 <= sg /\ sg < &1 /\
     ts + sg * h pow 2 = Tp - tau /\ Tp - tau < rfs_horizon hs /\ &0 <= Tp - tau /\
     ~(?j. Tp - tau = hs_time hs j) /\
     rfs_st_curve hs Tp gamma (&0) b /\
     (!s. s IN real_interval[&0,b]
          ==> p3_std_dist g0 (beta s) <= A /\ gamma s = Phi(beta s)) /\
     A / &2 <= p3_std_dist g0 (beta tau) /\
     lck_dist2 (rfs_kreg (&1 / &10)) (mpullback (p3_std_nc g0 A0) (cylinder_flow sg)) (G sg)
               (beta tau) < (&1 / &10) pow 2 /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) {x | p3_std_dist g0 x < A + &1} (rfs_view hs) ts (inv(h pow 2)) Phi J dcl /\
     sg IN J /\ &0 < dcl /\ dcl <= &1 / &10
     ==> ?f'. ((\s. p3_std_dist g0 (beta s)) has_real_derivative f') (atreal tau) /\
              f' pow 2 <= (&25 / &16 * inv(h pow 2)) *
                          mfd_speed (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau))
                                    gamma (&0) b tau pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC cs) THEN
  ABBREV_TAC `t = Tp - tau` THEN
  ABBREV_TAC `W = {x:real^3 | p3_std_dist g0 x < A + &1}` THEN
  ABBREV_TAC `y0 = (beta:real->real^3) tau` THEN
  SUBGOAL_THEN `&0 < inv(h pow 2) /\ ts + sg / inv(h pow 2) = t` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV; REAL_POW_LT; real_div; REAL_INV_INV] THEN
    ASM_REWRITE_TAC[GSYM real_div] THEN ASM_REWRITE_TAC[real_div; REAL_INV_INV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`; `inv(h pow 2)`;
                 `G:real->real^3->real^3^3`; `W:real^3->bool`; `J:real->bool`; `dcl:real`;
                 `sg:real`] P3N_VIEW_CLOSE_ELIM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi':A->real^3`)
    (X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P3_HIST_VIEW_SLICES) THEN
  ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric]) THEN
  SUBGOAL_THEN `mfd_param (rfs_top_at (hs:(A)rfs_history) t) (rfs_atlas_at hs t) W Phi`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_param] THEN EXISTS_TAC `psi':A->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN real_interval[&0,b] ==> (beta:real->real^3) s IN W`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= A ==> x < A + &1`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_st_curve] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_st_curve" with Failure _ -> false)) THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) t`; `rfs_atlas_at (hs:(A)rfs_history) t`;
                 `W:real^3->bool`; `Phi:real^3->A`; `gamma:real->A`; `beta:real->real^3`;
                 `real_interval[&0,b]`; `tau:real`] P3N_PARAM_INV_CONT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `W:real^3->bool`)) (concl th) &&
          can (find_term (fun t -> t = `real_interval[&0,b]`)) (concl th))) THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL];
        FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `p3_std_dist g0`)) (concl th) &&
          can (find_term (fun t -> t = `real_interval[&0,b]`)) (concl th))) THEN
        ASM_SIMP_TAC[IN_REAL_INTERVAL]];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`tau:real`; `O:A->bool`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false))
            (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC[]];
    DISCH_THEN(LABEL_TAC "bcont")] THEN
  (* the stage at time t and the preferred chart at gamma tau *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] RFS_SLAB) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k = rfs_slab (hs:(A)rfs_history) t` THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_top_at (hs:(A)rfs_history) t = hs_top hs k /\
                rfs_atlas_at hs t = hs_atlas hs k` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `rfs_live (hs:(A)rfs_history) t` ASSUME_TAC THENL
     [REWRITE_TAC[rfs_live; GSYM rfs_horizon] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[rfs_top_at; rfs_atlas_at];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) tau = (Phi:real^3->A) y0` ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `p3_std_dist g0`)) (concl th) &&
      can (find_term (fun t -> t = `real_interval[&0,b]`)) (concl th))) THEN
    ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) tau IN topspace(rfs_top_at hs t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) t`; `rfs_atlas_at (hs:(A)rfs_history) t`;
                   `W:real^3->bool`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y0:real^3) IN W` MP_TAC THENL
     [EXPAND_TAC "y0" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LT_IMP_LE];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (rfs_atlas_at (hs:(A)rfs_history) t) ((gamma:real->A) tau)` THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^3)) IN hs_atlas (hs:(A)rfs_history) k /\
                (gamma:real->A) tau IN FST c /\ open_in (hs_top hs k) (FST c)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) t`; `rfs_atlas_at (hs:(A)rfs_history) t`;
                   `(gamma:real->A) tau`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `rfs_top_at (hs:(A)rfs_history) t = hs_top hs k`;
                                ASSUME `rfs_atlas_at (hs:(A)rfs_history) t = hs_atlas hs k`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* facts about y0 *)
  SUBGOAL_THEN `(y0:real^3) IN W /\ &0 < p3_std_dist g0 y0 /\ p3_std_dist g0 y0 < A + &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `p3_std_dist g0 (y0:real^3) <= A` ASSUME_TAC THENL
     [EXPAND_TAC "y0" THEN
      FIRST_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `p3_std_dist g0`)) (concl th) &&
        can (find_term (fun t -> t = `real_interval[&0,b]`)) (concl th))) THEN
      ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y0:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < p3_std_dist g0 (y0:real^3)` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the open time slab around tau inside the C1 set of the chart c *)
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k < t` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(?j. t = hs_time (hs:(A)rfs_history) j)` THEN REWRITE_TAC[] THEN
    EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`tau:real`; `FST(c:(A->bool)#(A->real^3))`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      REWRITE_TAC[ASSUME `Tp - tau = t`;
                  ASSUME `rfs_top_at (hs:(A)rfs_history) t = hs_top hs k`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d1")))] THEN
  ABBREV_TAC `de = min (min d1 tau)
                       (min (b - tau) (min (t - hs_time (hs:(A)rfs_history) k)
                                           (hs_time hs (k + 1) - t)))` THEN
  SUBGOAL_THEN `&0 < de /\ de <= d1 /\ de <= tau /\ de <= b - tau /\
                de <= t - hs_time (hs:(A)rfs_history) k /\ de <= hs_time hs (k + 1) - t`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "de" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`k:num`; `c:(A->bool)#(A->real^3)`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "continuously_differentiable"
                             with Failure _ -> false)) (concl th))) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  ABBREV_TAC `Sc = {s | &0 < drop s /\ drop s <= b /\ hs_time (hs:(A)rfs_history) k <= Tp - drop s /\
                        Tp - drop s < hs_time hs (k + 1) /\
                        (gamma:real->A) (drop s) IN FST(c:(A->bool)#(A->real^3))}` THEN
  SUBGOAL_THEN `ball(lift tau,de) SUBSET Sc` (LABEL_TAC "ball") THENL
   [EXPAND_TAC "Sc" THEN
    REWRITE_TAC[SUBSET; FORALL_LIFT; IN_BALL; DIST_LIFT; IN_ELIM_THM; LIFT_DROP] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= x /\ x <= b /\ abs(x - tau) < d1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      USE_THEN "d1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the chart velocity v at tau *)
  SUBGOAL_THEN `(\s. SND(c:(A->bool)#(A->real^3)) ((gamma:real->A) (drop s)))
                differentiable (at (lift tau))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\s. SND(c:(A->bool)#(A->real^3)) ((gamma:real->A) (drop s)))
                  differentiable (at (lift tau) within Sc)` MP_TAC THENL
     [UNDISCH_TAC `continuously_differentiable 1 Sc
                     (\s. SND(c:(A->bool)#(A->real^3)) ((gamma:real->A) (drop s)))` THEN
      REWRITE_TAC[ONE; continuously_differentiable; differentiable] THEN
      DISCH_THEN(X_CHOOSE_THEN `D:real^1->real^1->real^3` (MP_TAC o SPEC `lift tau` o CONJUNCT1)) THEN
      ANTS_TAC THENL
       [USE_THEN "ball" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        REWRITE_TAC[CENTRE_IN_BALL] THEN FIRST_ASSUM ACCEPT_TAC;
        DISCH_TAC THEN EXISTS_TAC `(D:real^1->real^1->real^3) (lift tau)` THEN
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\s. SND(c:(A->bool)#(A->real^3)) ((gamma:real->A) (drop s))`; `lift tau`;
                   `ball(lift tau,de)`] DIFFERENTIABLE_WITHIN_OPEN) THEN
    REWRITE_TAC[CENTRE_IN_BALL; OPEN_BALL] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_WITHIN_SUBSET THEN EXISTS_TAC `Sc:real^1->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `v = vector_derivative (\s. SND(c:(A->bool)#(A->real^3)) ((gamma:real->A) (drop s)))
                                    (at (lift tau))` THEN
  SUBGOAL_THEN `((\s. SND(c:(A->bool)#(A->real^3)) ((gamma:real->A) (drop s)))
                 has_vector_derivative v) (at (lift tau))` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_velocity (rfs_atlas_at (hs:(A)rfs_history) t) (gamma:real->A) (&0) b tau = v`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_velocity;
                ASSUME `chart_at (rfs_atlas_at (hs:(A)rfs_history) t) ((gamma:real->A) tau) = c`] THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v dot (rfs_metric_at (hs:(A)rfs_history) t ((gamma:real->A) tau) ** v)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) t`; `rfs_atlas_at (hs:(A)rfs_history) t`;
                   `rfs_metric_at (hs:(A)rfs_history) t`; `(gamma:real->A) tau`]
                  RIEMANNIAN_METRIC_POS) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT2) THEN
    ASM_CASES_TAC `v:real^3 = vec 0` THEN
    ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_speed (rfs_atlas_at (hs:(A)rfs_history) t) (rfs_metric_at hs t) (gamma:real->A)
                          (&0) b tau pow 2 =
                v dot (rfs_metric_at hs t (gamma tau) ** v)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_speed;
                ASSUME `mfd_velocity (rfs_atlas_at (hs:(A)rfs_history) t) (gamma:real->A) (&0) b tau = v`] THEN
    MATCH_MP_TAC SQRT_POW_2 THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the velocity w of beta *)
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) t`; `rfs_atlas_at (hs:(A)rfs_history) t`;
                 `rfs_metric_at (hs:(A)rfs_history) t`; `W:real^3->bool`; `Phi:real^3->A`;
                 `gamma:real->A`; `beta:real->real^3`; `tau:real`; `v:real^3`;
                 `min tau (b - tau)`] P3N_PARAM_CURVE_DERIV) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[ASSUME `(beta:real->real^3) tau = y0`] THEN FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "bcont" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
      DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d2"))) THEN
      EXISTS_TAC `min d2 (min tau (b - tau))` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN USE_THEN "d2" MATCH_MP_TAC THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `p3_std_dist g0`)) (concl th) &&
        can (find_term (fun t -> t = `real_interval[&0,b]`)) (concl th))) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REWRITE_TAC[ASSUME `(beta:real->real^3) tau = y0`;
                  SYM(ASSUME `(gamma:real->A) tau = (Phi:real^3->A) y0`);
                  ASSUME `chart_at (rfs_atlas_at (hs:(A)rfs_history) t) ((gamma:real->A) tau) = c`] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o REWRITE_RULE[ASSUME `(beta:real->real^3) tau = y0`;
                               SYM(ASSUME `(gamma:real->A) tau = (Phi:real^3->A) y0`)]))) THEN
  (* the derivative of the distance along beta *)
  EXISTS_TAC `sqrt(p3s_rad_a g0 (norm(y0:real^3))) * (w dot y0) / norm y0` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
    SUBGOAL_THEN `lift o (\s. p3_std_dist g0 ((beta:real->real^3) s)) o drop =
                  (\z. lift(p3_std_dist g0 z)) o (\s. beta(drop s))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\s. (beta:real->real^3) (drop s)`; `\z. lift(p3_std_dist g0 (z:real^3))`;
                   `w:real^3`;
                   `\u. lift(sqrt(p3s_rad_a g0 (norm(y0:real^3))) * (u dot y0) / norm y0)`;
                   `lift tau`; `(:real^1)`] GRGD_VECTOR_DERIVATIVE_CHAIN) THEN
    BETA_TAC THEN REWRITE_TAC[WITHIN_UNIV; LIFT_DROP; ASSUME `(beta:real->real^3) tau = y0`] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC P3S_DIST_HAS_DERIV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the bound via the cylinder, the model flow and the history *)
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `y0:real^3`; `sg:real`; `w:real^3`]
                P3N_NC_RADIAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                  (G:real->real^3->real^3^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_flow g0 (&1) (G:real->real^3->real^3^3)` THEN
    REWRITE_TAC[p3_std_flow; p3_partial_std] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field W (p3n_cfl (hs:(A)rfs_history) Phi ts (inv(h pow 2)) sg)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`; `inv(h pow 2)`; `sg:real`;
                   `W:real^3->bool`] P3N_CFL_FIELD) THEN
    REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    REWRITE_TAC[ASSUME `ts + sg / inv(h pow 2) = t`] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `V = {x:real^3 | &0 < p3_std_dist g0 x /\ p3_std_dist g0 x < A + &1}` THEN
  SUBGOAL_THEN `metric_field V (mpullback (p3_std_nc g0 A0) (cylinder_flow sg))` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC P3N_NC_CYL_FIELD THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open(V:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field V (mpullback (p3_std_nc g0 A0) (cylinder_flow sg))` THEN
    SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `mpullback (p3_std_nc g0 A0) (cylinder_flow sg)`;
                 `(G:real->real^3->real^3^3) sg`;
                 `p3n_cfl (hs:(A)rfs_history) Phi ts (inv(h pow 2)) sg`;
                 `y0:real^3`; `w:real^3`; `rfs_kreg (&1 / &10)`; `rfs_kreg dcl`;
                 `&1 / &10`; `dcl:real`;
                 `(sqrt(p3s_rad_a g0 (norm(y0:real^3))) * (w dot y0) / norm y0) pow 2`]
                P3N_QF_CHAIN) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `W:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["V"; "W"] THEN
      SIMP_TAC[SUBSET; IN_ELIM_THM];
      EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dd:real` THEN CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `rfs_kreg dcl`)) (concl th))) THEN
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      REAL_ARITH_TAC; REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[REAL_LE_POW_2]; FIRST_ASSUM ACCEPT_TAC];
    DISCH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!z. q <= &25 / &16 * z /\ z = m * p ==> q <= (&25 / &16 * m) * p`) THEN
  EXISTS_TAC `w dot (p3n_cfl (hs:(A)rfs_history) Phi ts (inv(h pow 2)) sg y0 ** w)` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[p3n_cfl; rfs_view; rfs_vatlas; rfs_vmetric] THEN BETA_TAC THEN
  REWRITE_TAC[ASSUME `ts + sg / inv(h pow 2) = t`; MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `v dot (rfs_metric_at (hs:(A)rfs_history) t ((gamma:real->A) tau) ** v)` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ========================================================================= *)
(* Arithmetic and sign facts for Prop 16.13, the continuity of              *)
(* the distance along a continuous curve in a sublevel set, and the slice   *)
(* facts at a backward time tau (live slice, slab parameter in J, scalar    *)
(* lower bound h^-2 c/(2(1-s)) from P3N_1613_RBOUND).                       *)
(* ========================================================================= *)

(* the time constant theta0 = 1 - exp(-2 ell/c)/4 lies in (3/4,1) *)

let P3N_THETA0_BOUNDS = prove
 (`!c ell. &0 < c /\ &0 < ell
           ==> &3 / &4 < &1 - exp(--(&2 * ell / c)) / &4 /\
               &1 - exp(--(&2 * ell / c)) / &4 < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < exp(--(&2 * ell / c)) /\ exp(--(&2 * ell / c)) < &1` MP_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT; REAL_NEG_LT0] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
    REAL_ARITH_TAC]);;

(* the energy of the top case: c/2 log((1/2)/(1 - theta0)) = c/2 log 2 + ell *)

let P3N_1613_TOP_ARITH = prove
 (`!c ell. &0 < c /\ &0 < ell
           ==> ell < c / &2 * (log(&1 / &2) - log(&1 - (&1 - exp(--(&2 * ell / c)) / &4)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `&1 - (&1 - x / &4) = x / &4`] THEN
  SIMP_TAC[LOG_DIV; REAL_EXP_POS_LT; REAL_ARITH `&0 < &4 /\ &0 < &2 /\ &0 < &1`;
           LOG_EXP; LOG_1] THEN
  SUBGOAL_THEN `log(&4) = &2 * log(&2)` SUBST1_TAC THENL
   [SUBGOAL_THEN `&4 = &2 * &2` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[LOG_MUL; REAL_ARITH `&0 < &2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&2` LOG_POS_LT) THEN ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `c * (ell / c) = ell` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* the side case: A/2 <= K/2 (lam b + en/lam) with K = 5/(4h), lam =       *)
(* sqrt(ell)/h, b <= h^2 and A > 5/2 sqrt(ell) force en > ell             *)

let P3N_1613_SIDE_ARITH = prove
 (`!A h ell b en.
     &0 < h /\ &0 < ell /\ &0 <= b /\ b <= h pow 2 /\ &5 / &2 * sqrt ell < A /\
     A / &2 <= (&5 / (&4 * h)) / &2 * (sqrt ell / h * b + en / (sqrt ell / h))
     ==> ell < en`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `q = sqrt ell` THEN
  SUBGOAL_THEN `&0 < q /\ q pow 2 = ell` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(&5 / (&4 * h)) / &2 * (q / h * b + en / (q / h)) =
                &5 / &8 * (q * (b / h pow 2) + en / q)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `&0 < h` THEN UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `q * (b / h pow 2) <= q` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `q * x <= q * &1 ==> q * x <= q`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `en / q <= q` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REWRITE_TAC[GSYM REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* nonnegative sectional curvature of the standard flow on [0,1) *)

let P3N_STD_SEC_NONNEG = prove
 (`!g0 A0 (G:real->real^3->real^3^3).
     P2_THM_12_5_STATEMENT /\ p3_std_initial g0 A0 /\ p3_std_flow g0 (&1) G
     ==> !t x u v. &0 <= t /\ t < &1 /\ ~collinear {vec 0,u,v}
                   ==> &0 <= lsectional (G t) x u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM P2C_OPEN_SET_MFD_SECTIONAL] THEN
  ASM_CASES_TAC `t = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(G:real->real^3->real^3^3) (&0) = g0` SUBST1_TAC THENL
     [UNDISCH_TAC `p3_std_flow g0 (&1) (G:real->real^3->real^3^3)` THEN
      REWRITE_TAC[p3_std_flow; p3_partial_std] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `P2_THM_12_5_STATEMENT` THEN REWRITE_TAC[P2_THM_12_5_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`&1`; `G:real->real^3->real^3^3`] o CONJUNCT2) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `u:real^3`; `v:real^3`] o CONJUNCT2) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REAL_ARITH_TAC]);;

(* the distance from the tip along a curve that is continuous within       *)
(* [0,b] and stays in a sublevel set is real-continuous on [0,b]           *)

let P3N_DIST_COMP_CONT = prove
 (`!g0 A0 (beta:real->real^3) b A.
     p3_std_initial g0 A0 /\ &0 <= A /\
     (!s. s IN real_interval[&0,b] ==> p3_std_dist g0 (beta s) <= A) /\
     (!s0. s0 IN real_interval[&0,b]
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !s. s IN real_interval[&0,b] /\ abs(s - s0) < d
                               ==> dist(beta s,beta s0) < e)
     ==> (\s. p3_std_dist g0 (beta s)) real_continuous_on real_interval[&0,b]`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sub") (LABEL_TAC "bc")))) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A:real`] P3N_STD_SUBLEVEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `!s. s IN real_interval[&0,b]
                    ==> norm((beta:real->real^3) s) <= p3s_rad_rinv g0 A`
  (LABEL_TAC "nb") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(beta:real->real^3) s IN {x:real^3 | p3_std_dist g0 x <= A}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_CBALL_0]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 A`] P3S_RHO_CONT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "rho" o REWRITE_RULE[real_continuous_on; IN_REAL_INTERVAL]) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_ALT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
  REWRITE_TAC[real_continuous_on] THEN
  X_GEN_TAC `s0:real` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "rho" (MP_TAC o SPEC `norm((beta:real->real^3) s0)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[NORM_POS_LE] THEN USE_THEN "nb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d1"))) THEN
  USE_THEN "bc" (MP_TAC o C MP (ASSUME `&0 < d1`) o SPEC `d1:real` o
                 C MP (ASSUME `s0 IN real_interval[&0,b]`) o SPEC `s0:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d2"))) THEN
  EXISTS_TAC `d2:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "d1" MATCH_MP_TAC THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
   [USE_THEN "nb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm((beta:real->real^3) s - beta s0)` THEN
  REWRITE_TAC[REAL_ABS_SUB_NORM; GSYM dist] THEN
  USE_THEN "d2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* the slice facts at a backward time tau in [0,b] *)

let P3N_1613_SLICE = prove
 (`!c dl0 (hs:(A)rfs_history) Phi ts h Tp tp b (gamma:real->A) g0 A0 A
    (G:real->real^3->real^3^3) J dcl theta0 tau.
     (!(G0:real^3->real^3^3) H V z dl.
        metric_field V G0 /\ metric_field V H /\ z IN V /\ c <= lscalar G0 z /\
        (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G0 z u v) /\
        &0 < dl /\ dl <= dl0 /\ lck_dist2 (rfs_kreg dl) G0 H z < dl pow 2
        ==> lscalar G0 z / &2 <= lscalar H z) /\
     &0 < c /\ p3_std_flow g0 (&1) G /\
     (!t x. &0 <= t /\ t < &1 ==> c / (&1 - t) <= lscalar (G t) x) /\
     (!t x u v. &0 <= t /\ t < &1 /\ ~collinear {vec 0,u,v}
                ==> &0 <= lsectional (G t) x u v) /\
     rfs_history_ok hs /\ p3_std_initial g0 A0 /\ &0 < h /\ &0 <= A /\ theta0 < &1 /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) {x | p3_std_dist g0 x < A + &1} (rfs_view hs) ts (inv(h pow 2)) Phi J dcl /\
     (!s. &0 <= s /\ ts + s * h pow 2 <= Tp ==> s IN J) /\
     &0 < dcl /\ dcl <= dl0 /\
     Tp <= ts + theta0 * h pow 2 /\ ts <= tp /\ b = Tp - tp /\
     (!s. ts <= s /\ s <= Tp
          ==> IMAGE Phi {x | p3_std_dist g0 x <= A} SUBSET topspace(rfs_top_at hs s)) /\
     (!tau. &0 <= tau /\ tau <= b ==> gamma tau IN IMAGE Phi {x | p3_std_dist g0 x <= A}) /\
     &0 <= tau /\ tau <= b
     ==> Tp - tau < rfs_horizon hs /\ &0 <= Tp - tau /\
         &0 <= (Tp - tau - ts) / h pow 2 /\ (Tp - tau - ts) / h pow 2 <= theta0 /\
         ts + (Tp - tau - ts) / h pow 2 * h pow 2 = Tp - tau /\
         (Tp - tau - ts) / h pow 2 IN J /\
         inv(h pow 2) * c / (&2 * (&1 - (Tp - tau - ts) / h pow 2)) <=
         mfd_scalar (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau)) (gamma tau)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  ABBREV_TAC `sg = (Tp - tau - ts) / h pow 2` THEN
  SUBGOAL_THEN `&0 < h pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `ts + sg * h pow 2 = Tp - tau` ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN UNDISCH_TAC `&0 < h pow 2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sg /\ sg <= theta0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sg IN (J:real->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `J:real->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Phi:real^3->A) (vec 0) IN topspace(rfs_top_at (hs:(A)rfs_history) (Tp - tau))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `Tp - tau` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "topspace" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Tp - tau /\ Tp - tau < rfs_horizon (hs:(A)rfs_history)` STRIP_ASSUME_TAC
  THENL
   [MATCH_MP_TAC P2A_TOPSPACE_LIVE THEN EXISTS_TAC `(Phi:real^3->A) (vec 0)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `gamma:real->A`)) (concl th))) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `sg < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `open {x:real^3 | p3_std_dist g0 x < A + &1}` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A + &1`] P3N_STD_BALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN {x:real^3 | p3_std_dist g0 x < A + &1}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `ts + sg * h pow 2`] P3_HIST_VIEW_SLICES) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:real`; `dl0:real`; `hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`;
                 `h:real`; `G:real->real^3->real^3^3`; `g0:real^3->real^3^3`;
                 `{x:real^3 | p3_std_dist g0 x < A + &1}`; `J:real->bool`; `dcl:real`;
                 `sg:real`; `y:real^3`] P3N_1613_RBOUND) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `ts + sg * h pow 2 = Tp - tau`; rfs_view; rfs_vatlas; rfs_vmetric] THEN
  REWRITE_TAC[SYM(ASSUME `(gamma:real->A) tau = (Phi:real^3->A) y`)] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The two cases of Prop 16.13.  Basic facts of p3_struct at               *)
(* an event, injectivity of the view parametrization, continuity of the     *)
(* preimage curve, the top case (scalar curvature integral) and the side    *)
(* case (radial derivative bound with AM-GM, P3N_ENERGY_SIDE).              *)
(* ========================================================================= *)

let P3N_STRUCT_BASIC = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) k.
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ p3_hfun C hf /\ k <= hs_count hs
     ==> rfs_history_ok hs /\ &0 <= hs_time hs k /\ &0 < p3_hscale hf rp dl (hs_time hs k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history) /\
                (!t. &0 <= t ==> &0 < (rp:real->real) t /\ &0 < (dl:real->real) t)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= hs_time (hs:(A)rfs_history) k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `0`; `k:num`] APX_HS_TIME_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN SIMP_TAC[rfs_history_ok];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `hs_time (hs:(A)rfs_history) k` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> t = `rp:real->real`)) (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  UNDISCH_TAC `p3_hfun C (hf:real->real->real)` THEN REWRITE_TAC[p3_hfun; p3_hscale] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`(dl:real->real) (hs_time (hs:(A)rfs_history) k) * (rp:real->real) (hs_time hs k)`;
    `(dl:real->real) (hs_time (hs:(A)rfs_history) k)`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; SIMP_TAC[]]);;

(* the view parametrization is injective on its domain *)

let P3N_VIEW_CLOSE_INJ = prove
 (`!(hs:(A)rfs_history) Phi ts Q (G:real->real^3->real^3^3) W J dcl s.
     rfs_history_ok hs /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) W (rfs_view hs) ts Q Phi J dcl /\
     s IN J /\ &0 <= s /\ s < &1
     ==> !x y. x IN W /\ y IN W /\ Phi x = Phi y ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`; `Q:real`;
                 `G:real->real^3->real^3^3`; `W:real^3->bool`; `J:real->bool`; `dcl:real`;
                 `s:real`] P3N_VIEW_CLOSE_ELIM) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi':A->real^3` o CONJUNCT1 o CONJUNCT2) THEN
  MP_TAC(ISPECL [`rfs_vtop (rfs_view (hs:(A)rfs_history)) (ts + s / Q)`;
                 `rfs_vatlas (rfs_view (hs:(A)rfs_history)) (ts + s / Q)`;
                 `W:real^3->bool`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`hs:(A)rfs_history`; `ts + s / Q`] P3_HIST_VIEW_SLICES) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      REWRITE_TAC[mfd_param] THEN EXISTS_TAC `psi':A->real^3` THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(e':A->real^3) ((Phi:real^3->A) x)` THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    SUBST1_TAC(ASSUME `(Phi:real^3->A) x = Phi y`) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* continuity of the preimage curve beta within [0,b] at a point s0 *)

let P3N_1613_BETA_CONT = prove
 (`!(hs:(A)rfs_history) Phi ts h Tp b (gamma:real->A) (beta:real->real^3) g0 A
    (G:real->real^3->real^3^3) J dcl sg s0.
     rfs_history_ok hs /\ &0 < h /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) {x | p3_std_dist g0 x < A + &1} (rfs_view hs) ts (inv(h pow 2)) Phi J dcl /\
     rfs_st_curve hs Tp gamma (&0) b /\
     (!s. s IN real_interval[&0,b]
          ==> p3_std_dist g0 (beta s) <= A /\ gamma s = Phi(beta s)) /\
     s0 IN real_interval[&0,b] /\ ts + sg * h pow 2 = Tp - s0 /\ sg IN J /\
     &0 <= sg /\ sg < &1
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !s. s IN real_interval[&0,b] /\ abs(s - s0) < d
                         ==> dist(beta s,beta s0) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  SUBGOAL_THEN `&0 <= s0 /\ s0 <= b` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `s0 IN real_interval[&0,b]` THEN REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `ts + sg / inv(h pow 2) = Tp - s0` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_INV] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`; `inv(h pow 2)`;
                 `G:real->real^3->real^3^3`; `{x:real^3 | p3_std_dist g0 x < A + &1}`;
                 `J:real->bool`; `dcl:real`; `sg:real`] P3N_VIEW_CLOSE_ELIM) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi':A->real^3` o
    REWRITE_RULE[ASSUME `ts + sg / inv(h pow 2) = Tp - s0`; rfs_view; rfs_vtop; rfs_vatlas] o
    CONJUNCT1 o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_param (rfs_top_at (hs:(A)rfs_history) (Tp - s0)) (rfs_atlas_at hs (Tp - s0))
                          {x:real^3 | p3_std_dist g0 x < A + &1} Phi` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_param] THEN EXISTS_TAC `psi':A->real^3` THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `Tp - s0`] P3_HIST_VIEW_SLICES) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_st_curve] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_st_curve" with Failure _ -> false)) THEN
  MATCH_MP_TAC P3N_PARAM_INV_CONT THEN
  MAP_EVERY EXISTS_TAC [`rfs_top_at (hs:(A)rfs_history) (Tp - s0)`;
                        `rfs_atlas_at (hs:(A)rfs_history) (Tp - s0)`;
                        `{x:real^3 | p3_std_dist g0 x < A + &1}`; `Phi:real^3->A`;
                        `gamma:real->A`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MP (ASSUME `s IN real_interval[&0,b]`) o SPEC `s:real` o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `beta:real->real^3`)) (concl th))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`s0:real`; `O:A->bool`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN MESON_TAC[]]);;

(* the top case: the curve starts at the top time ts + theta0 h^2 *)

let P3N_1613_TOP = prove
 (`!c dl0 (hs:(A)rfs_history) Phi ts h Tp tp (gamma:real->A) g0 A0 A
    (G:real->real^3->real^3^3) J dcl ell theta0.
     (!(G0:real^3->real^3^3) H V z dl.
        metric_field V G0 /\ metric_field V H /\ z IN V /\ c <= lscalar G0 z /\
        (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G0 z u v) /\
        &0 < dl /\ dl <= dl0 /\ lck_dist2 (rfs_kreg dl) G0 H z < dl pow 2
        ==> lscalar G0 z / &2 <= lscalar H z) /\
     &0 < c /\ p3_std_flow g0 (&1) G /\
     (!t x. &0 <= t /\ t < &1 ==> c / (&1 - t) <= lscalar (G t) x) /\
     (!t x u v. &0 <= t /\ t < &1 /\ ~collinear {vec 0,u,v}
                ==> &0 <= lsectional (G t) x u v) /\
     rfs_history_ok hs /\ p3_std_initial g0 A0 /\ &0 < h /\ &0 <= A /\ &0 < ell /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) {x | p3_std_dist g0 x < A + &1} (rfs_view hs) ts (inv(h pow 2)) Phi J dcl /\
     (!s. &0 <= s /\ ts + s * h pow 2 <= Tp ==> s IN J) /\
     &0 < dcl /\ dcl <= dl0 /\
     theta0 = &1 - exp(--(&2 * ell / c)) / &4 /\ Tp = ts + theta0 * h pow 2 /\
     ts <= tp /\ tp <= ts + h pow 2 / &2 /\ tp <= Tp /\
     (!s. ts <= s /\ s <= Tp
          ==> IMAGE Phi {x | p3_std_dist g0 x <= A} SUBSET topspace(rfs_top_at hs s)) /\
     (!tau. &0 <= tau /\ tau <= Tp - tp
            ==> gamma tau IN IMAGE Phi {x | p3_std_dist g0 x <= A}) /\
     (\tau. mfd_scalar (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau)) (gamma tau) +
            mfd_speed (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau))
                      gamma (&0) (Tp - tp) tau pow 2)
     real_integrable_on real_interval[&0,Tp - tp]
     ==> ell < p3_energy hs Tp gamma (Tp - tp)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  MP_TAC(SPECL [`c:real`; `ell:real`] P3N_THETA0_BOUNDS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[SYM(ASSUME `theta0 = &1 - exp(--(&2 * ell / c)) / &4`)] THEN STRIP_TAC THEN
  ABBREV_TAC `b = Tp - tp` THEN
  REWRITE_TAC[p3_energy] THEN
  ABBREV_TAC `E = \tau. mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (Tp - tau))
                                   (rfs_metric_at hs (Tp - tau)) ((gamma:real->A) tau) +
                        mfd_speed (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau))
                                  gamma (&0) b tau pow 2` THEN
  SUBGOAL_THEN `&0 < h pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `c / &2 * (log(&1 / &2) - log(&1 - theta0))` THEN CONJ_TAC THENL
   [REWRITE_TAC[ASSUME `theta0 = &1 - exp(--(&2 * ell / c)) / &4`] THEN
    MATCH_MP_TAC P3N_1613_TOP_ARITH THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `theta0:real`; `h:real`; `b:real`; `E:real->real`;
                `real_integral (real_interval[&0,b]) (E:real->real)`] P3N_ENERGY_TOP) THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    EXPAND_TAC "b" THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `b / h pow 2 = theta0 - (tp - ts) / h pow 2` SUBST1_TAC THENL
     [EXPAND_TAC "b" THEN
      UNDISCH_TAC `Tp = ts + theta0 * h pow 2` THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `&0 < h pow 2` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `t - (t - x) = x`] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:real`; `dl0:real`; `hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`;
                   `h:real`; `Tp:real`; `tp:real`; `b:real`; `gamma:real->A`;
                   `g0:real^3->real^3^3`; `A0:real`; `A:real`; `G:real->real^3->real^3^3`;
                   `J:real->bool`; `dcl:real`; `theta0:real`; `tau:real`] P3N_1613_SLICE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); ALL_TAC] THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    SUBGOAL_THEN `(Tp - tau - ts) / h pow 2 = theta0 - tau / h pow 2` SUBST1_TAC THENL
     [UNDISCH_TAC `Tp = ts + theta0 * h pow 2` THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `&0 < h pow 2` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    EXPAND_TAC "E" THEN BETA_TAC THEN
    MP_TAC(SPEC `mfd_speed (rfs_atlas_at (hs:(A)rfs_history) (Tp - tau))
                           (rfs_metric_at hs (Tp - tau)) (gamma:real->A) (&0) b tau`
                REAL_LE_POW_2) THEN
    REAL_ARITH_TAC]);;

(* the side case: the curve enters through the side d = A *)

let P3N_1613_SIDE = prove
 (`!c dl0 (hs:(A)rfs_history) Phi ts h Tp tp (gamma:real->A) g0 A0 A A1 th1
    (G:real->real^3->real^3^3) J dcl ell theta0.
     (!(G0:real^3->real^3^3) H V z dl.
        metric_field V G0 /\ metric_field V H /\ z IN V /\ c <= lscalar G0 z /\
        (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G0 z u v) /\
        &0 < dl /\ dl <= dl0 /\ lck_dist2 (rfs_kreg dl) G0 H z < dl pow 2
        ==> lscalar G0 z / &2 <= lscalar H z) /\
     &0 < c /\ p3_std_flow g0 (&1) G /\
     (!t x. &0 <= t /\ t < &1 ==> c / (&1 - t) <= lscalar (G t) x) /\
     (!t x u v. &0 <= t /\ t < &1 /\ ~collinear {vec 0,u,v}
                ==> &0 <= lsectional (G t) x u v) /\
     (!t x. &0 <= t /\ t <= th1 /\ A1 < p3_std_dist g0 x
            ==> lck_dist2 (rfs_kreg (&1 / &10))
                  (mpullback (p3_std_nc g0 A0) (cylinder_flow t)) (G t) x
                < (&1 / &10) pow 2) /\
     rfs_history_ok hs /\ p3_std_initial g0 A0 /\ &0 < h /\ &0 < ell /\
     theta0 < &1 /\ theta0 <= th1 /\ &2 * A1 < A /\ &5 / &2 * sqrt ell < A /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) {x | p3_std_dist g0 x < A + &1} (rfs_view hs) ts (inv(h pow 2)) Phi J dcl /\
     (!s. &0 <= s /\ ts + s * h pow 2 <= Tp ==> s IN J) /\
     &0 < dcl /\ dcl <= dl0 /\ dcl <= &1 / &10 /\
     Tp <= ts + theta0 * h pow 2 /\ ts <= tp /\ tp <= Tp /\
     (!s. ts <= s /\ s <= Tp
          ==> IMAGE Phi {x | p3_std_dist g0 x <= A} SUBSET topspace(rfs_top_at hs s)) /\
     rfs_st_curve hs Tp gamma (&0) (Tp - tp) /\
     (!tau. &0 <= tau /\ tau <= Tp - tp
            ==> gamma tau IN IMAGE Phi {x | p3_std_dist g0 x <= A}) /\
     gamma (&0) IN IMAGE Phi {x | p3_std_dist g0 x = A} /\
     gamma (Tp - tp) IN IMAGE Phi {x | p3_std_dist g0 x < A / &2} /\
     (\tau. mfd_scalar (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau)) (gamma tau) +
            mfd_speed (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau))
                      gamma (&0) (Tp - tp) tau pow 2)
     real_integrable_on real_interval[&0,Tp - tp]
     ==> ell < p3_energy hs Tp gamma (Tp - tp)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  ABBREV_TAC `b = Tp - tp` THEN
  REWRITE_TAC[p3_energy] THEN
  ABBREV_TAC `E = \tau. mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (Tp - tau))
                                   (rfs_metric_at hs (Tp - tau)) ((gamma:real->A) tau) +
                        mfd_speed (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau))
                                  gamma (&0) b tau pow 2` THEN
  SUBGOAL_THEN `&0 < h pow 2 /\ &0 < sqrt ell /\ &0 < A` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; SQRT_POS_LT] THEN
    MP_TAC(SPEC `ell:real` SQRT_POS_LT) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b /\ b <= h pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `theta0 * h pow 2` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x * h <= &1 * h ==> x * h <= h`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  (* the slice facts at every backward time *)
  SUBGOAL_THEN
   `!tau. &0 <= tau /\ tau <= b
          ==> Tp - tau < rfs_horizon (hs:(A)rfs_history) /\ &0 <= Tp - tau /\
              &0 <= (Tp - tau - ts) / h pow 2 /\ (Tp - tau - ts) / h pow 2 <= theta0 /\
              ts + (Tp - tau - ts) / h pow 2 * h pow 2 = Tp - tau /\
              (Tp - tau - ts) / h pow 2 IN J /\
              inv(h pow 2) * c / (&2 * (&1 - (Tp - tau - ts) / h pow 2)) <=
              mfd_scalar (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau))
                         ((gamma:real->A) tau)`
  (LABEL_TAC "slice") THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:real`; `dl0:real`; `hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`;
                   `h:real`; `Tp:real`; `tp:real`; `b:real`; `gamma:real->A`;
                   `g0:real^3->real^3^3`; `A0:real`; `A:real`; `G:real->real^3->real^3^3`;
                   `J:real->bool`; `dcl:real`; `theta0:real`; `tau:real`] P3N_1613_SLICE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); ALL_TAC] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  (* injectivity of Phi on the A+1 ball *)
  SUBGOAL_THEN `&0 IN (J:real->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `J:real->bool`)) (concl th) &&
      is_imp(snd(dest_forall(concl th))) &&
      not (is_conj(snd(dest_imp(snd(dest_forall(concl th)))))))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`; `inv(h pow 2)`;
                 `G:real->real^3->real^3^3`; `{x:real^3 | p3_std_dist g0 x < A + &1}`;
                 `J:real->bool`; `dcl:real`; `&0`] P3N_VIEW_CLOSE_INJ) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE REAL_ARITH_TAC);
    DISCH_THEN(LABEL_TAC "inj")] THEN
  (* the preimage curve beta *)
  SUBGOAL_THEN `?beta:real->real^3. !s. s IN real_interval[&0,b]
                  ==> p3_std_dist g0 (beta s) <= A /\
                      (gamma:real->A) s = (Phi:real^3->A) (beta s)`
  (X_CHOOSE_THEN `beta:real->real^3` (LABEL_TAC "beta")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MP (CONJ (ASSUME `&0 <= s`) (ASSUME `s <= b`)) o SPEC `s:real` o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "IMAGE" with Failure _ -> false))
            (concl th) &&
        not (can (find_term (fun t -> try fst(dest_const t) = "topspace" with Failure _ -> false))
                 (concl th)))) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the end values of the distance along beta *)
  SUBGOAL_THEN `&0 IN real_interval[&0,b] /\ b IN real_interval[&0,b]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 ((beta:real->real^3) (&0)) = A` ASSUME_TAC THENL
   [UNDISCH_TAC `(gamma:real->A) (&0) IN IMAGE (Phi:real^3->A) {x | p3_std_dist g0 x = A}` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "beta" (STRIP_ASSUME_TAC o C MP (ASSUME `&0 IN real_interval[&0,b]`) o
                     SPEC `&0`) THEN
    SUBGOAL_THEN `(beta:real->real^3) (&0) = y1` SUBST1_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(gamma:real->A) (&0)` THEN
        CONJ_TAC THENL [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC]];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 ((beta:real->real^3) b) < A / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `(gamma:real->A) b IN IMAGE (Phi:real^3->A) {x | p3_std_dist g0 x < A / &2}` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "beta" (STRIP_ASSUME_TAC o C MP (ASSUME `b IN real_interval[&0,b]`) o
                     SPEC `b:real`) THEN
    SUBGOAL_THEN `(beta:real->real^3) b = y2` SUBST1_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(gamma:real->A) b` THEN
        CONJ_TAC THENL [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC]];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [ASM_CASES_TAC `b = &0` THENL
     [UNDISCH_TAC `p3_std_dist g0 ((beta:real->real^3) b) < A / &2` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* continuity of beta and of the distance along it *)
  SUBGOAL_THEN
   `!s0. s0 IN real_interval[&0,b]
         ==> !e. &0 < e
                 ==> ?d. &0 < d /\
                         !s. s IN real_interval[&0,b] /\ abs(s - s0) < d
                             ==> dist((beta:real->real^3) s,beta s0) < e`
  (LABEL_TAC "bcont") THENL
   [X_GEN_TAC `s0:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= s0 /\ s0 <= b` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `s0 IN real_interval[&0,b]` THEN REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
    USE_THEN "slice" (MP_TAC o SPEC `s0:real`) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`; `h:real`; `Tp:real`;
                   `b:real`; `gamma:real->A`; `beta:real->real^3`; `g0:real^3->real^3^3`;
                   `A:real`; `G:real->real^3->real^3^3`; `J:real->bool`; `dcl:real`;
                   `(Tp - s0 - ts) / h pow 2`; `s0:real`] P3N_1613_BETA_CONT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `beta:real->real^3`; `b:real`; `A:real`]
                P3N_DIST_COMP_CONT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      USE_THEN "beta" (ACCEPT_TAC o CONJUNCT1 o C MP (ASSUME `s IN real_interval[&0,b]`) o
                       SPEC `s:real`);
      USE_THEN "bcont" ACCEPT_TAC];
    DISCH_TAC] THEN
  (* the energy inequality of the side case *)
  MP_TAC(ISPECL [`\s. p3_std_dist g0 ((beta:real->real^3) s)`;
                 `\tau. mfd_speed (rfs_atlas_at (hs:(A)rfs_history) (Tp - tau))
                                  (rfs_metric_at hs (Tp - tau)) (gamma:real->A) (&0) b tau pow 2`;
                 `E:real->real`; `{tau | ?j. Tp - tau = hs_time (hs:(A)rfs_history) j}`;
                 `real_integral (real_interval[&0,b]) (E:real->real)`; `b:real`; `A:real`;
                 `&5 / (&4 * h)`; `sqrt ell / h`] P3N_ENERGY_SIDE) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      SUBGOAL_THEN `{tau | ?j. Tp - tau = hs_time (hs:(A)rfs_history) j} =
                    IMAGE (\j. Tp - hs_time hs j) (:num)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN BETA_TAC THEN
        MESON_TAC[REAL_ARITH `!Tp x y. Tp - x = y <=> x = Tp - y`];
        MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[NUM_COUNTABLE]];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN EXPAND_TAC "E" THEN BETA_TAC THEN
      USE_THEN "slice" (MP_TAC o SPEC `tau:real`) THEN
      ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      SUBGOAL_THEN `&0 < inv(h pow 2) * c / (&2 * (&1 - (Tp - tau - ts) / h pow 2))` MP_TAC
      THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN FIRST_ASSUM ACCEPT_TAC;
          MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
           [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC]];
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL; IN_ELIM_THM] THEN STRIP_TAC THEN
      USE_THEN "slice" (MP_TAC o SPEC `tau:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      SUBGOAL_THEN
       `lck_dist2 (rfs_kreg (&1 / &10))
          (mpullback (p3_std_nc g0 A0) (cylinder_flow ((Tp - tau - ts) / h pow 2)))
          ((G:real->real^3->real^3^3) ((Tp - tau - ts) / h pow 2))
          ((beta:real->real^3) tau) < (&1 / &10) pow 2`
      ASSUME_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> try fst(dest_const t) = "cylinder_flow"
                                   with Failure _ -> false)) (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`; `h:real`; `Tp:real`;
                     `b:real`; `gamma:real->A`; `beta:real->real^3`; `g0:real^3->real^3^3`;
                     `A0:real`; `A:real`; `G:real->real^3->real^3^3`; `J:real->bool`;
                     `dcl:real`; `(Tp - tau - ts) / h pow 2`; `tau:real`] P3N_1613_DERIV) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f':real` THEN
      SUBGOAL_THEN `(&5 / (&4 * h)) pow 2 = &25 / &16 * inv(h pow 2)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC P3N_1613_SIDE_ARITH THEN
  MAP_EVERY EXISTS_TAC [`A:real`; `h:real`; `b:real`] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* MT Prop 16.13 with the energy integrand integrable and a free start time  *)
(* Tp, from the Prop 16.5 body with the closeness up to a free time tc,      *)
(* Prop 12.31 (scalar curvature lower bound of the standard flow), Prop 12.7 *)
(* (closeness to the cylinder away from the cap) and Thm 12.5 (nonnegative   *)
(* curvature).  Constants: c from 12.31, theta0 = 1 - exp(-2 ell/c)/4,       *)
(* th1 = (1 + theta0)/2, A1' from 12.7 at th1 and 1/10, A1 = 2 A1' + 3       *)
(* sqrt(ell) + 3; Prop 16.5 is used at A + 1, th1 and min dl0 (1/10) with tc *)
(* the horizon.                                                              *)
(* ========================================================================= *)

let P3N_PROP_16_13_FIX = prove
 (`!u:A->bool.
     (?eps165. &0 < eps165 /\
         !C eps hf md g0 A0 r A dcl theta.
           &1 < C /\ &0 < eps /\ eps <= eps165 /\
           p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0 /\
           &0 < r /\ &0 < A /\ &0 < dcl /\ &0 < theta /\ theta < &1
           ==> ?d0. &0 < d0 /\
                 !rp dl (hs:(A)rfs_history) k i Phi xi ts h tc.
                    p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ tc <= rfs_horizon hs /\
                    (!t x. &0 <= t /\ t < tc /\ x IN topspace(rfs_top_at hs t) /\
                           inv(r pow 2) <= rfs_vscalar (rfs_view hs) t x
                           ==> p3_canon_at (rfs_view hs) C eps x t) /\
                    1 <= k /\ k <= hs_count hs /\ i IN ev_index(hs_event hs k) /\
                    ts = hs_time hs k /\ ts < tc /\ h = p3_hscale hf rp dl ts /\
                    p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i Phi xi /\
                    dl ts <= d0 /\ rp ts <= eps
                    ==> ?G. p3_std_flow g0 (&1) G /\
                        (p3_view_close
                          (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                         {s | &0 <= s /\ s < &1} G)
                          (&0) (&1) {x | p3_std_dist g0 x < A}
                          (rfs_view hs) ts (inv(h pow 2)) Phi
                          {s | &0 <= s /\ s < theta /\ ts + s * h pow 2 <= tc /\
                               ts + s * h pow 2 < rfs_horizon hs} dcl \/
                        ?k'. k < k' /\ k' <= hs_count hs /\ hs_time hs k' <= tc /\
                             hs_time hs k' < ts + theta * h pow 2 /\
                             p3_view_close
                               (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                              {s | &0 <= s /\ s < &1} G)
                               (&0) (&1) {x | p3_std_dist g0 x < A}
                               (rfs_view hs) ts (inv(h pow 2)) Phi
                               {s | &0 <= s /\ ts + s * h pow 2 < hs_time hs k'} dcl /\
                             DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < A})
                                      (topspace(hs_top hs k')))) /\
     P2_PROP_12_31_STATEMENT /\ P2_PROP_12_7_STATEMENT /\ P2_THM_12_5_STATEMENT
     ==> ?eps1613. &0 < eps1613 /\
         !C eps hf md g0 A0 r ell.
           &1 < C /\ &0 < eps /\ eps <= eps1613 /\
           p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0 /\
           &0 < r /\ &0 < ell
           ==> ?A1 theta0. &0 < A1 /\ &0 < theta0 /\ theta0 < &1 /\
                 !A. A1 <= A
                   ==> ?d0. &0 < d0 /\
                         !rp dl (hs:(A)rfs_history) k i Phi xi ts h Tp tp gamma.
                            p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
                            (!t x. &0 <= t /\ t < rfs_horizon hs /\
                                   x IN topspace(rfs_top_at hs t) /\
                                   inv(r pow 2) <= rfs_vscalar (rfs_view hs) t x
                                   ==> p3_canon_at (rfs_view hs) C eps x t) /\
                            1 <= k /\ k <= hs_count hs /\ i IN ev_index(hs_event hs k) /\
                            ts = hs_time hs k /\ h = p3_hscale hf rp dl ts /\
                            p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i Phi xi /\
                            dl ts <= d0 /\ rp ts <= eps /\
                            Tp <= ts + theta0 * h pow 2 /\
                            (!s. ts <= s /\ s <= Tp
                                 ==> IMAGE Phi {x | p3_std_dist g0 x <= A} SUBSET
                                     topspace(rfs_top_at hs s)) /\
                            ts <= tp /\ tp <= ts + h pow 2 / &2 /\ tp <= Tp /\
                            rfs_st_curve hs Tp gamma (&0) (Tp - tp) /\
                            (!tau. &0 <= tau /\ tau <= Tp - tp
                                   ==> gamma tau IN IMAGE Phi {x | p3_std_dist g0 x <= A}) /\
                            (Tp = ts + theta0 * h pow 2 \/
                             gamma (&0) IN IMAGE Phi {x | p3_std_dist g0 x = A}) /\
                            gamma (Tp - tp) IN IMAGE Phi {x | p3_std_dist g0 x < A / &2} /\
                            (\tau. mfd_scalar (rfs_atlas_at hs (Tp - tau))
                                              (rfs_metric_at hs (Tp - tau)) (gamma tau) +
                                   mfd_speed (rfs_atlas_at hs (Tp - tau))
                                             (rfs_metric_at hs (Tp - tau))
                                             gamma (&0) (Tp - tp) tau pow 2)
                            real_integrable_on real_interval[&0,Tp - tp]
                            ==> ell < p3_energy hs Tp gamma (Tp - tp)`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps165:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p165")))
    (CONJUNCTS_THEN2 (LABEL_TAC "p1231")
      (CONJUNCTS_THEN2 (LABEL_TAC "p127") (LABEL_TAC "p125")))) THEN
  EXISTS_TAC `eps165:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                       `g0:real^3->real^3^3`; `A0:real`; `r:real`; `ell:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0 /\ &0 < sqrt ell` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT] THEN UNDISCH_TAC `p3_std_initial g0 A0` THEN
    SIMP_TAC[p3_std_initial];
    ALL_TAC] THEN
  (* the constants *)
  USE_THEN "p1231" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`] o
                    REWRITE_RULE[P2_PROP_12_31_STATEMENT]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c"))) THEN
  MP_TAC(SPEC `c:real` P3N_LEN_SCALAR) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  MP_TAC(SPECL [`c:real`; `ell:real`] P3N_THETA0_BOUNDS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  ABBREV_TAC `theta0 = &1 - exp(--(&2 * ell / c)) / &4` THEN
  ABBREV_TAC `th1 = (&1 + theta0) / &2` THEN
  SUBGOAL_THEN `&0 < th1 /\ th1 < &1 /\ theta0 < th1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "th1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "p127" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `th1:real`; `&1 / &10`] o
                   REWRITE_RULE[P2_PROP_12_7_STATEMENT]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1':real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nk"))) THEN
  MAP_EVERY EXISTS_TAC [`&2 * A1' + &3 * sqrt ell + &3`; `theta0:real`] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC;
                         ALL_TAC] THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  (* Prop 16.5 at A + 1 *)
  USE_THEN "p165" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                                   `g0:real^3->real^3^3`; `A0:real`; `r:real`; `A + &1`;
                                   `min dl0 (&1 / &10)`; `th1:real`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d0"))) THEN
  EXISTS_TAC `d0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`rp:real->real`; `dl:real->real`; `hs:(A)rfs_history`; `k:num`; `i:num`;
                       `Phi:real^3->A`; `xi:real^3->real^3`; `ts:real`; `h:real`; `Tp:real`;
                       `tp:real`; `gamma:real->A`] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  (* basic facts *)
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                 `hs:(A)rfs_history`; `k:num`] P3N_STRUCT_BASIC) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[SYM(ASSUME `ts = hs_time (hs:(A)rfs_history) k`);
              SYM(ASSUME `h = p3_hscale hf rp dl ts`)] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(Phi:real^3->A) (vec 0) IN topspace(rfs_top_at (hs:(A)rfs_history) ts)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `ts:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "topspace" with Failure _ -> false))
          (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "IMAGE" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ts < rfs_horizon (hs:(A)rfs_history)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P2A_TOPSPACE_LIVE) THEN SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "d0" (MP_TAC o SPECL [`rp:real->real`; `dl:real->real`; `hs:(A)rfs_history`; `k:num`;
                                 `i:num`; `Phi:real^3->A`; `xi:real^3->real^3`; `ts:real`;
                                 `h:real`; `rfs_horizon (hs:(A)rfs_history)`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real->real^3->real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `Phi:real^3->A`; `ts:real`; `h:real`; `Tp:real`;
                 `g0:real^3->real^3^3`; `A:real`; `{x:real^3 | p3_std_dist g0 x < A + &1}`;
                 `G:real->real^3->real^3^3`; `th1:real`; `theta0:real`; `min dl0 (&1 / &10)`]
                P3N_1613_CLOSE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^3` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real->bool` STRIP_ASSUME_TAC) THEN
  (* the curvature facts of the model flow G *)
  SUBGOAL_THEN `!t x. &0 <= t /\ t < &1
                      ==> c / (&1 - t) <= lscalar ((G:real->real^3->real^3^3) t) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM P2C_OPEN_SET_MFD_SCALAR] THEN
    USE_THEN "c" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`] P3N_STD_SEC_NONNEG) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `!t x. &0 <= t /\ t <= th1 /\ A1' < p3_std_dist g0 x
                      ==> lck_dist2 (rfs_kreg (&1 / &10))
                            (mpullback (p3_std_nc g0 A0) (cylinder_flow t))
                            ((G:real->real^3->real^3^3) t) x < (&1 / &10) pow 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "nk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the two cases *)
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term (fun t -> t = `theta0:real`)) (concl th))) THENL
   [MP_TAC(ISPECL [`c:real`; `dl0:real`; `hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`;
                   `h:real`; `Tp:real`; `tp:real`; `gamma:real->A`; `g0:real^3->real^3^3`;
                   `A0:real`; `A:real`; `G:real->real^3->real^3^3`; `J:real->bool`;
                   `min dl0 (&1 / &10)`; `ell:real`; `theta0:real`] P3N_1613_TOP) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); SIMP_TAC[]];
    MP_TAC(ISPECL [`c:real`; `dl0:real`; `hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`;
                   `h:real`; `Tp:real`; `tp:real`; `gamma:real->A`; `g0:real^3->real^3^3`;
                   `A0:real`; `A:real`; `A1':real`; `th1:real`; `G:real->real^3->real^3^3`;
                   `J:real->bool`; `min dl0 (&1 / &10)`; `ell:real`; `theta0:real`]
                  P3N_1613_SIDE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); SIMP_TAC[]]]);;

(* ========================================================================= *)
(* Prop 16.13 with 1/2 <= theta0: the same statement as P3N_PROP_16_13_FIX   *)
(* with &1 / &2 <= theta0 in the existential (here theta0 = 1 - exp(-2       *)
(* ell/c)/4 > 3/4).  The route theorem P3N_PROP_16_13_ROUTE is proved from   *)
(* this one.                                                                 *)
(* ========================================================================= *)

let P3N_PROP_16_13_FIX2 = prove
 (`!u:A->bool.
     (?eps165. &0 < eps165 /\
         !C eps hf md g0 A0 r A dcl theta.
           &1 < C /\ &0 < eps /\ eps <= eps165 /\
           p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0 /\
           &0 < r /\ &0 < A /\ &0 < dcl /\ &0 < theta /\ theta < &1
           ==> ?d0. &0 < d0 /\
                 !rp dl (hs:(A)rfs_history) k i Phi xi ts h tc.
                    p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ tc <= rfs_horizon hs /\
                    (!t x. &0 <= t /\ t < tc /\ x IN topspace(rfs_top_at hs t) /\
                           inv(r pow 2) <= rfs_vscalar (rfs_view hs) t x
                           ==> p3_canon_at (rfs_view hs) C eps x t) /\
                    1 <= k /\ k <= hs_count hs /\ i IN ev_index(hs_event hs k) /\
                    ts = hs_time hs k /\ ts < tc /\ h = p3_hscale hf rp dl ts /\
                    p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i Phi xi /\
                    dl ts <= d0 /\ rp ts <= eps
                    ==> ?G. p3_std_flow g0 (&1) G /\
                        (p3_view_close
                          (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                         {s | &0 <= s /\ s < &1} G)
                          (&0) (&1) {x | p3_std_dist g0 x < A}
                          (rfs_view hs) ts (inv(h pow 2)) Phi
                          {s | &0 <= s /\ s < theta /\ ts + s * h pow 2 <= tc /\
                               ts + s * h pow 2 < rfs_horizon hs} dcl \/
                        ?k'. k < k' /\ k' <= hs_count hs /\ hs_time hs k' <= tc /\
                             hs_time hs k' < ts + theta * h pow 2 /\
                             p3_view_close
                               (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                              {s | &0 <= s /\ s < &1} G)
                               (&0) (&1) {x | p3_std_dist g0 x < A}
                               (rfs_view hs) ts (inv(h pow 2)) Phi
                               {s | &0 <= s /\ ts + s * h pow 2 < hs_time hs k'} dcl /\
                             DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < A})
                                      (topspace(hs_top hs k')))) /\
     P2_PROP_12_31_STATEMENT /\ P2_PROP_12_7_STATEMENT /\ P2_THM_12_5_STATEMENT
     ==> ?eps1613. &0 < eps1613 /\
         !C eps hf md g0 A0 r ell.
           &1 < C /\ &0 < eps /\ eps <= eps1613 /\
           p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0 /\
           &0 < r /\ &0 < ell
           ==> ?A1 theta0. &0 < A1 /\ &0 < theta0 /\ &1 / &2 <= theta0 /\ theta0 < &1 /\
                 !A. A1 <= A
                   ==> ?d0. &0 < d0 /\
                         !rp dl (hs:(A)rfs_history) k i Phi xi ts h Tp tp gamma.
                            p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
                            (!t x. &0 <= t /\ t < rfs_horizon hs /\
                                   x IN topspace(rfs_top_at hs t) /\
                                   inv(r pow 2) <= rfs_vscalar (rfs_view hs) t x
                                   ==> p3_canon_at (rfs_view hs) C eps x t) /\
                            1 <= k /\ k <= hs_count hs /\ i IN ev_index(hs_event hs k) /\
                            ts = hs_time hs k /\ h = p3_hscale hf rp dl ts /\
                            p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i Phi xi /\
                            dl ts <= d0 /\ rp ts <= eps /\
                            Tp <= ts + theta0 * h pow 2 /\
                            (!s. ts <= s /\ s <= Tp
                                 ==> IMAGE Phi {x | p3_std_dist g0 x <= A} SUBSET
                                     topspace(rfs_top_at hs s)) /\
                            ts <= tp /\ tp <= ts + h pow 2 / &2 /\ tp <= Tp /\
                            rfs_st_curve hs Tp gamma (&0) (Tp - tp) /\
                            (!tau. &0 <= tau /\ tau <= Tp - tp
                                   ==> gamma tau IN IMAGE Phi {x | p3_std_dist g0 x <= A}) /\
                            (Tp = ts + theta0 * h pow 2 \/
                             gamma (&0) IN IMAGE Phi {x | p3_std_dist g0 x = A}) /\
                            gamma (Tp - tp) IN IMAGE Phi {x | p3_std_dist g0 x < A / &2} /\
                            (\tau. mfd_scalar (rfs_atlas_at hs (Tp - tau))
                                              (rfs_metric_at hs (Tp - tau)) (gamma tau) +
                                   mfd_speed (rfs_atlas_at hs (Tp - tau))
                                             (rfs_metric_at hs (Tp - tau))
                                             gamma (&0) (Tp - tp) tau pow 2)
                            real_integrable_on real_interval[&0,Tp - tp]
                            ==> ell < p3_energy hs Tp gamma (Tp - tp)`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps165:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p165")))
    (CONJUNCTS_THEN2 (LABEL_TAC "p1231")
      (CONJUNCTS_THEN2 (LABEL_TAC "p127") (LABEL_TAC "p125")))) THEN
  EXISTS_TAC `eps165:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                       `g0:real^3->real^3^3`; `A0:real`; `r:real`; `ell:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0 /\ &0 < sqrt ell` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT] THEN UNDISCH_TAC `p3_std_initial g0 A0` THEN
    SIMP_TAC[p3_std_initial];
    ALL_TAC] THEN
  (* the constants *)
  USE_THEN "p1231" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`] o
                    REWRITE_RULE[P2_PROP_12_31_STATEMENT]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c"))) THEN
  MP_TAC(SPEC `c:real` P3N_LEN_SCALAR) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  MP_TAC(SPECL [`c:real`; `ell:real`] P3N_THETA0_BOUNDS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  ABBREV_TAC `theta0 = &1 - exp(--(&2 * ell / c)) / &4` THEN
  ABBREV_TAC `th1 = (&1 + theta0) / &2` THEN
  SUBGOAL_THEN `&0 < th1 /\ th1 < &1 /\ theta0 < th1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "th1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "p127" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `th1:real`; `&1 / &10`] o
                   REWRITE_RULE[P2_PROP_12_7_STATEMENT]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1':real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nk"))) THEN
  MAP_EVERY EXISTS_TAC [`&2 * A1' + &3 * sqrt ell + &3`; `theta0:real`] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
                         FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  (* Prop 16.5 at A + 1 *)
  USE_THEN "p165" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                                   `g0:real^3->real^3^3`; `A0:real`; `r:real`; `A + &1`;
                                   `min dl0 (&1 / &10)`; `th1:real`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d0"))) THEN
  EXISTS_TAC `d0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`rp:real->real`; `dl:real->real`; `hs:(A)rfs_history`; `k:num`; `i:num`;
                       `Phi:real^3->A`; `xi:real^3->real^3`; `ts:real`; `h:real`; `Tp:real`;
                       `tp:real`; `gamma:real->A`] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  (* basic facts *)
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`; `dl:real->real`;
                 `hs:(A)rfs_history`; `k:num`] P3N_STRUCT_BASIC) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[SYM(ASSUME `ts = hs_time (hs:(A)rfs_history) k`);
              SYM(ASSUME `h = p3_hscale hf rp dl ts`)] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(Phi:real^3->A) (vec 0) IN topspace(rfs_top_at (hs:(A)rfs_history) ts)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `ts:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "topspace" with Failure _ -> false))
          (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "IMAGE" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ts < rfs_horizon (hs:(A)rfs_history)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P2A_TOPSPACE_LIVE) THEN SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "d0" (MP_TAC o SPECL [`rp:real->real`; `dl:real->real`; `hs:(A)rfs_history`; `k:num`;
                                 `i:num`; `Phi:real^3->A`; `xi:real^3->real^3`; `ts:real`;
                                 `h:real`; `rfs_horizon (hs:(A)rfs_history)`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real->real^3->real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `Phi:real^3->A`; `ts:real`; `h:real`; `Tp:real`;
                 `g0:real^3->real^3^3`; `A:real`; `{x:real^3 | p3_std_dist g0 x < A + &1}`;
                 `G:real->real^3->real^3^3`; `th1:real`; `theta0:real`; `min dl0 (&1 / &10)`]
                P3N_1613_CLOSE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^3` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real->bool` STRIP_ASSUME_TAC) THEN
  (* the curvature facts of the model flow G *)
  SUBGOAL_THEN `!t x. &0 <= t /\ t < &1
                      ==> c / (&1 - t) <= lscalar ((G:real->real^3->real^3^3) t) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM P2C_OPEN_SET_MFD_SCALAR] THEN
    USE_THEN "c" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`] P3N_STD_SEC_NONNEG) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `!t x. &0 <= t /\ t <= th1 /\ A1' < p3_std_dist g0 x
                      ==> lck_dist2 (rfs_kreg (&1 / &10))
                            (mpullback (p3_std_nc g0 A0) (cylinder_flow t))
                            ((G:real->real^3->real^3^3) t) x < (&1 / &10) pow 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "nk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the two cases *)
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term (fun t -> t = `theta0:real`)) (concl th))) THENL
   [MP_TAC(ISPECL [`c:real`; `dl0:real`; `hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`;
                   `h:real`; `Tp:real`; `tp:real`; `gamma:real->A`; `g0:real^3->real^3^3`;
                   `A0:real`; `A:real`; `G:real->real^3->real^3^3`; `J:real->bool`;
                   `min dl0 (&1 / &10)`; `ell:real`; `theta0:real`] P3N_1613_TOP) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); SIMP_TAC[]];
    MP_TAC(ISPECL [`c:real`; `dl0:real`; `hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`;
                   `h:real`; `Tp:real`; `tp:real`; `gamma:real->A`; `g0:real^3->real^3^3`;
                   `A0:real`; `A:real`; `A1':real`; `th1:real`; `G:real->real^3->real^3^3`;
                   `J:real->bool`; `min dl0 (&1 / &10)`; `ell:real`; `theta0:real`]
                  P3N_1613_SIDE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); SIMP_TAC[]]]);;

(* ========================================================================= *)
(* The route theorem for Prop 16.13 from P3N_PROP_16_13_FIX2 (the statement  *)
(* with 1/2 <= theta0).                                                      *)
(* ========================================================================= *)

let P3N_PROP_16_13_ROUTE = prove
 (`!u:A->bool. P3_PROP_16_13_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_PROP_16_13_ROUTE_STATEMENT] THEN
  MP_TAC(ISPEC `u:A->bool` P3N_PROP_16_13_FIX2) THEN
  REWRITE_TAC[GSYM P3_PROP_16_5_STATEMENT; GSYM P3_PROP_16_13_STATEMENT]);;


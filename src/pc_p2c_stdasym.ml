(* ========================================================================= *)
(* Unit pc_p2c_stdasym (Part 2C): MT Ch 12, Prop 12.7 and Cor 12.8 for every *)
(* partial standard flow.  Far out, the flow is close to the shrinking       *)
(* cylinder: the pointed flows at points tending to infinity have a limit    *)
(* (Prop 5.14 on the punctured space with the cylinder metric, exact at time *)
(* 0 through the neck coordinates of g0), which is the cylinder flow by the  *)
(* uniqueness of complete bounded-curvature flows (P2C_REQ_UNIQ_COMPLETE).   *)
(* Since the cylinder flow degenerates at time 1, every partial standard     *)
(* flow has te <= 1.                                                         *)
(* ========================================================================= *)

needs "src/pc_p2c_stdflow.ml";;
needs "src/pc_p2c_stdgeom.ml";;
needs "src/pc_mfd_transport.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The cylinder flow is invariant under the dilations and the                *)
(* orthogonal maps of the punctured space.                                   *)
(* ------------------------------------------------------------------------- *)

let STDS_ORTH_DOT = prove
 (`!(Q:real^3^3) a b. orthogonal_matrix Q ==> (Q ** a) dot (Q ** b) = a dot b`,
  REWRITE_TAC[ORTHOGONAL_MATRIX_TRANSFORMATION; orthogonal_transformation] THEN
  SIMP_TAC[]);;

let STDS_LINEAR_CQ = prove
 (`!c (Q:real^3^3). linear (\z:real^3. c % (Q ** z))`,
  REWRITE_TAC[linear; MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
  REPEAT GEN_TAC THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let STDS_FRECHET_CQ = prove
 (`!c (Q:real^3^3) y.
     frechet_derivative (\z:real^3. c % (Q ** z)) (at y) = (\z. c % (Q ** z))`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[STDS_LINEAR_CQ]);;

let STDS_CYL_CQ_PULLBACK = prove
 (`!t c (Q:real^3^3) (y:real^3).
     &0 < c /\ orthogonal_matrix Q /\ ~(y = vec 0)
     ==> mpullback (\z. c % (Q ** z)) (cylinder_flow t) y = cylinder_flow t y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFB_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  SIMP_TAC[LRG_MPULLBACK_DOT; STDS_FRECHET_CQ; STDS_LINEAR_CQ] THEN
  REWRITE_TAC[cylinder_flow; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              MATRIX_VECTOR_MUL_LID; RFB_OUTER_MUL] THEN
  REWRITE_TAC[DOT_RMUL; DOT_LMUL; DOT_RADD; DOT_LADD; NORM_POW_2;
              MATRIX_VECTOR_MUL_RMUL] THEN
  ASM_SIMP_TAC[STDS_ORTH_DOT] THEN
  SUBGOAL_THEN `~((y:real^3) dot y = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < c` THEN REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The sectional curvatures of the cylinder flow lie in                     *)
(* [0, 1 / (2 (1 - t))] (the time-0 formula LSECTIONAL_CYLINDER and the     *)
(* representation cyl(t) = (1 - t) h_e^* cyl(0) of RFB_CYL_SETUP).           *)
(* ------------------------------------------------------------------------- *)

let STDS_OPEN_SET_MFD_SECTIONAL = prove
 (`!U (g:real^N->real^N^N) x u v.
     open U /\ x IN U ==> mfd_sectional (open_set_atlas U) g x u v = lsectional g x u v`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[mfd_sectional; RFB_OPEN_SET_CHART_AT] THEN
  REWRITE_TAC[SND] THEN MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL]);;

let STDS_LSECTIONAL_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G y u v.
     metric_field U G /\ diffeomorphism_on U' U h h' /\ y IN U'
     ==> lsectional (mpullback h G) y u v =
         lsectional G (h y) (frechet_derivative h (at y) u)
                            (frechet_derivative h (at y) v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`; `h':real^N->real^N`;
                 `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[lsectional] THEN ASM_SIMP_TAC[LRG_MPULLBACK_DOT] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`; `h':real^N->real^N`;
                 `G:real^N->real^N^N`; `y:real^N`; `u:real^N`; `v:real^N`; `v:real^N`]
         LRIEMANN_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let STDS_GRAM3 = prove
 (`!u v y:real^3.
     (y dot y) * ((u dot u) * (v dot v) - (u dot v) pow 2) -
     ((v dot y) pow 2 * (u dot u) + (u dot y) pow 2 * (v dot v) -
      &2 * (u dot y) * (v dot y) * (u dot v)) =
     (u$1 * (v$2 * y$3 - v$3 * y$2) - u$2 * (v$1 * y$3 - v$3 * y$1) +
      u$3 * (v$1 * y$2 - v$2 * y$1)) pow 2`,
  REWRITE_TAC[DOT_3] THEN CONV_TAC REAL_RING);;

let STDS_CYL0_SEC_BOUND = prove
 (`!y u v:real^3.
     ~(y = vec 0) /\ ~collinear {vec 0,u,v}
     ==> &0 <= lsectional (cylinder_flow (&0)) y u v /\
         lsectional (cylinder_flow (&0)) y u v <= inv(&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[LSECTIONAL_CYLINDER] THEN
  SUBGOAL_THEN `&0 < (u dot u) * (v dot v) - ((u:real^3) dot v) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2C_GRAM_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (v dot y) pow 2 * (u dot u) + (u dot y) pow 2 * (v dot v) -
                      &2 * (u dot y) * (v dot y) * ((u:real^3) dot v)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(v dot y) % u - (u dot y) % (v:real^3)` DOT_POS_LE) THEN
    REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(v dot y) pow 2 * (u dot u) + (u dot y) pow 2 * (v dot v) -
                &2 * (u dot y) * (v dot y) * ((u:real^3) dot v) <=
                (y dot y) * ((u dot u) * (v dot v) - (u dot v) pow 2)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`u:real^3`; `v:real^3`; `y:real^3`] STDS_GRAM3) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= s ==> (a - b = s) ==> b <= a`) THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_POW_2] THEN
  ABBREV_TAC `n = (y:real^3) dot y` THEN
  ABBREV_TAC `D = (u dot u) * (v dot v) - ((u:real^3) dot v) pow 2` THEN
  ABBREV_TAC `E = (v dot y) pow 2 * (u dot u) + (u dot y) pow 2 * (v dot v) -
                  &2 * (u dot y) * (v dot y) * ((u:real^3) dot v)` THEN
  SUBGOAL_THEN
   `((u dot u - (u dot y) pow 2 / n) * (v dot v - (v dot y) pow 2 / n) -
     ((u:real^3) dot v - (u dot y) * (v dot y) / n) pow 2) = D - E / n`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "E"] THEN UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `E / n <= D` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E / n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * D` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
  ASM_REAL_ARITH_TAC);;

let STDS_CYL_SEC_BOUND = prove
 (`!t (y:real^3) u v.
     t < &1 /\ ~(y = vec 0) /\ ~collinear {vec 0,u,v}
     ==> &0 <= lsectional (cylinder_flow t) y u v /\
         lsectional (cylinder_flow t) y u v <= inv(&2 * (&1 - t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `t:real` RFB_CYL_SETUP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `h = \y:real^3. ((norm y pow 2) rpow e) % y` THEN
  ABBREV_TAC `h' = \y:real^3. ((norm y pow 2) rpow (--e / (&2 * e + &1))) % y` THEN
  SUBGOAL_THEN `lsectional (cylinder_flow t) (y:real^3) u v =
                lsectional (\z. (&1 - t) %% mpullback h (cylinder_flow (&0)) z) y u v`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_REWRITE_TAC[LRG_CYL_OPEN; IN_DELETE; IN_UNIV; LRG_CYL0_EQ] THEN
    ASM_SIMP_TAC[IN_DELETE; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `mpullback h (cylinder_flow (&0))`; `&1 - t`;
                 `y:real^3`; `u:real^3`; `v:real^3`] APX_LSECTIONAL_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE; IN_UNIV; LRG_CYL0_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `(:real^3) DELETE vec 0`; `h:real^3->real^3`;
                 `h':real^3->real^3`; `cylinder_flow (&0)`; `y:real^3`; `u:real^3`;
                 `v:real^3`] STDS_LSECTIONAL_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`; IN_DELETE; IN_UNIV];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `(:real^3) DELETE vec 0`; `h:real^3->real^3`;
                 `h':real^3->real^3`; `y:real^3`] LRG_DIFFEO_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE; IN_UNIV];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`(h:real^3->real^3) y`; `frechet_derivative (h:real^3->real^3) (at y) u`;
                 `frechet_derivative (h:real^3->real^3) (at y) v`] STDS_CYL0_SEC_BOUND) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(h:real^3->real^3) y IN (:real^3) DELETE vec 0` THEN SET_TAC[];
      UNDISCH_TAC `~collinear {vec 0:real^3,u,v}` THEN
      MATCH_MP_TAC(TAUT `(p <=> q) ==> ~p ==> ~q`) THEN
      MP_TAC(ISPECL [`frechet_derivative (h:real^3->real^3) (at y)`;
                     `{vec 0:real^3,u,v}`] COLLINEAR_LINEAR_IMAGE_EQ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN
        DISCH_THEN(MP_TAC o AP_TERM
          `frechet_derivative (h':real^3->real^3) (at ((h:real^3->real^3) y))`) THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
        MP_TAC(MATCH_MP LINEAR_0
          (ASSUME `linear (frechet_derivative (h:real^3->real^3) (at y))`)) THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `inv(&2 * (&1 - t)) * (&1 - t) = inv(&2)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &1 - t` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The cylinder flow on the punctured space: a Ricci flow from               *)
(* time 0, riemannian slices, the comparison (1 - t) cyl(0) <= cyl(t) <=     *)
(* cyl(0) and the curvature bound |Rm| <= 1 / (2 (1 - t)).                    *)
(* ------------------------------------------------------------------------- *)

let STDS_CYL_RFF = prove
 (`!b. &0 < b /\ b <= &1
       ==> ricci_flow_from (subtopology euclidean ((:real^3) DELETE vec 0),
                            open_set_atlas ((:real^3) DELETE vec 0)) (&0) b cylinder_flow`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CF_RFO_FROM THEN
  MAP_EVERY EXISTS_TAC [`--(&1)`; `&1`] THEN
  ASM_SIMP_TAC[SHRINKING_CYLINDER_FLOW; REAL_ARITH `--(&1) < &1`] THEN
  ASM_REAL_ARITH_TAC);;

let STDS_CYL_RIEM = prove
 (`!t. t < &1 ==> riemannian_metric (open_set_atlas ((:real^3) DELETE vec 0))
                                     (cylinder_flow t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN
  ASM_SIMP_TAC[LRG_CYL_OPEN; RFB_CYL_METRIC_FIELD]);;

let STDS_QF_ARITH = prove
 (`!k t p w. &0 <= k /\ &0 <= t /\ &0 <= p /\ p <= w
             ==> (&1 - t) * k * w <= k * ((&1 - t) * w + t * p) /\
                 k * ((&1 - t) * w + t * p) <= k * w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= k * t * p /\ &0 <= k * t * (w - p)` MP_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let STDS_CS2 = prove
 (`!x y:real^N. (x dot y) pow 2 <= (x dot x) * (y dot y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  REWRITE_TAC[REAL_ABS_POS; REAL_ABS_MUL; REAL_ABS_NORM; NORM_CAUCHY_SCHWARZ_ABS]);;

let STDS_CYL_QF = prove
 (`!t (y:real^3) v.
     &0 <= t /\ t < &1 /\ ~(y = vec 0)
     ==> (&1 - t) * (v dot (cylinder_flow (&0) y ** v)) <= v dot (cylinder_flow t y ** v) /\
         v dot (cylinder_flow t y ** v) <= v dot (cylinder_flow (&0) y ** v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[cylinder_flow; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              MATRIX_VECTOR_MUL_LID; RFB_OUTER_MUL; DOT_RMUL; DOT_RADD] THEN
  REWRITE_TAC[REAL_SUB_RZERO; real_div; REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_LID] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `((y:real^3) dot v) * ((v:real^3) dot y) <= norm y pow 2 * (v dot v)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`y:real^3`; `v:real^3`] STDS_CS2) THEN
    REWRITE_TAC[NORM_POW_2] THEN REWRITE_TAC[REAL_POW_2] THEN REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((y:real^3) dot v) * ((v:real^3) dot y)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_SYM; REAL_LE_SQUARE]; ALL_TAC] THEN
  MP_TAC(SPECL [`&2 * inv(norm(y:real^3) pow 2)`; `t:real`;
                `inv(norm(y:real^3) pow 2) * ((y dot v) * ((v:real^3) dot y))`;
                `(v:real^3) dot v`] STDS_QF_ARITH) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_ARITH `inv n * q = q / n`] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `((y:real^3) dot v) * ((v:real^3) dot y) <= norm y pow 2 * (v dot v)` THEN
    REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let STDS_CYL_RM_NORM = prove
 (`!t (y:real^3).
     t < &1 /\ ~(y = vec 0)
     ==> mfd_rm_norm (open_set_atlas ((:real^3) DELETE vec 0)) (cylinder_flow t) y <=
         inv(&2 * (&1 - t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  DISCH_TAC THEN
  ASM_SIMP_TAC[STDS_OPEN_SET_MFD_SECTIONAL; LRG_CYL_OPEN; IN_DELETE; IN_UNIV] THEN
  MP_TAC(ISPECL [`t:real`; `y:real^3`; `u:real^3`; `v:real^3`] STDS_CYL_SEC_BOUND) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The cylinder slices are complete on the punctured space                   *)
(* (lengths bound the change of sqrt 2 log |y|, APX_SVAL_LENGTH_LOWER).      *)
(* ------------------------------------------------------------------------- *)

let STDS_CYL0_DIST_LOWER = prove
 (`!x y:real^3.
     mfd_joinable (subtopology euclidean ((:real^3) DELETE vec 0),
                   open_set_atlas ((:real^3) DELETE vec 0)) x y
     ==> abs(apx_sval y - apx_sval x) <=
         mfd_dist (subtopology euclidean ((:real^3) DELETE vec 0),
                   open_set_atlas ((:real^3) DELETE vec 0)) (cylinder_flow (&0)) x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_joinable] THEN
  DISCH_THEN(X_CHOOSE_TAC `c0:real->real^3`) THEN
  REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `l:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `c:real->real^3`; `&0`; `&1`]
           APX_SVAL_LENGTH_LOWER) THEN
    ASM_REWRITE_TAC[LRG_CYL_OPEN; IN_DELETE; IN_UNIV] THEN SIMP_TAC[]]);;

let STDS_CYL0_COMPLETE = prove
 (`mfd_complete (subtopology euclidean ((:real^3) DELETE vec 0),
                 open_set_atlas ((:real^3) DELETE vec 0)) (cylinder_flow (&0))`,
  REWRITE_TAC[mfd_complete; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_DELETE; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `r:real`] THEN DISCH_TAC THEN
  ABBREV_TAC `q = r / sqrt(&2)` THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `cball(vec 0:real^3,exp q * norm(x:real^3)) DIFF
              ball(vec 0,exp(--q) * norm x)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_BALL_0; IN_DELETE; IN_UNIV] THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(norm(vec 0:real^3) < exp(--q) * norm(x:real^3))` THEN
      ASM_SIMP_TAC[NORM_0; REAL_LT_MUL; REAL_EXP_POS_LT]];
    REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM; IN_DIFF; IN_BALL_0; IN_CBALL_0] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [UNDISCH_TAC `mfd_joinable (subtopology euclidean ((:real^3) DELETE vec 0),
                                 open_set_atlas ((:real^3) DELETE vec 0)) x y` THEN
      REWRITE_TAC[mfd_joinable] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`subtopology euclidean ((:real^3) DELETE vec 0)`;
                     `open_set_atlas ((:real^3) DELETE vec 0)`; `c:real->real^3`;
                     `&0`; `&1`; `&1`] MFD_C1_CURVE_IN_TOPSPACE) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_DELETE] THEN
      REWRITE_TAC[REAL_POS; REAL_LE_REFL; IN_UNIV] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    MP_TAC(SPECL [`x:real^3`; `y:real^3`] STDS_CYL0_DIST_LOWER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs(log(norm(y:real^3)) - log(norm(x:real^3))) <= q` MP_TAC THENL
     [EXPAND_TAC "q" THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; P3S_SQRT2_POS] THEN
      UNDISCH_TAC `abs(apx_sval y - apx_sval x) <=
                   mfd_dist (subtopology euclidean ((:real^3) DELETE vec 0),
                             open_set_atlas ((:real^3) DELETE vec 0))
                            (cylinder_flow (&0)) x y` THEN
      UNDISCH_TAC `mfd_dist (subtopology euclidean ((:real^3) DELETE vec 0),
                             open_set_atlas ((:real^3) DELETE vec 0))
                            (cylinder_flow (&0)) x y <= r` THEN
      REWRITE_TAC[apx_sval; GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
      SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; P3S_SQRT2_POS] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_NOT_LT] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`norm(y:real^3)`; `exp q * norm(x:real^3)`] LOG_MONO_LE) THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT; LOG_MUL; LOG_EXP] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`exp(--q) * norm(x:real^3)`; `norm(y:real^3)`] LOG_MONO_LE) THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT; LOG_MUL; LOG_EXP] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC MFD_CBALL_CLOSED THEN
    SIMP_TAC[OPEN_SET_ATLAS; LRG_CYL_OPEN; STDS_CYL_RIEM; REAL_ARITH `&0 < &1`]]);;

let STDS_CYL_COMPLETE = prove
 (`!t. &0 <= t /\ t < &1
       ==> mfd_complete (subtopology euclidean ((:real^3) DELETE vec 0),
                         open_set_atlas ((:real^3) DELETE vec 0)) (cylinder_flow t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CO_COMPLETE_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`cylinder_flow (&0)`; `inv(&1 - t)`] THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; LRG_CYL_OPEN; STDS_CYL_RIEM; REAL_ARITH `&0 < &1`;
               STDS_CYL0_COMPLETE; REAL_LT_INV_EQ; REAL_SUB_LT] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_DELETE; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`z:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:real`; `z:real^3`; `v:real^3`] STDS_CYL_QF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `&0 < &1 - t` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`&1 - t`,`a:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ]);;

(* ------------------------------------------------------------------------- *)
(* An exhaustion function of the punctured space for the                     *)
(* cylinder metric, phi = sqrt(1 + theta^2) with theta = - sqrt 2 log |y|:   *)
(* smooth, bounded gradient and Laplacian (chain rule and P2CN_THETA_BOUND). *)
(* ------------------------------------------------------------------------- *)

let stds_cphi = new_definition
 `stds_cphi (y:real^3) = sqrt(&1 + p2cn_theta (&0) y pow 2)`;;

let STDS_CPHI_ALT = prove
 (`stds_cphi = \y. sqrt(&1 + p2cn_theta (&0) y pow 2)`,
  REWRITE_TAC[FUN_EQ_THM; stds_cphi]);;

let STDS_SQ1_POS = prove
 (`!u. &0 < &1 + u pow 2`,
  GEN_TAC THEN MP_TAC(SPEC `u:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let STDS_H_DERIVS = prove
 (`!u. ((\u. sqrt(&1 + u pow 2)) has_real_derivative (u / sqrt(&1 + u pow 2))) (atreal u) /\
       ((\u. u / sqrt(&1 + u pow 2)) has_real_derivative (inv(sqrt(&1 + u pow 2)) pow 3))
       (atreal u)`,
  GEN_TAC THEN MP_TAC(SPEC `u:real` STDS_SQ1_POS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&1 + u pow 2) /\ sqrt(&1 + u pow 2) pow 2 = &1 + u pow 2`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  CONJ_TAC THEN REAL_DIFF_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
  ABBREV_TAC `s = sqrt(&1 + u pow 2)` THEN
  UNDISCH_TAC `s pow 2 = &1 + u pow 2` THEN UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD);;

let STDS_H_BOUNDS = prove
 (`!u. abs(u / sqrt(&1 + u pow 2)) <= &1 /\
       abs(inv(sqrt(&1 + u pow 2)) pow 3) <= &1 /\
       abs u <= sqrt(&1 + u pow 2)`,
  GEN_TAC THEN MP_TAC(SPEC `u:real` STDS_SQ1_POS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs u <= sqrt(&1 + u pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW2_ABS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= sqrt(&1 + u pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN MP_TAC(SPEC `u:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&1 + u pow 2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_LE_LDIV_EQ;
                 REAL_MUL_LID];
    REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_1_LE THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_ABS_INV] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
    ASM_REAL_ARITH_TAC]);;

let STDS_ABS_COMB = prove
 (`!a b c d K. abs a <= &1 /\ abs b <= &1 /\ abs c <= K /\ abs d <= K
               ==> abs(a * c + b * d) <= &2 * K /\ a pow 2 * d <= K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs a * abs c <= &1 * K` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `abs b * abs d <= &1 * K` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `abs a pow 2 <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `abs a pow 2 * abs d <= &1 * K` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `a pow 2 * d <= abs a pow 2 * abs d` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_POW; GSYM REAL_ABS_MUL; REAL_ABS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(a * c + b * d) <= abs a * abs c + abs b * abs d` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_ABS_TRIANGLE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let STDS_CPHI_SMOOTH = prove
 (`smooth_map_on ((:real^3) DELETE vec 0) (\z. lift(stds_cphi z))`,
  REWRITE_TAC[stds_cphi] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `\z:real^3. lift(&1 + p2cn_theta (&0) z pow 2)`]
                SMOOTH_MAP_ON_LIFT_SQRT) THEN
  REWRITE_TAC[LIFT_DROP; LRG_CYL_OPEN; STDS_SQ1_POS] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[LIFT_ADD; REAL_POW_2] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  REWRITE_TAC[LRG_CYL_OPEN; SMOOTH_MAP_ON_CONST] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `\z:real^3. lift(p2cn_theta (&0) z)`;
                 `\z:real^3. lift(p2cn_theta (&0) z)`] SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
  REWRITE_TAC[LIFT_DROP; LRG_CYL_OPEN; P2CN_THETA_SMOOTH]);;

let STDS_CPHI_GRAD_LAP = prove
 (`?K. !y:real^3. ~(y = vec 0)
         ==> lgrad2 (cylinder_flow (&0)) stds_cphi y <= K /\
             abs(llap (cylinder_flow (&0)) stds_cphi y) <= K`,
  X_CHOOSE_TAC `K0:real` (SPEC `&0` P2CN_THETA_BOUND) THEN
  EXISTS_TAC `&2 * K0` THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `u = p2cn_theta (&0) (y:real^3)` THEN
  MP_TAC(SPEC `u:real` STDS_H_BOUNDS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= K0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(lgrad2 (cylinder_flow (&0)) (p2cn_theta (&0)) y)` THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow (&0)`;
                           `p2cn_theta (&0)`; `\u. sqrt(&1 + u pow 2)`;
                           `u / sqrt(&1 + u pow 2)`; `y:real^3`] RFA_LGRAD2_COMPOSE)) THEN
  ASM_REWRITE_TAC[LRG_CYL_OPEN; P2CN_THETA_SMOOTH; IN_DELETE; IN_UNIV; STDS_H_DERIVS] THEN
  REWRITE_TAC[GSYM STDS_CPHI_ALT] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`(:real^3) DELETE vec 0`; `(:real)`; `cylinder_flow (&0)`;
                           `p2cn_theta (&0)`; `\u. sqrt(&1 + u pow 2)`;
                           `\u. u / sqrt(&1 + u pow 2)`; `\u. inv(sqrt(&1 + u pow 2)) pow 3`;
                           `y:real^3`] RFA_LLAP_COMPOSE)) THEN
  ASM_REWRITE_TAC[LRG_CYL_OPEN; P2CN_THETA_SMOOTH; IN_DELETE; IN_UNIV; STDS_H_DERIVS] THEN
  REWRITE_TAC[GSYM STDS_CPHI_ALT] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`u / sqrt(&1 + u pow 2)`; `inv(sqrt(&1 + u pow 2)) pow 3`;
                `llap (cylinder_flow (&0)) (p2cn_theta (&0)) y`;
                `lgrad2 (cylinder_flow (&0)) (p2cn_theta (&0)) y`; `K0:real`] STDS_ABS_COMB) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The sublevel sets of the exhaustion are compact annuli, its              *)
(* volume growth is exponential, and the conversions of the open-set atlas  *)
(* of the punctured space to the local calculus.                            *)
(* ------------------------------------------------------------------------- *)

let STDS_P_CONV = prove
 (`!(g:real^3->real^3^3) f l x.
     ~(x = vec 0)
     ==> p2c_fgrad2 (open_set_atlas ((:real^3) DELETE vec 0)) g f x = lgrad2 g f x /\
         p2c_flap (open_set_atlas ((:real^3) DELETE vec 0)) g f x = llap g f x /\
         lrm_deriv_norm2 l (metric_local (open_set_atlas ((:real^3) DELETE vec 0))
                              (chart_at (open_set_atlas ((:real^3) DELETE vec 0)) x) g)
                           (SND(chart_at (open_set_atlas ((:real^3) DELETE vec 0)) x) x) =
         lrm_deriv_norm2 l g x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE; IN_UNIV]; ALL_TAC] THEN
  ASM_SIMP_TAC[p2c_fgrad2; p2c_flap; RFB_OPEN_SET_CHART_AT] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LGRAD2_LOCAL; MATCH_MP_TAC LLAP_LOCAL; MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL] THEN
  EXISTS_TAC `(:real^3) DELETE vec 0` THEN
  ASM_SIMP_TAC[LRG_CYL_OPEN; RFB_OPEN_SET_METRIC_LOCAL; o_THM; MFDM_CHART_INV_ID]);;

let STDS_CPHI_GE = prove
 (`!y:real^3. &1 <= stds_cphi y /\ abs(p2cn_theta (&0) y) <= stds_cphi y`,
  GEN_TAC THEN REWRITE_TAC[stds_cphi] THEN
  MP_TAC(SPEC `p2cn_theta (&0) (y:real^3)` STDS_H_BOUNDS) THEN SIMP_TAC[] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
  MP_TAC(SPEC `p2cn_theta (&0) (y:real^3)` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let STDS_CPHI_ANNULUS = prove
 (`!c y:real^3. ~(y = vec 0) /\ stds_cphi y <= c
                ==> exp(--(abs c)) <= norm y /\ norm y <= exp(abs c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(log(norm(y:real^3))) <= abs c` ASSUME_TAC THENL
   [MP_TAC(SPEC `y:real^3` STDS_CPHI_GE) THEN
    REWRITE_TAC[p2cn_theta; REAL_SUB_LZERO; REAL_ABS_NEG; REAL_ABS_MUL] THEN
    SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; P3S_SQRT2_POS] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&1 <= sqrt(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `abs(log(norm(y:real^3))) <= sqrt(&2) * abs(log(norm y))` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`exp(--(abs c))`; `norm(y:real^3)`] LOG_MONO_LE);
    MP_TAC(SPECL [`norm(y:real^3)`; `exp(abs c)`] LOG_MONO_LE)] THEN
  ASM_SIMP_TAC[REAL_EXP_POS_LT; LOG_EXP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REAL_ARITH_TAC);;

let STDS_CPHI_SUBLEVEL = prove
 (`!c. compact {x:real^3 | x IN (:real^3) DELETE vec 0 /\ stds_cphi x <= c} /\
       {x:real^3 | x IN (:real^3) DELETE vec 0 /\ stds_cphi x <= c} SUBSET
       cball(vec 0,exp(abs c)) DIFF ball(vec 0,exp(--(abs c)))`,
  GEN_TAC THEN
  ABBREV_TAC `A = cball(vec 0:real^3,exp(abs c)) DIFF ball(vec 0,exp(--(abs c)))` THEN
  SUBGOAL_THEN `{x:real^3 | x IN (:real^3) DELETE vec 0 /\ stds_cphi x <= c} SUBSET A`
  ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_UNIV; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`c:real`; `y:real^3`] STDS_CPHI_ANNULUS) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(A:real^3->bool) SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_BALL_0; IN_DELETE; IN_UNIV] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(norm(vec 0:real^3) < exp(--(abs c)))` THEN
    REWRITE_TAC[NORM_0; REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x:real^3 | x IN (:real^3) DELETE vec 0 /\ stds_cphi x <= c} =
                {x | x IN A /\ lift(stds_cphi x) IN {z:real^1 | drop z <= c}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; LIFT_DROP] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `A:real^3->bool` THEN
    CONJ_TAC THENL [EXPAND_TAC "A" THEN MATCH_MP_TAC BOUNDED_DIFF THEN
                    REWRITE_TAC[BOUNDED_CBALL]; SET_TAC[]];
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      REWRITE_TAC[STDS_CPHI_SMOOTH];
      EXPAND_TAC "A" THEN MATCH_MP_TAC CLOSED_DIFF THEN
      REWRITE_TAC[CLOSED_CBALL; OPEN_BALL];
      REWRITE_TAC[drop; CLOSED_HALFSPACE_COMPONENT_LE]]]);;

let STDS_CPHI_VOLUME = prove
 (`!s v. mfd_has_volume (subtopology euclidean ((:real^3) DELETE vec 0),
                         open_set_atlas ((:real^3) DELETE vec 0)) (cylinder_flow (&0))
                        {x | x IN (:real^3) DELETE vec 0 /\ stds_cphi x <= s} v
         ==> v <= &24 * exp(&6 * abs s) /\ (s < &1 ==> v = &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `S = {x:real^3 | x IN (:real^3) DELETE vec 0 /\ stds_cphi x <= s}` THEN
  MP_TAC(SPEC `s:real` STDS_CPHI_SUBLEVEL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(S:real^3->bool) SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean ((:real^3) DELETE vec 0))
                  (open_set_atlas ((:real^3) DELETE vec 0)) /\
                riemannian_metric (open_set_atlas ((:real^3) DELETE vec 0))
                  (cylinder_flow (&0)) /\
                riemannian_metric (open_set_atlas ((:real^3) DELETE vec 0)) (\x. mat 1)`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[OPEN_SET_ATLAS; LRG_CYL_OPEN; STDS_CYL_RIEM; REAL_ARITH `&0 < &1`] THEN
    REWRITE_TAC[open_set_atlas] THEN SIMP_TAC[MFD_EUCLIDEAN_OPEN; LRG_CYL_OPEN];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN SUBGOAL_THEN `S:real^3->bool = {}` SUBST_ALL_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN MP_TAC(SPEC `y:real^3` STDS_CPHI_GE) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(ISPECL [`subtopology euclidean ((:real^3) DELETE vec 0)`;
                           `open_set_atlas ((:real^3) DELETE vec 0)`;
                           `cylinder_flow (&0)`; `{}:real^3->bool`]
                          MFD_HAS_VOLUME_UNIQUE) THEN
      ASM_REWRITE_TAC[MFD_HAS_VOLUME_EMPTY]]] THEN
  SUBGOAL_THEN `mfd_has_volume (subtopology euclidean ((:real^3) DELETE vec 0),
                                open_set_atlas ((:real^3) DELETE vec 0)) (\x. mat 1)
                               S (measure(S:real^3->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas] THEN
    ASM_SIMP_TAC[MFD_HAS_VOLUME_EUCLIDEAN; LRG_CYL_OPEN; GSYM HAS_MEASURE_MEASURE;
                 MEASURABLE_COMPACT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean ((:real^3) DELETE vec 0)`;
                 `open_set_atlas ((:real^3) DELETE vec 0)`; `cylinder_flow (&0)`;
                 `\x:real^3. mat 1:real^3^3`; `S:real^3->bool`; `v:real`;
                 `measure(S:real^3->bool)`; `&2 * exp(&2 * abs s)`]
                MFD_HAS_VOLUME_COMPARE_QF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_EXP_POS_LE] THEN
    MAP_EVERY X_GEN_TAC [`y:real^3`; `w:real^3`] THEN DISCH_TAC THEN
    REWRITE_TAC[APX_CYL0_QUAD; MATRIX_VECTOR_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DOT_POS_LE] THEN
    SUBGOAL_THEN `exp(--(abs s)) <= norm(y:real^3)` ASSUME_TAC THENL
     [UNDISCH_TAC `(S:real^3->bool) SUBSET
                   cball(vec 0,exp(abs s)) DIFF ball(vec 0,exp(--(abs s)))` THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_BALL_0; REAL_NOT_LT] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(y:real^3) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `exp(--(abs s))` THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&1 <= exp(&2 * abs s) * norm(y:real^3) pow 2` MP_TAC THENL
     [SUBGOAL_THEN `exp(&2 * abs s) * exp(--(abs s)) pow 2 = &1` (SUBST1_TAC o SYM) THENL
       [REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_EXP_ADD] THEN
        REWRITE_TAC[REAL_ARITH `&2 * x + &2 * --x = &0`; REAL_EXP_0];
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `measure(S:real^3->bool) <= &4 / &3 * pi * exp(abs s) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `measure(cball(vec 0:real^3,exp(abs s)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[MEASURABLE_COMPACT; MEASURABLE_CBALL] THEN ASM SET_TAC[];
      SIMP_TAC[VOLUME_CBALL; REAL_EXP_POS_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2 * exp(&2 * abs s)) = sqrt(&2) * exp(abs s)` SUBST1_TAC THENL
   [SIMP_TAC[SQRT_MUL; REAL_POS; REAL_EXP_POS_LE] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ARITH `&2 * x = x + x`; REAL_EXP_ADD] THEN
    MATCH_MP_TAC SQRT_UNIQUE THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC PI2_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= measure(S:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURE_POS_LE; MEASURABLE_COMPACT]; ALL_TAC] THEN
  ABBREV_TAC `E = exp(abs s)` THEN
  SUBGOAL_THEN `&0 < E` ASSUME_TAC THENL [EXPAND_TAC "E" THEN REWRITE_TAC[REAL_EXP_POS_LT];
                                           ALL_TAC] THEN
  SUBGOAL_THEN `exp(&2 * abs s) = E pow 2 /\ exp(&6 * abs s) = E pow 6` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[GSYM REAL_EXP_N] THEN REWRITE_TAC[REAL_MUL_AC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&2 * E pow 2) * (sqrt(&2) * E)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_LT_IMP_LE; SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `v <= ((&2 * E pow 2) * (sqrt(&2) * E)) * (&4 / &3 * pi * E pow 3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((&2 * E pow 2) * (sqrt(&2) * E)) * measure(S:real^3->bool)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `v <= (&2 * E pow 2) * (sqrt(&2) * E) * measure(S:real^3->bool)` THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((&2 * E pow 2) * (sqrt(&2) * E)) * (&4 / &3 * pi * E pow 3) =
                (&8 / &3 * sqrt(&2) * pi) * E pow 6` SUBST_ALL_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&8 / &3 * sqrt(&2) * pi) * E pow 6` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `sqrt(&2) * pi <= &2 * &4` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness of the cylinder flow among complete flows of bounded curvature *)
(* from cyl(0) on the punctured space (the route hypothesis                  *)
(* P2C_REQ_UNIQ_COMPLETE, with the exhaustion stds_cphi).                    *)
(* ------------------------------------------------------------------------- *)

let STDS_CPHI_MFD_SMOOTH = prove
 (`mfd_smooth (open_set_atlas ((:real^3) DELETE vec 0)) (lift o stds_cphi)`,
  REWRITE_TAC[mfd_smooth; RFB_OPEN_SET_ATLAS_CASES; FORALL_UNWIND_THM2; FST; SND;
              IMAGE_ID] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\z:real^3. lift(stds_cphi z)` THEN
  REWRITE_TAC[STDS_CPHI_SMOOTH] THEN SIMP_TAC[o_THM; MFDM_CHART_INV_ID]);;

let STDS_CYL_UNIQUE = prove
 (`P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3)
   ==> !b g. &0 < b /\ b <= &1 /\
             ricci_flow_from (subtopology euclidean ((:real^3) DELETE vec 0),
                              open_set_atlas ((:real^3) DELETE vec 0)) (&0) b g /\
             (!y. ~(y = vec 0) ==> g (&0) y = cylinder_flow (&0) y) /\
             (!t. &0 <= t /\ t < b
                  ==> mfd_complete (subtopology euclidean ((:real^3) DELETE vec 0),
                                    open_set_atlas ((:real^3) DELETE vec 0)) (g t)) /\
             (!b1. b1 < b
                   ==> ?K. !t y. &0 <= t /\ t <= b1 /\ ~(y = vec 0)
                                 ==> mfd_rm_norm (open_set_atlas ((:real^3) DELETE vec 0))
                                                 (g t) y <= K)
             ==> !t y. &0 <= t /\ t < b /\ ~(y = vec 0) ==> g t y = cylinder_flow t y`,
  REWRITE_TAC[P2C_REQ_UNIQ_COMPLETE_STATEMENT] THEN DISCH_THEN(LABEL_TAC "U") THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd")))))) THEN
  X_CHOOSE_TAC `K1:real` STDS_CPHI_GRAD_LAP THEN
  ABBREV_TAC `C = max (&24) (max (&6) K1)` THEN
  USE_THEN "U" (MP_TAC o SPECL
    [`subtopology euclidean ((:real^3) DELETE vec 0)`;
     `open_set_atlas ((:real^3) DELETE vec 0)`; `&0`; `b:real`; `cylinder_flow`;
     `g:real->real^3->real^3^3`; `stds_cphi`; `C:real`]) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_DELETE; IN_UNIV] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN];
    MATCH_MP_TAC STDS_CYL_RFF THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC STDS_CYL_COMPLETE THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `b1:real` THEN DISCH_TAC THEN
    USE_THEN "bd" (MP_TAC o SPEC `b1:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `Kg:real`)] THEN
    EXISTS_TAC `max Kg (inv(&2 * (&1 - max b1 (&0))))` THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 * (&1 - t))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC STDS_CYL_RM_NORM THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= max k b`) THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `a <= k ==> a <= max k b`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `l:num` THEN X_CHOOSE_TAC `K0:real` (SPEC `l:num` P2CN_CYL0_RMD_BOUND) THEN
    EXISTS_TAC `K0 pow 2` THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[STDS_P_CONV];
    REWRITE_TAC[STDS_CPHI_MFD_SMOOTH];
    GEN_TAC THEN REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
    REWRITE_TAC[REWRITE_RULE[IN_DELETE; IN_UNIV] STDS_CPHI_SUBLEVEL] THEN SET_TAC[];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[STDS_P_CONV] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "C" THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `v:real`] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`s:real`; `v:real`]
      (REWRITE_RULE[IN_DELETE; IN_UNIV] STDS_CPHI_VOLUME)) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_CASES_TAC `s < &1` THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_EXP_POS_LE] THEN EXPAND_TAC "C" THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&24 * exp(&6 * abs s)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_POS; REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN
    CONJ_TAC THENL [EXPAND_TAC "C" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `abs s = s /\ &6 <= C` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "C" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The neck maps of a partial standard flow at far points x:                *)
(* phi_x(y) = ncinv(|nc x| Q_x y), Q_x orthogonal with Q_x e1 = x / |x|.     *)
(* phi_x(e1) = x; on an annulus mapped into the cylindrical region phi_x is *)
(* a diffeomorphism onto its image and pulls g0 back to cyl(0) exactly, and  *)
(* nc^* cyl(t) back to cyl(t).                                               *)
(* ------------------------------------------------------------------------- *)

let stds_rot = new_definition
 `stds_rot (x:real^3) = @Q:real^3^3. orthogonal_matrix Q /\ Q ** basis 1 = inv(norm x) % x`;;

let STDS_ROT = prove
 (`!x:real^3. ~(x = vec 0)
              ==> orthogonal_matrix (stds_rot x) /\ stds_rot x ** basis 1 = inv(norm x) % x`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[stds_rot] THEN CONV_TAC SELECT_CONV THEN
  MP_TAC(ISPECL [`basis 1:real^3`; `inv(norm x) % (x:real^3)`]
                ORTHOGONAL_TRANSFORMATION_EXISTS_1) THEN
  ANTS_TAC THENL
   [SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `matrix(f:real^3->real^3)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ORTHOGONAL_TRANSFORMATION_MATRIX]) THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let stds_nmap = new_definition
 `stds_nmap (g0:real^3->real^3^3) (A0:real) (x:real^3) (y:real^3) =
    p3s_ncinv g0 A0 (norm(p3_std_nc g0 A0 x) % (stds_rot x ** y))`;;

let STDS_NMAP_E1 = prove
 (`!g0 A0 (x:real^3). p3_std_initial g0 A0 /\ ~(x = vec 0)
                      ==> stds_nmap g0 A0 x (basis 1) = x`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[stds_nmap; STDS_ROT] THEN
  SUBGOAL_THEN `norm(p3_std_nc g0 A0 x) % inv(norm x) % (x:real^3) = p3_std_nc g0 A0 x`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[P3S_NC_NORM] THEN REWRITE_TAC[p3_std_nc];
    ASM_SIMP_TAC[P3S_NC_NCINV]]);;

let STDS_NC_MU_POS = prove
 (`!g0 A0 (x:real^3). ~(x = vec 0) ==> &0 < norm(p3_std_nc g0 A0 x)`,
  SIMP_TAC[P3S_NC_NORM; REAL_EXP_POS_LT]);;

(* The linear part L y = mu Q y and its inverse.                            *)

let STDS_LIN_FACTS = prove
 (`!mu (Q:real^3^3).
     &0 < mu /\ orthogonal_matrix Q
     ==> linear (\y:real^3. mu % (Q ** y)) /\ linear (\z:real^3. inv mu % (transp Q ** z)) /\
         (!y. inv mu % (transp Q ** (mu % (Q ** y))) = y) /\
         (!z. mu % (Q ** (inv mu % (transp Q ** z))) = z) /\
         (!y. norm(mu % (Q ** y)) = mu * norm y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[STDS_LINEAR_CQ] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_ASSOC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP ORTHOGONAL_MATRIX_TRANSP_LMUL) THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; MATRIX_VECTOR_MUL_LID; VECTOR_MUL_LID];
    GEN_TAC THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_ASSOC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP ORTHOGONAL_MATRIX_TRANSP_RMUL) THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; MATRIX_VECTOR_MUL_LID; VECTOR_MUL_LID];
    GEN_TAC THEN ASM_SIMP_TAC[NORM_MUL; ORTHOGONAL_MATRIX_NORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`]]);;

let STDS_NMAP_O = prove
 (`!g0 A0 (x:real^3).
     stds_nmap g0 A0 x =
     p3s_ncinv g0 A0 o (\y. norm(p3_std_nc g0 A0 x) % (stds_rot x ** y))`,
  REWRITE_TAC[FUN_EQ_THM; stds_nmap; o_THM]);;

let STDS_ANNULUS_LIN_IMAGE = prove
 (`!mu (Q:real^3^3) r1 r2.
     &0 < mu /\ orthogonal_matrix Q
     ==> IMAGE (\y:real^3. mu % (Q ** y)) (annulus r1 r2) = annulus (mu * r1) (mu * r2) /\
         IMAGE (\z:real^3. inv mu % (transp Q ** z)) (annulus (mu * r1) (mu * r2)) =
         annulus r1 r2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`mu:real`; `Q:real^3^3`] STDS_LIN_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "inv1") (CONJUNCTS_THEN2 (LABEL_TAC "inv2")
    (LABEL_TAC "nm"))))) THEN
  SUBGOAL_THEN `!z:real^3. norm(inv mu % (transp (Q:real^3^3) ** z)) = norm z / mu`
  (LABEL_TAC "nm2") THENL
   [GEN_TAC THEN ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN
    USE_THEN "nm" (MP_TAC o SPEC `inv mu % (transp (Q:real^3^3) ** (z:real^3))`) THEN
    USE_THEN "inv2" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; annulus; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "nm" (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ];
    DISCH_TAC THEN EXISTS_TAC `inv mu % (transp (Q:real^3^3) ** (z:real^3))` THEN
    USE_THEN "inv2" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "nm2" (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "nm2" (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN EXISTS_TAC `mu % ((Q:real^3^3) ** z)` THEN
    USE_THEN "inv1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "nm" (fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[REAL_LT_LMUL_EQ]]);;

let STDS_NMAP_DIFFEO = prove
 (`!g0 A0 (x:real^3) r1 r2.
     p3_std_initial g0 A0 /\ ~(x = vec 0) /\ &0 < r1 /\ r1 < r2 /\
     norm(p3_std_nc g0 A0 x) * r2 <= exp(&4 / sqrt(&2))
     ==> diffeomorphism_on (annulus r1 r2) (IMAGE (stds_nmap g0 A0 x) (annulus r1 r2))
           (stds_nmap g0 A0 x)
           ((\z. inv(norm(p3_std_nc g0 A0 x)) % (transp(stds_rot x) ** z)) o
            p3_std_nc g0 A0) /\
         (!y. y IN annulus r1 r2 ==> A0 < p3_std_dist g0 (stds_nmap g0 A0 x y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(p3_std_nc g0 A0 (x:real^3))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[STDS_NC_MU_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `orthogonal_matrix (stds_rot (x:real^3))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[STDS_ROT]; ALL_TAC] THEN
  REWRITE_TAC[STDS_NMAP_O] THEN
  ABBREV_TAC `mu = norm(p3_std_nc g0 A0 (x:real^3))` THEN
  ABBREV_TAC `Q = stds_rot (x:real^3)` THEN
  MP_TAC(SPECL [`mu:real`; `Q:real^3^3`] STDS_LIN_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`mu:real`; `Q:real^3^3`; `r1:real`; `r2:real`] STDS_ANNULUS_LIN_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL [REWRITE_TAC[P3S_SQRT2_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mu * r1 /\ &0 < mu * r2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * log(mu * r2) <= &4` ASSUME_TAC THENL
   [SUBGOAL_THEN `log(mu * r2) <= &4 / sqrt(&2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&4 / sqrt(&2)))` THEN
      CONJ_TAC THENL [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
                      REWRITE_TAC[LOG_EXP; REAL_LE_REFL]];
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `sqrt(&2) * log(mu * r1)`;
                 `sqrt(&2) * log(mu * r2)`] P3S_NC_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_LMUL_EQ; LOG_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_LMUL_EQ];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `{y:real^3 | exp((sqrt(&2) * log(mu * r1)) / sqrt(&2)) < norm y /\
                            norm y < exp((sqrt(&2) * log(mu * r2)) / sqrt(&2))} =
                annulus (mu * r1) (mu * r2)` SUBST1_TAC THENL
   [REWRITE_TAC[annulus] THEN
    SUBGOAL_THEN `!c. &0 < c ==> exp((sqrt(&2) * log c) / sqrt(&2)) = c`
      (fun th -> ASM_SIMP_TAC[th]) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(sqrt(&2) * log c) / sqrt(&2) = log c` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD; ASM_SIMP_TAC[EXP_LOG]];
    ALL_TAC] THEN
  ABBREV_TAC `V = {z:real^3 | sqrt(&2) * log(mu * r1) < A0 + &4 - p3_std_dist g0 z /\
                              A0 + &4 - p3_std_dist g0 z < sqrt(&2) * log(mu * r2)}` THEN
  SUBGOAL_THEN `!z:real^3. z IN V ==> A0 < p3_std_dist g0 z` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IMAGE_o; OPEN_ANNULUS] THEN
  SUBGOAL_THEN `!y:real^3. y IN annulus r1 r2 ==> mu % ((Q:real^3^3) ** y) IN annulus (mu * r1) (mu * r2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (\y:real^3. mu % ((Q:real^3^3) ** y)) (annulus r1 r2) =
                 annulus (mu * r1) (mu * r2)` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN V ==> p3_std_nc g0 A0 z IN annulus (mu * r1) (mu * r2)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN annulus (mu * r1) (mu * r2) ==> p3s_ncinv g0 A0 w IN V`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[o_THM];
    ASM_SIMP_TAC[o_THM];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `annulus (mu * r1) (mu * r2):real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS; SUBSET_REFL] THEN
    SUBGOAL_THEN `(\y:real^3. mu % ((Q:real^3^3) ** y)) = (\y. mu % (Q ** y)) o (\y. y)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS; SMOOTH_MAP_ON_ID];
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[o_THM]]);;

let STDS_NMAP_PULLBACK = prove
 (`!g0 A0 (x:real^3) r1 r2 t y.
     p3_std_initial g0 A0 /\ ~(x = vec 0) /\ &0 < r1 /\ r1 < r2 /\
     norm(p3_std_nc g0 A0 x) * r2 <= exp(&4 / sqrt(&2)) /\ y IN annulus r1 r2
     ==> mpullback (stds_nmap g0 A0 x) (mpullback (p3_std_nc g0 A0) (cylinder_flow t)) y =
         cylinder_flow t y /\
         mpullback (stds_nmap g0 A0 x) g0 y = cylinder_flow (&0) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `r1:real`; `r2:real`]
         STDS_NMAP_DIFFEO) THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(p3_std_nc g0 A0 (x:real^3))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[STDS_NC_MU_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `orthogonal_matrix (stds_rot (x:real^3))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[STDS_ROT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[P3S_A0_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN annulus r1 r2
                           ==> p3_std_nc g0 A0 (stds_nmap g0 A0 x w) =
                               norm(p3_std_nc g0 A0 x) % (stds_rot x ** w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN REWRITE_TAC[stds_nmap] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
                   `norm(p3_std_nc g0 A0 x) % (stds_rot x ** (w:real^3))`] P3S_NCINV_FACTS) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`norm(p3_std_nc g0 A0 (x:real^3))`; `stds_rot (x:real^3)`; `r1:real`; `r2:real`]
           STDS_ANNULUS_LIN_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `norm(p3_std_nc g0 A0 x) % (stds_rot x ** (w:real^3))`) THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
     [EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC
       `norm(p3_std_nc g0 A0 x) * r1 < norm(vec 0:real^3)` THEN
      REWRITE_TAC[NORM_0; REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&4` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `&0 < norm(norm(p3_std_nc g0 A0 x) % (stds_rot x ** (w:real^3)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `norm(p3_std_nc g0 A0 x) * r1` THEN
      ASM_SIMP_TAC[REAL_LT_MUL];
      ALL_TAC] THEN
    SUBGOAL_THEN `log(norm(norm(p3_std_nc g0 A0 x) % (stds_rot x ** (w:real^3)))) <
                  &4 / sqrt(&2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `log(exp(&4 / sqrt(&2)))` THEN
      CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[LOG_EXP; REAL_LE_REFL]] THEN
      ASM_SIMP_TAC[LOG_MONO_LT; REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[REAL_LT_RDIV_EQ; P3S_SQRT2_POS] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(stds_nmap g0 A0 x y = vec 0) /\ ~(y:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `!y:real^3. y IN annulus r1 r2 ==> A0 < p3_std_dist g0 (stds_nmap g0 A0 x y)` THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(MATCH_MP P3S_DIST_0 (ASSUME `p3_std_initial g0 A0`)) THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `vec 0 IN annulus r1 r2:real^3->bool` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; NORM_0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(stds_nmap g0 A0 x) differentiable at (y:real^3) /\
                (p3_std_nc g0 A0) differentiable at (stds_nmap g0 A0 x y)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `annulus r1 r2:real^3->bool` THEN ASM_REWRITE_TAC[OPEN_ANNULUS];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[LRG_CYL_OPEN; P3S_NC_SMOOTH; IN_DELETE; IN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. mpullback (stds_nmap g0 A0 x) (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) y =
                    cylinder_flow s (y:real^3)` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[APX_MPULLBACK_CHAIN] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `mpullback (\w:real^3. norm(p3_std_nc g0 A0 x) % (stds_rot x ** w))
                          (cylinder_flow s) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CG_MPULLBACK_LOCAL THEN EXISTS_TAC `annulus r1 r2:real^3->bool` THEN
      ASM_SIMP_TAC[OPEN_ANNULUS; o_THM];
      MATCH_MP_TAC STDS_CYL_CQ_PULLBACK THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (stds_nmap g0 A0 x) (mpullback (p3_std_nc g0 A0) (cylinder_flow (&0))) y` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC P2CG_MPULLBACK_PT THEN
  UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `!y:real^3. y IN annulus r1 r2 ==> A0 < p3_std_dist g0 (stds_nmap g0 A0 x y)` THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The exhaustion of the punctured space by annuli and the                  *)
(* exact slice limit of the far pointed views of a partial standard flow.   *)
(* ------------------------------------------------------------------------- *)

let stds_aW = new_definition
 `stds_aW (k:num) = annulus (exp(--(&k + &1))) (exp(&k + &1)):real^3->bool`;;

let STDS_CANNULUS_SUBSET = prove
 (`!a b. &0 < a
         ==> cball(vec 0:real^3,b) DIFF ball(vec 0,a) SUBSET (:real^3) DELETE vec 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_DIFF; IN_BALL_0; IN_DELETE; IN_UNIV] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `~(norm(vec 0:real^3) < a)` THEN ASM_REWRITE_TAC[NORM_0]);;

let STDS_AW_SUBSET = prove
 (`!k. stds_aW k SUBSET (:real^3) DELETE vec 0 /\ open(stds_aW k)`,
  GEN_TAC THEN REWRITE_TAC[stds_aW; OPEN_ANNULUS] THEN
  REWRITE_TAC[annulus; SUBSET; IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `exp(--(&k + &1)) < norm(vec 0:real^3)` THEN
  REWRITE_TAC[NORM_0; REAL_NOT_LT; REAL_EXP_POS_LE]);;

let STDS_AW_CLOSURE = prove
 (`!k. closure(stds_aW k) SUBSET
       cball(vec 0:real^3,exp(&k + &1)) DIFF ball(vec 0,exp(--(&k + &1)))`,
  GEN_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
  SIMP_TAC[CLOSED_DIFF; CLOSED_CBALL; OPEN_BALL] THEN
  REWRITE_TAC[stds_aW; annulus; SUBSET; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
  REAL_ARITH_TAC);;

let STDS_AW_MONO = prove
 (`!m n. m <= n ==> stds_aW m SUBSET stds_aW n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stds_aW; annulus; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `exp(--(&n + &1)) <= exp(--(&m + &1)) /\ exp(&m + &1) <= exp(&n + &1)`
  MP_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN UNDISCH_TAC `m:num <= n` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let STDS_AW_UNIONS = prove
 (`UNIONS {stds_aW k | k IN (:num)} = (:real^3) DELETE vec 0`,
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV; IN_DELETE] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPEC `k:num` STDS_AW_SUBSET) THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN ASM_MESON_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    MP_TAC(SPEC `abs(log(norm(y:real^3)))` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN EXISTS_TAC `stds_aW k` THEN
    CONJ_TAC THENL [EXISTS_TAC `k:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[stds_aW; annulus; IN_ELIM_THM] THEN
    SUBGOAL_THEN `norm(y:real^3) = exp(log(norm y))` SUBST1_TAC THENL
     [ASM_SIMP_TAC[EXP_LOG]; ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC]);;

let STDS_AW_BASIS = prove
 (`!k. basis 1 IN stds_aW k`,
  GEN_TAC THEN SIMP_TAC[stds_aW; annulus; IN_ELIM_THM; NORM_BASIS; DIMINDEX_3; ARITH] THEN
  MP_TAC(SPECL [`--(&k + &1)`; `&0`] REAL_EXP_MONO_LT) THEN
  MP_TAC(SPECL [`&0`; `&k + &1`] REAL_EXP_MONO_LT) THEN
  REWRITE_TAC[REAL_EXP_0] THEN MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC);;

let STDS_AW_FACTS = prove
 (`(!k. open_in (subtopology euclidean ((:real^3) DELETE vec 0)) (stds_aW k) /\
        basis 1 IN stds_aW k /\
        compact_in (subtopology euclidean ((:real^3) DELETE vec 0))
          (subtopology euclidean ((:real^3) DELETE vec 0) closure_of stds_aW k) /\
        subtopology euclidean ((:real^3) DELETE vec 0) closure_of stds_aW k SUBSET
        stds_aW (SUC k)) /\
   UNIONS {stds_aW k | k IN (:num)} = (:real^3) DELETE vec 0 /\
   (!m n. m <= n ==> stds_aW m SUBSET stds_aW n) /\
   (!k. stds_aW k SUBSET (:real^3) DELETE vec 0) /\
   (!k. open(stds_aW k))`,
  REWRITE_TAC[STDS_AW_SUBSET; STDS_AW_MONO; STDS_AW_UNIONS; STDS_AW_BASIS] THEN
  X_GEN_TAC `k:num` THEN
  MP_TAC(SPEC `k:num` STDS_AW_SUBSET) THEN MP_TAC(SPEC `k:num` STDS_AW_CLOSURE) THEN
  ABBREV_TAC `W = stds_aW k` THEN
  ABBREV_TAC `A = cball(vec 0:real^3,exp(&k + &1)) DIFF ball(vec 0,exp(--(&k + &1)))` THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
    SUBGOAL_THEN `A SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
     [EXPAND_TAC "A" THEN MATCH_MP_TAC STDS_CANNULUS_SUBSET THEN
      REWRITE_TAC[REAL_EXP_POS_LT];
      ALL_TAC] THEN
    SUBGOAL_THEN `((:real^3) DELETE vec 0) INTER W = W /\
                  ((:real^3) DELETE vec 0) INTER closure W = closure W`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> t INTER s = s`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `A:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CLOSURE] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "W" THEN REWRITE_TAC[stds_aW] THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^3,exp(&k + &1))` THEN
      REWRITE_TAC[BOUNDED_BALL; SUBSET; annulus; IN_ELIM_THM; IN_BALL_0] THEN SIMP_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `A:real^3->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
    MATCH_MP_TAC(SET_RULE `(t:real^3->bool) SUBSET u ==> s INTER t SUBSET u`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(W:real^3->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `A:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "A" THEN
    REWRITE_TAC[stds_aW; annulus; SUBSET; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0;
                GSYM REAL_OF_NUM_SUC; REAL_NOT_LT] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `exp(--((&k + &1) + &1)) < exp(--(&k + &1)) /\
                  exp(&k + &1) < exp((&k + &1) + &1)` MP_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LT] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

let STDS_RFS_PULLBACK_UNIV = prove
 (`!(e:real^3->real^3) g. rfs_pullback (open_set_atlas (:real^3)) e g = mpullback e g`,
  REWRITE_TAC[FUN_EQ_THM; rfs_pullback; P2CN_OPEN_UNIV_CHART; P2C_OPEN_SET_METRIC_LOCAL_UNIV;
              SND] THEN
  REWRITE_TAC[o_DEF; ETA_AX]);;

let STDS_FAR_MU = prove
 (`!g0 A0 (x:real^3) m.
     p3_std_initial g0 A0 /\ A0 + sqrt(&2) * (&m + &1) <= p3_std_dist g0 x
     ==> ~(x = vec 0) /\ norm(p3_std_nc g0 A0 x) * exp(&m + &1) <= exp(&4 / sqrt(&2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0 /\ &0 < sqrt(&2)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[P3S_A0_POS; P3S_SQRT2_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&2) * (&m + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MP_TAC(SPEC `m:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(MATCH_MP P3S_DIST_0 (ASSUME `p3_std_initial g0 A0`)) THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[P3S_NC_NORM; GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[REAL_ARITH `a / s + b <= c / s <=> (a - c) / s + b <= &0`] THEN
  SUBGOAL_THEN `((A0 + &4 - p3_std_dist g0 x) - &4) / sqrt(&2) + (&m + &1) =
                ((A0 - p3_std_dist g0 x) + sqrt(&2) * (&m + &1)) / sqrt(&2)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC);;

let STDS_AW_COMPACT = prove
 (`!K. compact K /\ K SUBSET (:real^3) DELETE vec 0
       ==> ?k0. !k. k0 <= k ==> K SUBSET stds_aW k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `K:real^3->bool` COMPACT_IMP_BOUNDED) THEN ASM_REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:real^3->bool`; `vec 0:real^3`] SEPARATE_POINT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `abs(log B) + abs(log d)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN EXISTS_TAC `k0:num` THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&k0 <= &k` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; stds_aW; annulus; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `d:real` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `exp(--(&k + &1)) < exp(log d)` MP_TAC THENL
       [REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[EXP_LOG]];
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[DIST_0]];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `B:real` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(log B + &1)` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_EXP_ADD; EXP_LOG] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`&0`; `&1`] REAL_EXP_MONO_LT) THEN
        REWRITE_TAC[REAL_EXP_0] THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC]]]);;

let STDS_BASIS1_NZ = prove
 (`~(basis 1:real^3 = vec 0)`,
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH]);;

let STDS_ASYM_SLICE = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) (xs:num->real^3).
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\
     (!n. A0 + sqrt(&2) * (&n + &1) <= p3_std_dist g0 (xs n))
     ==> p2c_slice_limit_with
           (\n. rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < te} G)
           xs (\n. &0) (\n. &1)
           (subtopology euclidean ((:real^3) DELETE vec 0),
            open_set_atlas ((:real^3) DELETE vec 0))
           (cylinder_flow (&0)) (basis 1) stds_aW (\n. stds_nmap g0 A0 (xs n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < te /\ (G:real->real^3->real^3^3) (&0) = g0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[STDS_PARTIAL_POS; p3_partial_std]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~((xs:num->real^3) n = vec 0) /\
                    norm(p3_std_nc g0 A0 (xs n)) * exp(&n + &1) <= exp(&4 / sqrt(&2))`
  (LABEL_TAC "far") THENL
   [GEN_TAC THEN MATCH_MP_TAC STDS_FAR_MU THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC STDS_AW_FACTS THEN STRIP_TAC THEN
  REWRITE_TAC[p2c_slice_limit_with; P2CF_FLOW_VIEW_PARTS; IN_ELIM_THM; REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_DELETE; IN_UNIV; REAL_LT_01;
                  STDS_BASIS1_NZ] THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; LRG_CYL_OPEN; STDS_CYL_RIEM; REAL_ARITH `&0 < &1`;
               HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN; STDS_NMAP_E1] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN
    EXISTS_TAC `(\z. inv(norm(p3_std_nc g0 A0 ((xs:num->real^3) k))) %
                     (transp(stds_rot (xs k)) ** z)) o p3_std_nc g0 A0` THEN
    MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `(:real^3)`; `stds_aW k`;
                   `IMAGE (stds_nmap g0 A0 ((xs:num->real^3) k)) (stds_aW k)`;
                   `stds_nmap g0 A0 ((xs:num->real^3) k)`;
                   `(\z. inv(norm(p3_std_nc g0 A0 ((xs:num->real^3) k))) %
                         (transp(stds_rot (xs k)) ** z)) o p3_std_nc g0 A0`]
                  MFD_DIFFEO_OPEN_SET_ATLAS) THEN
    ASM_REWRITE_TAC[LRG_CYL_OPEN; OPEN_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[stds_aW] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `(xs:num->real^3) k`;
                  `exp(--(&k + &1))`; `exp(&k + &1)`] STDS_NMAP_DIFFEO) THEN
    USE_THEN "far" (MP_TAC o SPEC `k:num`) THEN
    ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`K:real^3->bool`; `m:num`; `eta:real`] THEN
  REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN STRIP_TAC THEN
  MP_TAC(SPEC `K:real^3->bool` STDS_AW_COMPACT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN EXISTS_TAC `k0:num` THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(K:real^3->bool) SUBSET stds_aW k` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN stds_aW k /\ y IN (:real^3) DELETE vec 0` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_CHART_AT; STDS_RFS_PULLBACK_UNIV; MATRIX_CMUL_LID] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `lck_dist2 m (cylinder_flow (&0)) (cylinder_flow (&0)) (y:real^3)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[P2BL_LCK_DIST2_REFL]] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LCK_DIST2_LOCAL THEN
  EXISTS_TAC `stds_aW k` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL; LRG_CYL_OPEN] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback (stds_nmap g0 A0 ((xs:num->real^3) k)) g0 z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CG_MPULLBACK_LOCAL THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[LRG_CYL_OPEN; o_THM; MFDM_CHART_INV_ID];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `(xs:num->real^3) k`;
                `exp(--(&k + &1))`; `exp(&k + &1)`; `&0`; `z:real^3`] STDS_NMAP_PULLBACK) THEN
  USE_THEN "far" (MP_TAC o SPEC `k:num`) THEN
  UNDISCH_TAC `(z:real^3) IN stds_aW k` THEN
  ASM_SIMP_TAC[stds_aW; REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]]);;

let STDS_NMAP_OPEN_IMAGE = prove
 (`!g0 A0 (x:real^3) m.
     p3_std_initial g0 A0 /\ A0 + sqrt(&2) * (&m + &1) <= p3_std_dist g0 x
     ==> open(IMAGE (stds_nmap g0 A0 x) (stds_aW m))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `m:num`] STDS_FAR_MU) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`;
                `exp(--(&m + &1))`; `exp(&m + &1)`] STDS_NMAP_DIFFEO) THEN
  ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT; stds_aW] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[diffeomorphism_on]]);;

let STDS_ASYM_REGION = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) (xs:num->real^3) T'.
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\ T' < te /\
     (!n. A0 + sqrt(&2) * (&n + &1) <= p3_std_dist g0 (xs n))
     ==> !m a b. real_interval[a,b] SUBSET real_interval[&0,T']
           ==> ?CM N. !n. N <= n
                 ==> (!s. a <= s /\ s <= b
                          ==> IMAGE (stds_nmap g0 A0 (xs n)) (stds_aW m) SUBSET
                              topspace(rfs_vtop (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                                   {s | &0 <= s /\ s < te} G) s)) /\
                     rfs_persists (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                     {s | &0 <= s /\ s < te} G)
                                  (IMAGE (stds_nmap g0 A0 (xs n)) (stds_aW m)) a b /\
                     !s y. a <= s /\ s <= b /\
                           y IN IMAGE (stds_nmap g0 A0 (xs n)) (stds_aW m)
                           ==> p3_vrm (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                         {s | &0 <= s /\ s < te} G) s y <= CM`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `a:real`; `b:real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s. a <= s /\ s <= b ==> &0 <= s /\ s <= T'` (LABEL_TAC "ab") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `s IN real_interval[&0,T']` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL];
      REWRITE_TAC[IN_REAL_INTERVAL]];
    ALL_TAC] THEN
  UNDISCH_TAC `p3_partial_std g0 te (G:real->real^3->real^3^3)` THEN
  REWRITE_TAC[p3_partial_std] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `T':real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (LABEL_TAC "K")) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `m:num`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[P2CF_FLOW_VIEW_PARTS; P2CO_PERSISTS_ALT; p3_vrm; IN_ELIM_THM] THEN
  SUBGOAL_THEN `A0 + sqrt(&2) * (&m + &1) <= p3_std_dist g0 ((xs:num->real^3) n)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A0 + sqrt(&2) * (&n + &1)` THEN
    ASM_REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
    UNDISCH_TAC `m:num <= n` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "ab" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= s /\ s < te` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[TOPSPACE_EUCLIDEAN; SUBSET_UNIV]];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "ab" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= s /\ s < te` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P2C_EUCLID_FACTS; GSYM OPEN_IN] THEN
    MATCH_MP_TAC STDS_NMAP_OPEN_IMAGE THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "ab" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    USE_THEN "K" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Completeness of a Ricci flow from a complete metric under a               *)
(* curvature bound, and the limit of the far pointed views (Prop 5.14 on the *)
(* punctured space), which is the cylinder flow.                            *)
(* ------------------------------------------------------------------------- *)

let STDS_COMPLETE_FROM_BOUND = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) b (g:real->A->real^3^3) M.
     ricci_flow_from (top,atlas) (&0) b g /\ &0 <= M /\
     mfd_complete (top,atlas) (g (&0)) /\
     (!s y. &0 <= s /\ s < b /\ y IN topspace top ==> mfd_rm_norm atlas (g s) y <= M)
     ==> !s. &0 <= s /\ s < b ==> mfd_complete (top,atlas) (g s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:A`,`:A`; `:3`,`:N`] RFU_RIC_FROM_RMNORM) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cr:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RIC"))) THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < b ==> riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t)`
  (LABEL_TAC "RM") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t = &0` THENL
     [ASM_MESON_TAC[ricci_flow_from];
      UNDISCH_TAC `ricci_flow_from (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (&0) b (g:real->A->real^3^3)` THEN
      REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `&0`; `b:real`;
                 `g:real->A->real^3^3`; `Cr * M`] RFA_METRIC_EQUIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `v:real^3`] THEN STRIP_TAC THEN
    USE_THEN "RIC" (MP_TAC o ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                     `(g:real->A->real^3^3) t`; `x:A`; `M:real`;
                                     `v:real^3`]) THEN
    ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[REAL_MUL_ASSOC]] THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN(LABEL_TAC "EQV")] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC P2CO_COMPLETE_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`(g:real->A->real^3^3) (&0)`; `exp(&2 * (Cr * M) * t)`] THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "RM" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    USE_THEN "RM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z:A`; `v:real^3`] THEN DISCH_TAC THEN
  USE_THEN "EQV" (MP_TAC o SPECL [`t:real`; `z:A`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(&2 * (Cr * M) * t) *
              (exp(--(&2 * (Cr * M) * t)) *
               ((v:real^3) dot ((g:real->A->real^3^3) (&0) z ** v)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_EXP_ADD; REAL_ADD_RINV; REAL_EXP_0;
                REAL_MUL_LID; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]]);;

let STDS_ASYM_LIMIT = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) T' (xs:num->real^3).
     P2C_PROP_5_14_STATEMENT (:real^3) (:real^3) /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\ &0 < T' /\ T' < te /\
     (!n. A0 + sqrt(&2) * (&n + &1) <= p3_std_dist g0 (xs n))
     ==> ?sub g K.
           p3_subseq sub /\ g (&0) = cylinder_flow (&0) /\ &0 <= K /\
           p2c_flow_limit_with
             (\n. rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < te} G)
             (xs o sub) ((\n. &0) o sub) ((\n. &1) o sub) (real_interval[&0,T'])
             (subtopology euclidean ((:real^3) DELETE vec 0),
              open_set_atlas ((:real^3) DELETE vec 0))
             g (basis 1) stds_aW ((\n. stds_nmap g0 A0 (xs n)) o sub) /\
           (!s. s IN real_interval[&0,T']
                ==> riemannian_metric (open_set_atlas ((:real^3) DELETE vec 0)) (g s)) /\
           ricci_flow_from (subtopology euclidean ((:real^3) DELETE vec 0),
                            open_set_atlas ((:real^3) DELETE vec 0)) (&0) T' g /\
           (!s y. &0 <= s /\ s <= T' /\ ~(y = vec 0)
                  ==> mfd_rm_norm (open_set_atlas ((:real^3) DELETE vec 0)) (g s) y <= K)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "p514") (CONJUNCTS_THEN2 (LABEL_TAC "freg")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < te /\ (G:real->real^3->real^3^3) (&0) = g0 /\
                ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) te G`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[STDS_PARTIAL_POS; p3_partial_std]; ALL_TAC] THEN
  SUBGOAL_THEN `?K. &0 <= K /\
                    !t x. &0 <= t /\ t <= T'
                          ==> mfd_rm_norm (open_set_atlas (:real^3)) (G t) x <= K`
  (X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "K"))) THENL
   [UNDISCH_TAC `p3_partial_std g0 te (G:real->real^3->real^3^3)` THEN
    REWRITE_TAC[p3_partial_std] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `T':real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `K0:real`) THEN EXISTS_TAC `abs K0` THEN
    REWRITE_TAC[REAL_ABS_POS] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= k ==> x <= abs k`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "p514" (MP_TAC o SPECL
    [`\n:num. rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < te}
                            (G:real->real^3->real^3^3)`;
     `xs:num->real^3`; `\n:num. &0`; `\n:num. &1`; `real_interval[&0,T']`;
     `subtopology euclidean ((:real^3) DELETE vec 0)`;
     `open_set_atlas ((:real^3) DELETE vec 0)`; `cylinder_flow (&0)`; `basis 1:real^3`;
     `stds_aW`; `\n. stds_nmap g0 A0 ((xs:num->real^3) n)`] o
     REWRITE_RULE[P2C_PROP_5_14_STATEMENT]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IS_REALINTERVAL_INTERVAL];
      ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_LT_IMP_LE];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `a0:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `&0`) THEN ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC;
      TRY GEN_TAC THEN BETA_TAC THEN
      USE_THEN "freg" (MATCH_MP_TAC o REWRITE_RULE[P2C_FLOW_VIEW_REGULAR_STATEMENT]) THEN
      ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN];
      MATCH_MP_TAC STDS_ASYM_SLICE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ADD_LID; REAL_DIV_1; REAL_MUL_RID] THEN
      MATCH_MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `te:real`;
                           `G:real->real^3->real^3^3`; `xs:num->real^3`; `T':real`]
                          STDS_ASYM_REGION) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num`
    (X_CHOOSE_THEN `g:real->real^3->real^3^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `g:real->real^3->real^3^3`; `K:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
    [`\n:num. rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < te}
                            (G:real->real^3->real^3^3)`;
     `(xs:num->real^3) o (sub:num->num)`; `(\n:num. &0) o (sub:num->num)`;
     `(\n:num. &1) o (sub:num->num)`; `real_interval[&0,T']`;
     `subtopology euclidean ((:real^3) DELETE vec 0)`;
     `open_set_atlas ((:real^3) DELETE vec 0)`; `g:real->real^3->real^3^3`; `basis 1:real^3`;
     `stds_aW`; `(\n. stds_nmap g0 A0 ((xs:num->real^3) n)) o (sub:num->num)`;
     `s:real`; `y:real^3`; `K:real`] STDS_LIM_RM_BOUND) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    TRY GEN_TAC THEN BETA_TAC THEN
    USE_THEN "freg" (MATCH_MP_TAC o REWRITE_RULE[P2C_FLOW_VIEW_REGULAR_STATEMENT]) THEN
    ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_DELETE; IN_UNIV];
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[o_THM; REAL_ADD_LID; REAL_DIV_1; REAL_MUL_RID; P2CF_FLOW_VIEW_PARTS] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "K" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The limit is the cylinder flow up to min T' 1.                            *)

let STDS_ASYM_CYL = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) T' (xs:num->real^3).
     P2C_PROP_5_14_STATEMENT (:real^3) (:real^3) /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3) /\
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\ &0 < T' /\ T' < te /\
     (!n. A0 + sqrt(&2) * (&n + &1) <= p3_std_dist g0 (xs n))
     ==> ?sub g.
           p3_subseq sub /\
           p2c_flow_limit_with
             (\n. rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < te} G)
             (xs o sub) ((\n. &0) o sub) ((\n. &1) o sub) (real_interval[&0,T'])
             (subtopology euclidean ((:real^3) DELETE vec 0),
              open_set_atlas ((:real^3) DELETE vec 0))
             g (basis 1) stds_aW ((\n. stds_nmap g0 A0 (xs n)) o sub) /\
           (!s. s IN real_interval[&0,T']
                ==> riemannian_metric (open_set_atlas ((:real^3) DELETE vec 0)) (g s)) /\
           ricci_flow_from (subtopology euclidean ((:real^3) DELETE vec 0),
                            open_set_atlas ((:real^3) DELETE vec 0)) (&0) T' g /\
           (!s y. &0 <= s /\ s < min T' (&1) /\ ~(y = vec 0) ==> g s y = cylinder_flow s y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `te:real`; `G:real->real^3->real^3^3`;
                `T':real`; `xs:num->real^3`] STDS_ASYM_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `g:real->real^3->real^3^3`
    (X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `g:real->real^3->real^3^3`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`subtopology euclidean ((:real^3) DELETE vec 0)`;
                 `open_set_atlas ((:real^3) DELETE vec 0)`; `T':real`;
                 `g:real->real^3->real^3^3`; `K:real`] STDS_COMPLETE_FROM_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[STDS_CYL0_COMPLETE; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_DELETE; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(MATCH_MP STDS_CYL_UNIQUE
    (ASSUME `P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3)`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`min T' (&1)`; `g:real->real^3->real^3^3`]) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`&0`; `T':real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `b1:real` THEN DISCH_TAC THEN EXISTS_TAC `K:real` THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* Points of the standard initial metric at any prescribed distances.       *)

let STDS_FAR_SEQ = prove
 (`!g0 A0 (c:num->real). p3_std_initial g0 A0 /\ (!n. &0 <= c n)
     ==> ?xs:num->real^3. !n. p3_std_dist g0 (xs n) = c n`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `\n:num. p3s_rad_rinv g0 ((c:num->real) n) % basis 1:real^3` THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
                 `p3s_rad_rinv g0 ((c:num->real) n) % basis 1:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `(c:num->real) n`] P3S_RINV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID;
               REAL_ARITH `&0 <= x ==> abs x = x`]);;

(* Cor 12.8: every partial standard flow has te <= 1.                         *)

let STDS_TE_LE_1 = prove
 (`!g0 A0 te (G:real->real^3->real^3^3).
     P2C_PROP_5_14_STATEMENT (:real^3) (:real^3) /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3) /\
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G
     ==> te <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `T' = (&1 + te) / &2` THEN
  SUBGOAL_THEN `&1 < T' /\ T' < te` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`;
                `\n:num. A0 + sqrt(&2) * (&n + &1)`] STDS_FAR_SEQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [ASM_MESON_TAC[P3S_A0_POS; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
      MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC];
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `xs:num->real^3`)] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `te:real`; `G:real->real^3->real^3^3`;
                `T':real`; `xs:num->real^3`] STDS_ASYM_CYL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `g:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `min T' (&1) = &1` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `f = \s. ((g:real->real^3->real^3^3) s (basis 1))$2$2` THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s < &1 ==> f s = &2 * (&1 - s)` (LABEL_TAC "fcyl") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "f" THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
      (CONJ (ASSUME `&0 <= s`) (CONJ (ASSUME `s < &1`) STDS_BASIS1_NZ))]) THEN
    SIMP_TAC[GSYM RFB_BASIS_DOT_MATRIX; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[cylinder_flow; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
                MATRIX_VECTOR_MUL_LID; RFB_OUTER_MUL; DOT_RMUL; DOT_RADD] THEN
    SIMP_TAC[NORM_BASIS; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `f real_continuous atreal (&1)` MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
    UNDISCH_TAC `ricci_flow_from (subtopology euclidean ((:real^3) DELETE vec 0),
                                  open_set_atlas ((:real^3) DELETE vec 0)) (&0) T'
                                 (g:real->real^3->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
    EXPAND_TAC "f" THEN
    EXISTS_TAC `--(&2) * mfd_ricci_matrix (open_set_atlas ((:real^3) DELETE vec 0))
                          ((g:real->real^3->real^3^3) (&1)) (basis 1)$2$2` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_DELETE; IN_UNIV; STDS_BASIS1_NZ;
                    DIMINDEX_3] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < f(&1)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN BETA_TAC THEN
    SIMP_TAC[GSYM RFB_BASIS_DOT_MATRIX; DIMINDEX_3; ARITH] THEN
    MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH; IN_DELETE; IN_UNIV; STDS_BASIS1_NZ] THEN
    MATCH_MP_TAC P3S_OPEN_RIEM_FIELD THEN REWRITE_TAC[LRG_CYL_OPEN] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `f(&1) / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `h = min (d / &2) (min (f(&1) / &8) (&1 / &2))` THEN
  SUBGOAL_THEN `&0 < h /\ h <= d / &2 /\ h <= f(&1) / &8 /\ h <= &1 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1 - h`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "fcyl" (MP_TAC o SPEC `&1 - h`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Prop 12.7 in the coordinates of the far neck maps: on a                   *)
(* compact subset of the punctured space and up to a time T' < min te 1 the  *)
(* pulled back flow is uniformly close to the cylinder flow far out.        *)
(* ------------------------------------------------------------------------- *)

let STDS_ASYM_CLOSE = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) T' K0 m eta.
     P2C_PROP_5_14_STATEMENT (:real^3) (:real^3) /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3) /\
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\ &0 <= T' /\ T' < te /\ T' < &1 /\
     compact K0 /\ K0 SUBSET (:real^3) DELETE vec 0 /\ &0 < eta
     ==> ?A1. !x s y. A1 < p3_std_dist g0 x /\ &0 <= s /\ s <= T' /\ y IN K0
                      ==> lck_dist2 m (cylinder_flow s)
                                      (mpullback (stds_nmap g0 A0 x) (G s)) y < eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `T2 = (T' + min te (&1)) / &2` THEN
  SUBGOAL_THEN `T' < T2 /\ T2 < te /\ T2 < &1 /\ &0 < T2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN `n:num` o SPEC `A0 + sqrt(&2) * (&n + &1)`) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:num->real^3` (X_CHOOSE_THEN `ss:num->real`
    (X_CHOOSE_THEN `ys:num->real^3` (LABEL_TAC "bad")))) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `te:real`; `G:real->real^3->real^3^3`;
                `T2:real`; `xs:num->real^3`] STDS_ASYM_CYL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    USE_THEN "bad" (fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT1(SPEC `n:num` th))]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `g:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
              CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `T':real`; `K0:real^3->bool`; `m:num`; `eta:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (MP_TAC o SPEC `k0:num`)) THEN
  REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "conv"))) THEN
  USE_THEN "bad" (MP_TAC o SPEC `(sub:num->num) k0`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `(ys:num->real^3) ((sub:num->num) k0) IN (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "conv" (MP_TAC o SPECL [`(ss:num->real) ((sub:num->num) k0)`;
                                   `(ys:num->real^3) ((sub:num->num) k0)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_THM; REAL_ADD_LID; REAL_DIV_1; MATRIX_CMUL_LID; P2CF_FLOW_VIEW_PARTS] THEN
  SIMP_TAC[RFB_OPEN_SET_CHART_AT; STDS_RFS_PULLBACK_UNIV;
           ASSUME `(ys:num->real^3) ((sub:num->num) k0) IN (:real^3) DELETE vec 0`] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a < e ==> b < e`) THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
  ASM_REWRITE_TAC[LRG_CYL_OPEN] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL; LRG_CYL_OPEN] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(z:real^3) IN (:real^3) DELETE vec 0` THEN
    REWRITE_TAC[IN_DELETE; IN_UNIV] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2CG_MPULLBACK_LOCAL THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[LRG_CYL_OPEN; o_THM; MFDM_CHART_INV_ID]]);;

(* ------------------------------------------------------------------------- *)
(* Prop 12.7 in the coordinates of g0 (the P4 form): far out                 *)
(* and up to Tp < min te 1, G t is close to nc^* cyl(t) at x.                *)
(* ------------------------------------------------------------------------- *)

(* The transfer from the neck coordinates at e1 to the point x.            *)

let STDS_NMAP_TRANSFER = prove
 (`!g0 A0 (x:real^3) (H:real^3->real^3^3) t k.
     p3_std_initial g0 A0 /\ A0 + sqrt(&2) * (&0 + &1) <= p3_std_dist g0 x /\ t < &1 /\
     metric_field (:real^3) H
     ==> lck_dist2 k (mpullback (p3_std_nc g0 A0) (cylinder_flow t)) H x =
         lck_dist2 k (cylinder_flow t) (mpullback (stds_nmap g0 A0 x) H) (basis 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `0`] STDS_FAR_MU) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^3. w IN stds_aW 0 ==> ~(stds_nmap g0 A0 x w = vec 0)` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`;
                  `exp(--(&0 + &1))`; `exp(&0 + &1)`] STDS_NMAP_DIFFEO) THEN
    ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(w:real^3) IN stds_aW 0` THEN REWRITE_TAC[stds_aW]; ALL_TAC] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `A0 < p3_std_dist g0 (stds_nmap g0 A0 x w)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(MATCH_MP P3S_DIST_0 (ASSUME `p3_std_initial g0 A0`)) THEN
    MP_TAC(MATCH_MP P3S_A0_POS (ASSUME `p3_std_initial g0 A0`)) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `U' = stds_aW 0` THEN
  SUBGOAL_THEN `(U':real^3->bool) SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [EXPAND_TAC "U'" THEN REWRITE_TAC[STDS_AW_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `phi = stds_nmap g0 A0 (x:real^3)` THEN
  ABBREV_TAC `psi = (\z:real^3. inv(norm(p3_std_nc g0 A0 x)) % (transp(stds_rot x) ** z)) o
                    p3_std_nc g0 A0` THEN
  ABBREV_TAC `U = IMAGE (phi:real^3->real^3) U'` THEN
  SUBGOAL_THEN `diffeomorphism_on (U':real^3->bool) (U:real^3->bool) (phi:real^3->real^3) psi` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "U'"; "phi"; "psi"] THEN REWRITE_TAC[stds_aW] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`;
                  `exp(--(&0 + &1))`; `exp(&0 + &1)`] STDS_NMAP_DIFFEO) THEN
    ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `basis 1 IN (U':real^3->bool) /\ (phi:real^3->real^3) (basis 1) = (x:real^3) /\
                x IN (U:real^3->bool) /\ (psi:real^3->real^3) x = basis 1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `basis 1 IN (U':real^3->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "U'" THEN REWRITE_TAC[STDS_AW_BASIS]; ALL_TAC] THEN
    SUBGOAL_THEN `(phi:real^3->real^3) (basis 1) = x` ASSUME_TAC THENL
     [EXPAND_TAC "phi" THEN ASM_SIMP_TAC[STDS_NMAP_E1]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `metric_field (U:real^3->bool) (H:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN (U:real^3->bool) ==> ~(z = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lck_dist2 k (mpullback (psi:real^3->real^3) (cylinder_flow t))
                          (mpullback psi (mpullback phi (H:real^3->real^3^3))) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(psi:real^3->real^3) differentiable at z /\
                  (phi:real^3->real^3) differentiable at (psi z) /\
                  (p3_std_nc g0 A0) differentiable at z`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
       [EXISTS_TAC `U:real^3->bool`; EXISTS_TAC `U':real^3->bool`;
        EXISTS_TAC `(:real^3) DELETE vec 0`] THEN
      ASM_SIMP_TAC[LRG_CYL_OPEN; P3S_NC_SMOOTH; IN_DELETE; IN_UNIV] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "psi" THEN
      SUBGOAL_THEN `(\z:real^3. inv(norm(p3_std_nc g0 A0 x)) % (transp(stds_rot x) ** z))
                    differentiable at (p3_std_nc g0 A0 z)` ASSUME_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_LINEAR THEN REWRITE_TAC[STDS_LINEAR_CQ]; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM APX_MPULLBACK_CHAIN] THEN MATCH_MP_TAC P2CG_MPULLBACK_PT THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC STDS_CYL_CQ_PULLBACK THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ; STDS_NC_MU_POS; ORTHOGONAL_MATRIX_TRANSP; STDS_ROT] THEN
      SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[STDS_ROT; STDS_NC_MU_POS; P3S_NC_NORM] THEN
      DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN
      ASM_SIMP_TAC[NORM_0; REAL_EXP_NZ; P3S_NC_NORM];
      ASM_SIMP_TAC[APX_MPULLBACK_CHAIN] THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `mpullback (\w:real^3. w) (H:real^3->real^3^3) z` THEN
      CONJ_TAC THENL [REWRITE_TAC[P2CE_MPULLBACK_ID]; ALL_TAC] THEN
      MATCH_MP_TAC P2CG_MPULLBACK_LOCAL THEN EXISTS_TAC `U:real^3->bool` THEN
      ASM_SIMP_TAC[o_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on (U:real^3->bool) (U':real^3->bool) (psi:real^3->real^3) phi` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[diffeomorphism_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U':real^3->bool`; `U:real^3->bool`; `psi:real^3->real^3`;
                 `phi:real^3->real^3`; `cylinder_flow t`;
                 `mpullback (phi:real^3->real^3) (H:real^3->real^3^3)`; `x:real^3`]
                LCK_DIST2_PULLBACK) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD];
    MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `psi:real^3->real^3`] THEN ASM_REWRITE_TAC[]]);;

let STDS_PARTIAL_RIEM = prove
 (`!g0 te (G:real->real^3->real^3^3) t.
     p3_partial_std g0 te G /\ &0 <= t /\ t < te
     ==> riemannian_metric (open_set_atlas (:real^3)) (G t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_partial_std; ricci_flow_from; ricci_flow_on] THEN
  STRIP_TAC THEN ASM_CASES_TAC `t = &0` THENL
   [ASM_MESON_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let STDS_ASYM_P4 = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) Tp eps.
     P2C_PROP_5_14_STATEMENT (:real^3) (:real^3) /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3) /\
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\ &0 <= Tp /\ Tp < te /\ Tp < &1 /\
     &0 < eps
     ==> ?A1. A0 <= A1 /\
              !t x. &0 <= t /\ t <= Tp /\ A1 < p3_std_dist g0 x
                    ==> lck_dist2 (rfs_kreg eps)
                          (mpullback (p3_std_nc g0 A0) (cylinder_flow t)) (G t) x < eps pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `te:real`; `G:real->real^3->real^3^3`;
                `Tp:real`; `{basis 1:real^3}`; `rfs_kreg eps`; `eps pow 2`] STDS_ASYM_CLOSE) THEN
  ASM_SIMP_TAC[COMPACT_SING; REAL_POW_LT; SING_SUBSET; IN_DELETE; IN_UNIV; STDS_BASIS1_NZ;
               IN_SING] THEN
  DISCH_THEN(X_CHOOSE_TAC `A2:real`) THEN
  EXISTS_TAC `max A2 (A0 + sqrt(&2) * (&0 + &1))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> a <= max b (a + c)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (:real^3) ((G:real->real^3->real^3^3) t)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_OPEN_RIEM_FIELD THEN REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC STDS_PARTIAL_RIEM THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `te:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`;
                `(G:real->real^3->real^3^3) t`; `t:real`; `rfs_kreg eps`] STDS_NMAP_TRANSFER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o SPECL [`x:real^3`; `t:real`; `basis 1:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The P3 form: far out the flow has eps-necks up to time t0.               *)

let STDS_FAR_MU_R = prove
 (`!g0 A0 (x:real^3) c.
     p3_std_initial g0 A0 /\ &0 <= c /\ A0 + sqrt(&2) * c <= p3_std_dist g0 x
     ==> ~(x = vec 0) /\ norm(p3_std_nc g0 A0 x) * exp c <= exp(&4 / sqrt(&2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0 /\ &0 < sqrt(&2)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[P3S_A0_POS; P3S_SQRT2_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&2) * c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(MATCH_MP P3S_DIST_0 (ASSUME `p3_std_initial g0 A0`)) THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[P3S_NC_NORM; GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[REAL_ARITH `a / s + b <= c / s <=> (a - c) / s + b <= &0`] THEN
  SUBGOAL_THEN `((A0 + &4 - p3_std_dist g0 x) - &4) / sqrt(&2) + c =
                ((A0 - p3_std_dist g0 x) + sqrt(&2) * c) / sqrt(&2)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC);;

let STDS_ASYM_P3 = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) t0 eps.
     P2C_PROP_5_14_STATEMENT (:real^3) (:real^3) /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3) /\
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\ &0 <= t0 /\ t0 < te /\ t0 < &1 /\
     &0 < eps
     ==> ?X. compact X /\
             !x. ~(x IN X)
                 ==> ?e. mfd_param euclidean (open_set_atlas (:real^3)) (rfs_neck_dom eps) e /\
                         x IN IMAGE e (sphere(vec 0,&1)) /\
                         rfs_close_fam (rfs_kreg eps) eps {s | &0 <= s /\ s <= t0}
                           (rfs_neck_dom eps) cylinder_flow
                           (\s y. rfs_pullback (open_set_atlas (:real^3)) e (G s) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[P3S_SQRT2_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom eps = annulus (exp(--c)) (exp c):real^3->bool` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[rfs_neck_dom]; ALL_TAC] THEN
  ABBREV_TAC `K0 = cball(vec 0:real^3,exp c) DIFF ball(vec 0,exp(--c))` THEN
  SUBGOAL_THEN `compact (K0:real^3->bool) /\ K0 SUBSET (:real^3) DELETE vec 0 /\
                annulus (exp(--c)) (exp c) SUBSET K0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
      MATCH_MP_TAC STDS_CANNULUS_SUBSET THEN REWRITE_TAC[REAL_EXP_POS_LT];
      REWRITE_TAC[annulus; SUBSET; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `te:real`; `G:real->real^3->real^3^3`;
                `t0:real`; `K0:real^3->bool`; `rfs_kreg eps`; `eps pow 2 / &2`]
               STDS_ASYM_CLOSE) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_ARITH `&0 < &2`] THEN
  DISCH_THEN(X_CHOOSE_TAC `A2:real`) THEN
  ABBREV_TAC `A1 = max (&0) (max A2 (A0 + sqrt(&2) * c))` THEN
  EXISTS_TAC `cball(vec 0:real^3,p3s_rad_rinv g0 A1)` THEN REWRITE_TAC[COMPACT_CBALL] THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_CBALL_0; REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `A1 < p3_std_dist g0 (x:real^3)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A1:real`; `x:real^3`]
           P2CN_DIST_COMPARE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "A1" THEN REAL_ARITH_TAC;
                    ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `c:real`] STDS_FAR_MU_R) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN EXPAND_TAC "A1" THEN UNDISCH_TAC `A1 < p3_std_dist g0 x` THEN
    EXPAND_TAC "A1" THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `exp(--c)`; `exp c`]
         STDS_NMAP_DIFFEO) THEN
  ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  EXISTS_TAC `stds_nmap g0 A0 (x:real^3)` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_param; MFD_DIFFEO_EUCLIDEAN] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `basis 1:real^3` THEN
    ASM_SIMP_TAC[STDS_NMAP_E1; IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
    REWRITE_TAC[rfs_close_fam; STDS_RFS_PULLBACK_UNIV; ETA_AX; IN_ELIM_THM] THEN
    EXISTS_TAC `eps pow 2 / &2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x / &2 < x`) THEN ASM_SIMP_TAC[REAL_POW_LT];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o SPECL [`x:real^3`; `s:real`; `y:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `A1 < p3_std_dist g0 x` THEN EXPAND_TAC "A1" THEN REAL_ARITH_TAC;
      ASM SET_TAC[]]]);;


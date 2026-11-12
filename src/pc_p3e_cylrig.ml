(* ========================================================================= *)
(* Unit pc_p3e_cylrig (for MT Prop 15.2): the round cylinder flow is affine  *)
(* in time, cyl(s) = cyl(0) - 2 s Ric_cyl, with a Ricci tensor that does not *)
(* depend on time; rescaled pullbacks of the family keep this form with the  *)
(* Ricci tensor of the pulled back metric (rigidity without a classification *)
(* of isometries); shifting the base of lck_dist2 between cylinder bases;    *)
(* sequences of metrics close to cylinders converge in the near calculus of  *)
(* pc_p2c_flconv (p2cm_mnear); the Ricci tensor and Lap R + 2|Ric|^2 along   *)
(* such sequences, and positivity of the latter near cylinders.              *)
(* ========================================================================= *)

needs "src/pc_lrg_stab.ml";;
needs "src/pc_lrg_lap.ml";;
needs "src/pc_p2c_flconv.ml";;
needs "src/pc_p3_s14jet.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The cylinder flow is affine in time with slope -2 Ric, and                *)
(* its Ricci tensor does not depend on time (RFB_CYL_RICCI).  Pullbacks by a *)
(* diffeomorphism and rescalings keep the affine form, with the Ricci       *)
(* matrix of the pulled back metric (LRICCI_PULLBACK, LRICCI_SCALE).         *)
(* ------------------------------------------------------------------------- *)

let P3E_CYL_RICMAT = prove
 (`!s (y:real^3).
     s < &1 /\ ~(y = vec 0)
     ==> ((lambda i j. lricci (cylinder_flow s) y (basis i) (basis j)):real^3^3) =
         (lambda i j. lricci (cylinder_flow (&0)) y (basis i) (basis j))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RFB_CYL_RICCI; REAL_ARITH `&0 < &1`]);;

let P3E_CYL_AFFINE = prove
 (`!s (y:real^3).
     ~(y = vec 0)
     ==> cylinder_flow s y =
         cylinder_flow (&0) y -
         (&2 * s) %% (lambda i j. lricci (cylinder_flow (&0)) y (basis i) (basis j))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RFB_CYL_RICCI; REAL_ARITH `&0 < &1`] THEN
  SUBGOAL_THEN `~(norm(y:real^3) pow 2 = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_EQ_0; NORM_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  REWRITE_TAC[cylinder_flow; CART_EQ] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA; MATRIX_SUB_COMPONENT; MATRIX_ADD_COMPONENT;
               MATRIX_CMUL_COMPONENT; MAT_COMPONENT; DOT_BASIS; BASIS_COMPONENT] THEN
  REPEAT COND_CASES_TAC THEN TRY(ASM_MESON_TAC[]) THEN
  UNDISCH_TAC `~(norm(y:real^3) pow 2 = &0)` THEN CONV_TAC REAL_FIELD);;

let P3E_CYL_SHIFT_AFFINE = prove
 (`!a b (y:real^3).
     ~(y = vec 0)
     ==> cylinder_flow (a + b) y =
         cylinder_flow a y -
         (&2 * b) %% (lambda i j. lricci (cylinder_flow (&0)) y (basis i) (basis j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a + b:real`; `y:real^3`] P3E_CYL_AFFINE) THEN
  MP_TAC(SPECL [`a:real`; `y:real^3`] P3E_CYL_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[CART_EQ; MATRIX_SUB_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN CONV_TAC REAL_RING);;

let P3E_MPULLBACK_RICMAT = prove
 (`!U U' (h:real^N->real^N) h' G z.
     metric_field U G /\ diffeomorphism_on U' U h h' /\ z IN U'
     ==> mpullback h (\w. (lambda i j. lricci G w (basis i) (basis j)):real^N^N) z =
         (lambda i j. lricci (mpullback h G) z (basis i) (basis j))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFB_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `z:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U' (mpullback (h:real^N->real^N) G)` ASSUME_TAC THENL
   [ASM_MESON_TAC[METRIC_FIELD_PULLBACK]; ALL_TAC] THEN
  REWRITE_TAC[mpullback] THEN BETA_TAC THEN ASM_SIMP_TAC[RFB_CONGRUENCE_DOT] THEN
  MP_TAC(ISPECL [`U':real^N->bool`; `mpullback (h:real^N->real^N) G`; `z:real^N`;
                 `u:real^N`; `v:real^N`] LRG_LRICCI_DOT_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(h:real^N->real^N) z`;
                 `frechet_derivative (h:real^N->real^N) (at z) u`;
                 `frechet_derivative (h:real^N->real^N) (at z) v`] LRG_LRICCI_DOT_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G:real^N->real^N^N`; `z:real^N`;
                 `u:real^N`; `v:real^N`] LRICCI_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let P3E_CYL_PULLBACK_AFFINE = prove
 (`!U U' (h:real^3->real^3) h' sig z.
     U SUBSET (:real^3) DELETE vec 0 /\ diffeomorphism_on U' U h h' /\ z IN U'
     ==> mpullback h (cylinder_flow sig) z =
         mpullback h (cylinder_flow (&0)) z -
         (&2 * sig) %%
         (lambda i j. lricci (mpullback h (cylinder_flow (&0))) z (basis i) (basis j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U (cylinder_flow (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`] THEN
    ASM_MESON_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `U':real^3->bool`; `h:real^3->real^3`;
                 `h':real^3->real^3`; `cylinder_flow (&0)`; `z:real^3`]
         P3E_MPULLBACK_RICMAT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `U':real^3->bool`; `h:real^3->real^3`;
                 `h':real^3->real^3`; `z:real^3`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((h:real^3->real^3) z = vec 0)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mpullback] THEN BETA_TAC THEN
  MP_TAC(SPECL [`sig:real`; `(h:real^3->real^3) z`] P3E_CYL_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB; MATRIX_MUL_LMUL;
              MATRIX_MUL_RMUL]);;

let P3E_CYL_SCALED_PULLBACK_AFFINE = prove
 (`!U U' (h:real^3->real^3) h' c sig z.
     U SUBSET (:real^3) DELETE vec 0 /\ diffeomorphism_on U' U h h' /\ z IN U' /\
     &0 < c
     ==> c %% mpullback h (cylinder_flow sig) z =
         c %% mpullback h (cylinder_flow (&0)) z -
         (&2 * c * sig) %%
         (lambda i j. lricci (\w. c %% mpullback h (cylinder_flow (&0)) w) z
                             (basis i) (basis j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U (cylinder_flow (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`] THEN
    ASM_MESON_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U' (mpullback (h:real^3->real^3) (cylinder_flow (&0)))`
  ASSUME_TAC THENL [ASM_MESON_TAC[METRIC_FIELD_PULLBACK]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `U':real^3->bool`; `h:real^3->real^3`;
                 `h':real^3->real^3`; `sig:real`; `z:real^3`]
         P3E_CYL_PULLBACK_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U':real^3->bool`; `mpullback (h:real^3->real^3) (cylinder_flow (&0))`;
                 `c:real`; `z:real^3`] LRICCI_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[CART_EQ; MATRIX_SUB_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Shifting the base of lck_dist2 between cylinder metrics.                  *)
(* All cylinder_flow s share the Levi-Civita connection                      *)
(* (CHRISTOFFEL_CYLINDER_FLOW), so the covariant derivatives of G - cyl(b)   *)
(* are the same for the bases cyl(a) and cyl(b), and G - cyl(b) is the     *)
(* difference of the shifted metric G + cyl(a) - cyl(b) and cyl(a); only     *)
(* the norms change, by the factor max 1 ((1 - b) / (1 - a)) per slot.       *)
(* ------------------------------------------------------------------------- *)

let P3E_CYL_COMPARE2 = prove
 (`!a b (y:real^3) x.
     a < &1 /\ b < &1 /\ ~(y = vec 0)
     ==> x dot (cylinder_flow b y ** x) <=
         max (&1) ((&1 - b) / (&1 - a)) * (x dot (cylinder_flow a y ** x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LRG_CYL_FLOW_DOT] THEN
  MP_TAC(ISPEC `y:real^3` LRG_CYL_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((x:real^3) dot y) pow 2 <= norm(y:real^3) pow 2 * (x dot x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_ABS_MUL; REAL_ABS_NORM] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS];
    ALL_TAC] THEN
  ABBREV_TAC `r = norm(y:real^3) pow 2` THEN
  ABBREV_TAC `X = (x:real^3) dot x` THEN
  ABBREV_TAC `t = ((x:real^3) dot y) pow 2 / r` THEN
  SUBGOAL_THEN `&0 <= t /\ t <= X` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_POW_2; REAL_LT_IMP_LE;
                                     REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. (&1 - s) * X * (&2 / r) +
        s / &2 * (&2 / r * (&2 / r * (((x:real^3) dot y) * (x dot y)))) =
        (&2 / r) * (t + (&1 - s) * (X - t))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "t" THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `lam = max (&1) ((&1 - b) / (&1 - a))` THEN
  SUBGOAL_THEN `&1 <= lam /\ (&1 - b) / (&1 - a) <= lam` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - b <= lam * (&1 - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - b) / (&1 - a) * (&1 - a)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t <= lam * t` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - b) * (X - t) <= (lam * (&1 - a)) * (X - t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 / r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `q * (t + (&1 - b) * (X - t)) <= q * (lam * (t + (&1 - a) * (X - t)))
    ==> q * (t + (&1 - b) * (X - t)) <= lam * (q * (t + (&1 - a) * (X - t)))`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `t <= lam * t /\ (&1 - b) * (X - t) <= (lam * (&1 - a)) * (X - t)
    ==> t + (&1 - b) * (X - t) <= lam * (t + (&1 - a) * (X - t))`) THEN
  ASM_REWRITE_TAC[]);;

let P3E_LCK_CYL_SHIFT = prove
 (`!k a b t (G:real^3->real^3^3) y.
     a < &1 /\ b < &1 /\ t SUBSET ((:real^3) DELETE vec 0) /\
     metric_field t G /\ y IN t
     ==> lck_dist2 k (cylinder_flow a)
           (\z. G z + cylinder_flow a z - cylinder_flow b z) y
         <= max (&1) ((&1 - b) / (&1 - a)) pow (k + 2) *
            lck_dist2 k (cylinder_flow b) G y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(t:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field t (cylinder_flow a) /\ metric_field t (cylinder_flow b)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD];
    ALL_TAC] THEN
  ABBREV_TAC `lam = max (&1) ((&1 - b) / (&1 - a))` THEN
  SUBGOAL_THEN `&1 <= lam` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z u. lmetric2 (\z. (G:real^3->real^3^3) z + cylinder_flow a z -
                         cylinder_flow b z) z u -
           lmetric2 (cylinder_flow a) z u) =
    (\z u. lmetric2 G z u - lmetric2 (cylinder_flow b) z u)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; lmetric2; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
                MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_RADD; DOT_RSUB] THEN
    REPEAT GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[lck_dist2] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow b`; `G:real^3->real^3^3`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `t:real^3->bool`; `cylinder_flow b`;
                 `\z u. lmetric2 (G:real^3->real^3^3) z u -
                        lmetric2 (cylinder_flow b) z u`]
         LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "FS") THEN
  MP_TAC(ISPECL [`2`; `cylinder_flow a`; `cylinder_flow b`;
                 `\z u. lmetric2 (G:real^3->real^3^3) z u -
                        lmetric2 (cylinder_flow b) z u`;
                 `(:real^3) DELETE vec 0`] LRG_LNABLA_ITER_CHRISTOFFEL_EQ) THEN
  ANTS_TAC THENL
   [SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`a:real`; `z:real^3`; `a':real^3`; `b':real^3`]
           CHRISTOFFEL_CYLINDER_FLOW) THEN
    MP_TAC(SPECL [`b:real`; `z:real^3`; `a':real^3`; `b':real^3`]
           CHRISTOFFEL_CYLINDER_FLOW) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC;
    DISCH_THEN(LABEL_TAC "EQ")] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `ltnorm2 (2 + l) (cylinder_flow a)
                (lnabla_iter 2 l (cylinder_flow b)
                  (\z u. lmetric2 (G:real^3->real^3^3) z u -
                         lmetric2 (cylinder_flow b) z u)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
    REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "EQ" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_DELETE; IN_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lam pow (2 + l) *
              ltnorm2 (2 + l) (cylinder_flow b)
                (lnabla_iter 2 l (cylinder_flow b)
                  (\z u. lmetric2 (G:real^3->real^3^3) z u -
                         lmetric2 (cylinder_flow b) z u)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_COMPARE THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(USE_THEN "FS" (fun th -> REWRITE_TAC[th]) THEN NO_TAC) THEN
    TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    EXPAND_TAC "lam" THEN GEN_TAC THEN MATCH_MP_TAC P3E_CYL_COMPARE2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "FS" (fun th -> REWRITE_TAC[th])]);;

let P3E_LCK_DIST2_POS = prove
 (`!s (G0:real^N->real^N^N) G k y.
     metric_field s G0 /\ metric_field s G /\ y IN s ==> &0 <= lck_dist2 k G0 G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lck_dist2] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* From lck_dist2 closeness to convergence in the near                       *)
(* calculus.  P3E_LCK_SEQ_PARTIALS: if lck_dist2 m G0 (Hs n) tends to 0     *)
(* uniformly on a compact K and the Hs n are eventually metric fields, all  *)
(* iterated partials of order at most m converge uniformly on K (by         *)
(* contradiction, P3S_NORMALIZED_JET along a subsequence with rate 1/(j+1)). *)
(* P3E_LCK_MNEAR: closeness of every order on a closed ball gives           *)
(* p2cm_mnear at its centre.                                                *)
(* ------------------------------------------------------------------------- *)

let P3E_LCK_SEQ_PARTIALS = prove
 (`!V K (G0:real^N->real^N^N) (Hs:num->real^N->real^N^N) m.
     metric_field V G0 /\ compact K /\ K SUBSET V /\
     (?N. !n. N <= n ==> metric_field V (Hs n)) /\
     (!e. &0 < e ==> ?N. !n y. N <= n /\ y IN K ==> lck_dist2 m G0 (Hs n) y < e)
     ==> !l. l IN pde_index_lists m (:N)
             ==> !e. &0 < e
                     ==> ?N. !n y. N <= n /\ y IN K
                                   ==> norm(iterated_partial l
                                              ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                               Hs n) y -
                                            iterated_partial l (vectorize o G0) y) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `N0:num`)
                                                 (LABEL_TAC "CV"))))) THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:num->num` (X_CHOOSE_THEN `yy:num->real^N`
    (LABEL_TAC "BAD"))) THEN
  SUBGOAL_THEN
   `?M:num->num. !j n:num y. M j <= n /\ y IN K
                ==> lck_dist2 m (G0:real^N->real^N^N) ((Hs:num->real^N->real^N^N) n) y <
                    inv(&j + &1) pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `j:num` THEN
    USE_THEN "CV" MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `K:real^N->bool`; `G0:real^N->real^N^N`;
                 `\j. (Hs:num->real^N->real^N^N) (nn(N0 + (M:num->num) j + j))`;
                 `m:num`] P3S_NORMALIZED_JET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `j:num` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      USE_THEN "BAD" (MP_TAC o SPEC `N0 + (M:num->num) j + j`) THEN ARITH_TAC;
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "BAD" (MP_TAC o SPEC `N0 + (M:num->num) j + j`) THEN ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "NJ"))] THEN
  SUBGOAL_THEN `?j. C * inv(&j + &1) < e` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `C / e` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN EXISTS_TAC `j:num` THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &j + &1`] THEN
    UNDISCH_TAC `C / e <= &j` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "NJ" (MP_TAC o SPECL [`j:num`; `l:num list`;
                                 `(yy:num->real^N) (N0 + (M:num->num) j + j)`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "BAD" (MP_TAC o SPEC `N0 + (M:num->num) j + j`) THEN SIMP_TAC[]];
    DISCH_TAC] THEN
  USE_THEN "BAD" (STRIP_ASSUME_TAC o SPEC `N0 + (M:num->num) j + j`) THEN
  ASM_REAL_ARITH_TAC);;

let P3E_LCK_MNEAR = prove
 (`!V (G0:real^N->real^N^N) (Hs:num->real^N->real^N^N) z0 r.
     metric_field V G0 /\ &0 < r /\ cball(z0,r) SUBSET V /\
     (?N. !n. N <= n ==> metric_field V (Hs n)) /\
     (!m e. &0 < e
            ==> ?N. !n y. N <= n /\ y IN cball(z0,r) ==> lck_dist2 m G0 (Hs n) y < e)
     ==> p2cm_mnear z0 Hs G0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `N0:num`)
                                                 (LABEL_TAC "CV"))))) THEN
  SUBGOAL_THEN `ball(z0:real^N,r) SUBSET V` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(z0:real^N,r)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  REWRITE_TAC[p2cm_mnear] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`r:real`; `N0:num`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; X_GEN_TAC `n:num` THEN DISCH_TAC] THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC P2CI_NEAR_OF_PARTIALS THEN EXISTS_TAC `r:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `N0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_MESON_TAC[metric_field];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `cball(z0:real^N,r)`; `G0:real^N->real^N^N`;
                 `Hs:num->real^N->real^N^N`; `LENGTH(l:num list)`]
         P3E_LCK_SEQ_PARTIALS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CBALL] THEN REPEAT CONJ_TAC THEN
    TRY(EXISTS_TAC `N0:num` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN USE_THEN "CV" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Curvature along p2cm_mnear sequences.  Products of                        *)
(* near-convergent real sequences; the Ricci matrix entries (P2CM_NEAR_EVAL *)
(* with the jet polynomial p2ch_xric), the inverse metric entries, the      *)
(* scalar curvature and its Laplacian converge in the near calculus;        *)
(* evaluation at points converging to the centre.                           *)
(* ------------------------------------------------------------------------- *)

let P3E_NEAR_MUL = prove
 (`!(z0:real^M) (f:num->real^M->real) g (f0:real^M->real) g0.
     p2ci_near z0 (\n z. lift(f n z)) (\z. lift(f0 z)) /\
     p2ci_near z0 (\n z. lift(g n z)) (\z. lift(g0 z))
     ==> p2ci_near z0 (\n z. lift(f n z * g n z)) (\z. lift(f0 z * g0 z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(a:real^1) (v:real^1). drop a % v`; `z0:real^M`;
                 `\n z. lift((f:num->real^M->real) n z)`; `\z. lift((f0:real^M->real) z)`;
                 `\n z. lift((g:num->real^M->real) n z)`; `\z. lift((g0:real^M->real) z)`]
         P2CI_NEAR_BILINEAR2) THEN
  ASM_REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP; GSYM LIFT_CMUL]);;

let P3E_NEAR_SUB = prove
 (`!(z0:real^M) (f:num->real^M->real) g (f0:real^M->real) g0.
     p2ci_near z0 (\n z. lift(f n z)) (\z. lift(f0 z)) /\
     p2ci_near z0 (\n z. lift(g n z)) (\z. lift(g0 z))
     ==> p2ci_near z0 (\n z. lift(f n z - g n z)) (\z. lift(f0 z - g0 z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_SUB; VECTOR_SUB] THEN
  MATCH_MP_TAC P2CI_NEAR_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CI_NEAR_NEG THEN ASM_REWRITE_TAC[]);;

let P3E_MNEAR_LRICCI = prove
 (`!(z0:real^N) As A0 a b.
     p2cm_mnear z0 As A0 /\ 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
     ==> p2ci_near z0 (\n z. lift(lricci (As n) z (basis a) (basis b)))
                      (\z. lift(lricci A0 z (basis a) (basis b)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cm_mnear]) THEN
  MP_TAC(ISPECL [`As:num->real^N->real^N^N`; `A0:real^N->real^N^N`; `z0:real^N`]
         P2CM_NEAR_EVAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CM_MNEAR_INVERTIBLE THEN
    EXISTS_TAC `As:num->real^N->real^N^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `p2ch_xric (dimindex(:N)) a b`) THEN
  ASM_SIMP_TAC[P2CH_OK_XRIC] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2CI_NEAR_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`\n z. lift(p2ch_eval (\s:real. (As:num->real^N->real^N^N) n)
                          (p2ch_xric (dimindex(:N)) a b) (&0) z)`;
    `\z. lift(p2ch_eval (\s:real. (A0:real^N->real^N^N))
                        (p2ch_xric (dimindex(:N)) a b) (&0) z)`;
    `r:real`; `N:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THENL
   [MP_TAC(ISPECL [`ball(z0:real^N,r)`; `\s:real. (As:num->real^N->real^N^N) n`;
                   `&0`; `z:real^N`; `a:num`; `b:num`] P2CH_EVAL_XRIC);
    MP_TAC(ISPECL [`ball(z0:real^N,r)`; `\s:real. (A0:real^N->real^N^N)`;
                   `&0`; `z:real^N`; `a:num`; `b:num`] P2CH_EVAL_XRIC)] THEN
  ASM_SIMP_TAC[]);;

let P3E_MNEAR_INV_ENTRY = prove
 (`!(z0:real^N) As A0 i j.
     p2cm_mnear z0 As A0 /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> p2ci_near z0 (\n z. lift(matrix_inv(As n z)$i$j))
                      (\z. lift(matrix_inv(A0 z)$i$j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cm_mnear]) THEN
  MP_TAC(ISPECL [`z0:real^N`; `\n z. matrix_inv((As:num->real^N->real^N^N) n z)`;
                 `\z. matrix_inv((A0:real^N->real^N^N) z)`]
         P2CI_NEAR_MATRIX) THEN
  MP_TAC(ISPECL [`As:num->real^N->real^N^N`; `A0:real^N->real^N^N`; `z0:real^N`]
         P2CM_NEAR_INV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CM_MNEAR_INVERTIBLE THEN
    EXISTS_TAC `As:num->real^N->real^N^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[]);;

let P3E_MNEAR_LSCALAR = prove
 (`!(z0:real^N) As A0.
     p2cm_mnear z0 As A0
     ==> p2ci_near z0 (\n z. lift(lscalar (As n) z)) (\z. lift(lscalar A0 z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lscalar; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC P2CI_NEAR_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC P2CI_NEAR_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC P3E_NEAR_MUL THEN
  ASM_SIMP_TAC[P3E_MNEAR_INV_ENTRY; P3E_MNEAR_LRICCI]);;

let P3E_MNEAR_LLAP_SCALAR = prove
 (`!(z0:real^N) As A0.
     p2cm_mnear z0 As A0
     ==> p2ci_near z0 (\n z. lift(llap (As n) (lscalar (As n)) z))
                      (\z. lift(llap A0 (lscalar A0) z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:N)
        ==> p2ci_near z0
              (\n. partial_derivative k (\w. lift(lscalar ((As:num->real^N->real^N^N) n) w)))
              (partial_derivative k (\w. lift(lscalar (A0:real^N->real^N^N) w)))`
  (LABEL_TAC "D1") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`z0:real^N`; `\n w. lift(lscalar ((As:num->real^N->real^N^N) n) w)`;
                   `\w. lift(lscalar (A0:real^N->real^N^N) w)`; `k:num`]
           P2CI_NEAR_PARTIAL) THEN
    ASM_SIMP_TAC[P3E_MNEAR_LSCALAR];
    ALL_TAC] THEN
  REWRITE_TAC[llap; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC P2CI_NEAR_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC P2CI_NEAR_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC P3E_NEAR_MUL THEN ASM_SIMP_TAC[P3E_MNEAR_INV_ENTRY] THEN
  MATCH_MP_TAC P3E_NEAR_SUB THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_DROP; GSYM partial_derivative; ETA_AX] THEN
    MP_TAC(ISPECL [`z0:real^N`;
                   `\n. partial_derivative j
                          (\w. lift(lscalar ((As:num->real^N->real^N^N) n) w))`;
                   `partial_derivative j (\w. lift(lscalar (A0:real^N->real^N^N) w))`;
                   `i:num`] P2CI_NEAR_PARTIAL) THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC P2CI_NEAR_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC P3E_NEAR_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CM_MNEAR_CHRIST THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_DROP; GSYM partial_derivative; ETA_AX] THEN
    USE_THEN "D1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P3E_NEAR_SEQ_POINT = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f yy.
     p2ci_near z0 Fs f /\ (yy --> z0) sequentially
     ==> ((\n. Fs n (yy n)) --> f z0) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ci_near] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "UC"))))))
    (LABEL_TAC "YY")) THEN
  SUBGOAL_THEN `(f:real^M->real^N) continuous at z0` MP_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real^N`; `ball(z0:real^M,r)`]
           CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(LABEL_TAC "CT") THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "CT" (MP_TAC o SPEC `e / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  USE_THEN "UC" (MP_TAC o SPEC `e / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  USE_THEN "YY" (MP_TAC o SPEC `min d r` o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "N2" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `(yy:num->real^M) n IN ball(z0,r)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "N1" (MP_TAC o SPECL [`n:num`; `(yy:num->real^M) n`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "D" (MP_TAC o SPEC `(yy:num->real^M) n`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `dist((f:real^M->real^N) ((yy:num->real^M) n),f z0) < e / &2` THEN
  UNDISCH_TAC `norm((Fs:num->real^M->real^N) n (yy n) - f (yy n)) < e / &2` THEN
  REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH);;

let P3E_CYL_LAP_SCALAR = prove
 (`!xi (y:real^3).
     xi < &1 /\ ~(y = vec 0)
     ==> llap (cylinder_flow xi) (lscalar (cylinder_flow xi)) y = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!z:real^3. ~(z = vec 0)
               ==> frechet_derivative (\w. lift(lscalar (cylinder_flow xi) w)) (at z) =
                   (\h. vec 0)`
  (LABEL_TAC "D1") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\w:real^3. lift(&1 / (&1 - xi))`; `norm(z:real^3)`] THEN
    ASM_REWRITE_TAC[NORM_POS_LT; HAS_DERIVATIVE_CONST] THEN
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RFB_CYL_SCALAR THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `dist(vec 0:real^3,z) < norm z` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. frechet_derivative
          (\z. frechet_derivative (\w. lift(lscalar (cylinder_flow xi) w)) (at z)
                                  (basis j))
          (at y) = (\h. vec 0:real^1)`
  (LABEL_TAC "D2") THENL
   [X_GEN_TAC `j:num` THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\w:real^3. vec 0:real^1`; `norm(y:real^3)`] THEN
    ASM_REWRITE_TAC[NORM_POS_LT; HAS_DERIVATIVE_CONST] THEN
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(w:real^3 = vec 0)` (fun th -> USE_THEN "D1" (MP_TAC o C MATCH_MP th))
    THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `dist(vec 0:real^3,y) < norm y` THEN CONV_TAC NORM_ARITH;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[llap] THEN USE_THEN "D2" (fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; SUM_0; REAL_SUB_REFL]);;

let P3E_MNEAR_CYL_EVOL_POS = prove
 (`!xi (z0:real^3) As yy.
     xi < &1 /\ ~(z0 = vec 0) /\ p2cm_mnear z0 As (cylinder_flow xi) /\
     (yy --> z0) sequentially
     ==> ?N. !n. N <= n
                 ==> &0 < llap (As n) (lscalar (As n)) (yy n) +
                          &2 * ltnorm2 2 (As n) (lric2 (As n)) (yy n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 / (&1 - xi)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`z0:real^3`; `\n z. lift(lscalar ((As:num->real^3->real^3^3) n) z)`;
                 `\z. lift(lscalar (cylinder_flow xi) z)`; `yy:num->real^3`]
         P3E_NEAR_SEQ_POINT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[P3E_MNEAR_LSCALAR]; ALL_TAC] THEN
  ASM_SIMP_TAC[RFB_CYL_SCALAR] THEN REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `(&1 / (&1 - xi)) / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  MP_TAC(ISPECL [`z0:real^3`;
                 `\n z. lift(llap ((As:num->real^3->real^3^3) n) (lscalar (As n)) z)`;
                 `\z. lift(llap (cylinder_flow xi) (lscalar (cylinder_flow xi)) z)`;
                 `yy:num->real^3`] P3E_NEAR_SEQ_POINT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[P3E_MNEAR_LLAP_SCALAR]; ALL_TAC] THEN
  ASM_SIMP_TAC[P3E_CYL_LAP_SCALAR] THEN REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `(&1 / (&1 - xi)) pow 2 / &4`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_ARITH `&0 < &4`] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2cm_mnear]) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `N3:num` STRIP_ASSUME_TAC)) (K ALL_TAC)) THEN
  UNDISCH_TAC `((yy:num->real^3) --> z0) sequentially` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N4:num` (LABEL_TAC "N4")) THEN
  EXISTS_TAC `N1 + N2 + N3 + N4:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "N1" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "N2" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "N4" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `metric_field (ball(z0:real^3,r)) ((As:num->real^3->real^3^3) n)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(z0:real^3,r)`; `(As:num->real^3->real^3^3) n`;
                 `(yy:num->real^3) n`] RFA_RIC_SCALAR_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN
  ABBREV_TAC `c = &1 / (&1 - xi)` THEN
  ABBREV_TAC `R = lscalar ((As:num->real^3->real^3^3) n) (yy n)` THEN
  ABBREV_TAC `L = llap ((As:num->real^3->real^3^3) n) (lscalar (As n)) (yy n)` THEN
  ABBREV_TAC `X = ltnorm2 2 ((As:num->real^3->real^3^3) n) (lric2 (As n)) (yy n)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(&3 * c / &4) pow 2 < R pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
    UNDISCH_TAC `abs(R - c) < c / &4` THEN UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `abs(L - &0) < c pow 2 / &4` THEN
  UNDISCH_TAC `(&3 * c / &4) pow 2 < R pow 2` THEN
  UNDISCH_TAC `R pow 2 <= &3 * X` THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Sequences of cylinder metrics and metrics close to                        *)
(* cylinders.  The cylinder flow is an affine combination of cyl(0) and     *)
(* cyl(1/2); constant sequences and the cylinder family converge in the     *)
(* near calculus; shifted metrics G + cyl(a) - cyl(b) are metric fields     *)
(* when G is C^0 close to cyl(b); P3E_NECK_SEQ_MNEAR: metrics with          *)
(* lck_dist2 (ks n) (cyl(ss n)) (Gs n) <= ds n, ks n -> infinity, ds n -> 0 *)
(* and ss n -> s < 1 on sets eventually containing a closed ball converge  *)
(* to cyl(s) near its centre (base shift to cyl(0), P3E_LCK_MNEAR).        *)
(* ------------------------------------------------------------------------- *)

let P3E_CYL_COMBO = prove
 (`!s (y:real^3).
     cylinder_flow s y =
     (&1 - &2 * s) %% cylinder_flow (&0) y + (&2 * s) %% cylinder_flow (&1 / &2) y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cylinder_flow; CART_EQ; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING);;

let P3E_NEAR_CONSTSEQ = prove
 (`!(z0:real^M) (k:num->real^N) k0.
     (k --> k0) sequentially ==> p2ci_near z0 (\n z. k n) (\z. k0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CI_NEAR_OF_PARTIALS THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; SMOOTH_MAP_ON_CONST] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[P2CT_ITERATED_PARTIAL_CONST] THEN COND_CASES_TAC THENL
   [UNDISCH_TAC `((k:num->real^N) --> k0) sequentially` THEN
    REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0]]);;

let P3E_CYL_SEQ_NEAR = prove
 (`!(z0:real^3) ss s.
     ~(z0 = vec 0) /\ ((\n. lift(ss n)) --> lift s) sequentially
     ==> p2ci_near z0 (\n. vectorize o cylinder_flow (ss n))
                      (vectorize o cylinder_flow s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(z0:real^3,r) SUBSET (:real^3) DELETE vec 0`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `norm(z0:real^3)` THEN ASM_REWRITE_TAC[NORM_POS_LT] THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_DELETE; IN_UNIV] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `dist(z0:real^3,vec 0) < norm z0` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (ball(z0:real^3,r))
      ((vectorize:real^3^3->real^(3,3)finite_prod) o cylinder_flow (&0)) /\
    smooth_map_on (ball(z0:real^3,r))
      ((vectorize:real^3^3->real^(3,3)finite_prod) o cylinder_flow (&1 / &2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `&0` RFB_CYL_METRIC_FIELD) THEN
    MP_TAC(SPEC `&1 / &2` RFB_CYL_METRIC_FIELD) THEN
    REWRITE_TAC[metric_field] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. (vectorize:real^3^3->real^(3,3)finite_prod) o cylinder_flow t =
        (\z. drop(lift(&1 - &2 * t)) % (vectorize o cylinder_flow (&0)) z +
             drop(lift(&2 * t)) % (vectorize o cylinder_flow (&1 / &2)) z)`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP] THEN
    GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [P3E_CYL_COMBO] THEN
    REWRITE_TAC[VECTORIZE_ADD; VECTORIZE_CMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC P2CI_NEAR_ADD THEN CONJ_TAC THEN
  MP_TAC(ISPECL [`\(a:real^1) (v:real^(3,3)finite_prod). drop a % v`; `z0:real^3`]
         P2CI_NEAR_BILINEAR2) THEN
  REWRITE_TAC[BILINEAR_DROP_MUL] THEN DISCH_THEN MATCH_MP_TAC THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC P3E_NEAR_CONSTSEQ THEN
     REWRITE_TAC[LIFT_SUB; LIFT_CMUL; LIFT_NUM] THEN
     TRY(MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST]) THEN
     MATCH_MP_TAC LIM_CMUL THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `r:real` THEN
     ASM_REWRITE_TAC[ETA_AX]]));;

let P3E_CYL_SEQ_MNEAR = prove
 (`!(z0:real^3) ss s.
     ~(z0 = vec 0) /\ s < &1 /\ ((\n. lift(ss n)) --> lift s) sequentially
     ==> p2cm_mnear z0 (\n. cylinder_flow (ss n)) (cylinder_flow s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2cm_mnear] THEN
  ASM_SIMP_TAC[P3E_CYL_SEQ_NEAR] THEN
  UNDISCH_TAC `((\n. lift(ss n)) --> lift s) sequentially` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 - s`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N:num`)] THEN
  MAP_EVERY EXISTS_TAC [`norm(z0:real^3)`; `N:num`] THEN
  SUBGOAL_THEN `ball(z0:real^3,norm z0) SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; IN_DELETE; IN_UNIV] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `dist(z0:real^3,vec 0) < norm z0` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[NORM_POS_LT] THEN CONJ_TAC THENL
   [ALL_TAC; X_GEN_TAC `n:num` THEN DISCH_TAC] THEN
  MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN
  TRY(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[]) THEN
  ASM_REAL_ARITH_TAC);;

let P3E_SHIFT_METRIC_FIELD = prove
 (`!U (G:real^3->real^3^3) a b.
     a < &1 /\ b < &1 /\ U SUBSET (:real^3) DELETE vec 0 /\ metric_field U G /\
     (!y. y IN U
          ==> max (&1) ((&1 - b) / (&1 - a)) *
              sqrt(lck_dist2 0 (cylinder_flow b) G y) < &1)
     ==> metric_field U (\z. G z + cylinder_flow a z - cylinder_flow b z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U (cylinder_flow a) /\ metric_field U (cylinder_flow b)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD];
    ALL_TAC] THEN
  REWRITE_TAC[metric_field] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ASSUME `metric_field U (G:real^3->real^3^3)`) THEN
    MP_TAC(ASSUME `metric_field U (cylinder_flow a)`) THEN
    MP_TAC(ASSUME `metric_field U (cylinder_flow b)`) THEN
    REWRITE_TAC[metric_field; o_DEF; VECTORIZE_ADD; VECTORIZE_SUB] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[TRANSP_MATRIX_ADD; TRANSP_MATRIX_SUB] THEN ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
              DOT_RADD; DOT_RSUB] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `U:real^3->bool`; `cylinder_flow b`; `G:real^3->real^3^3`;
                 `y:real^3`; `v:real^3`] LCK_DIST_C0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `y:real^3`; `v:real^3`] P3E_CYL_COMPARE2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < v dot (cylinder_flow a y ** v)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `lam = max (&1) ((&1 - b) / (&1 - a))` THEN
  ABBREV_TAC `sl = sqrt(lck_dist2 0 (cylinder_flow b) (G:real^3->real^3^3) y)` THEN
  ABBREV_TAC `q = v dot (cylinder_flow a y ** v)` THEN
  ABBREV_TAC `p = v dot (cylinder_flow b y ** v)` THEN
  ABBREV_TAC `g = v dot ((G:real^3->real^3^3) y ** v)` THEN
  SUBGOAL_THEN `&0 <= sl` ASSUME_TAC THENL
   [EXPAND_TAC "sl" THEN MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[lck_dist2] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sl * p <= sl * (lam * q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(lam * sl) * q < &1 * q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `abs(g - p) <= sl * p` THEN
  UNDISCH_TAC `sl * p <= sl * (lam * q)` THEN
  UNDISCH_TAC `(lam * sl) * q < &1 * q` THEN
  REAL_ARITH_TAC);;

let P3E_NECK_SEQ_MNEAR = prove
 (`!(Gs:num->real^3->real^3^3) Vs ss s ks ds (z0:real^3) r.
     s < &1 /\ &0 < r /\ cball(z0,r) SUBSET (:real^3) DELETE vec 0 /\
     ((\n. lift(ss n)) --> lift s) sequentially /\
     (!m. ?N. !n. N <= n ==> m <= ks n) /\
     ((\n. lift(ds n)) --> vec 0) sequentially /\
     (?N. !n. N <= n
              ==> ss n < &1 /\ cball(z0,r) SUBSET Vs n /\ metric_field (Vs n) (Gs n) /\
                  (!y. y IN Vs n
                       ==> lck_dist2 (ks n) (cylinder_flow (ss n)) (Gs n) y <= ds n))
     ==> p2cm_mnear z0 Gs (cylinder_flow s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "SS")
    (CONJUNCTS_THEN2 (LABEL_TAC "KS") (CONJUNCTS_THEN2 (LABEL_TAC "DS")
      (X_CHOOSE_THEN `N0:num` (LABEL_TAC "EV")))))))) THEN
  SUBGOAL_THEN `~(z0:real^3 = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `cball(z0:real^3,r) SUBSET (:real^3) DELETE vec 0` THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN DISCH_THEN(MP_TAC o SPEC `z0:real^3`) THEN
    ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(z0:real^3,r) SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(z0:real^3,r)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(z0:real^3,r / &2) SUBSET ball(z0,r)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t < &1 ==> metric_field (ball(z0:real^3,r)) (cylinder_flow t)`
  (LABEL_TAC "MCY") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n:num. N0 <= n
            ==> (ss:num->real) n < &1 /\
                metric_field (ball(z0:real^3,r)) ((Gs:num->real^3->real^3^3) n) /\
                metric_field (ball(z0:real^3,r)) (cylinder_flow (ss n)) /\
                (!y. y IN ball(z0,r)
                     ==> lck_dist2 ((ks:num->num) n) (cylinder_flow (ss n)) (Gs n) y <=
                         (ds:num->real) n)`
  (LABEL_TAC "EB") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "EV" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(Vs:num->real^3->bool) n` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS];
      USE_THEN "MCY" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]];
    ALL_TAC] THEN
  ABBREV_TAC `B = &2 + abs s` THEN
  SUBGOAL_THEN `&1 <= B` ASSUME_TAC THENL [EXPAND_TAC "B" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `?N1:num. !n:num. N1 <= n ==> max (&1) ((&1 - (ss:num->real) n) / (&1 - &0)) <= B`
  (X_CHOOSE_THEN `N1:num` (LABEL_TAC "LAM")) THENL
   [USE_THEN "SS" (MP_TAC o SPEC `&1` o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
    REWRITE_TAC[REAL_LT_01; DIST_LIFT] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1] THEN
    EXPAND_TAC "B" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n:num y. N0 <= n /\ y IN ball(z0:real^3,r)
              ==> &0 <= lck_dist2 0 (cylinder_flow ((ss:num->real) n))
                                    ((Gs:num->real^3->real^3^3) n) y /\
                  lck_dist2 0 (cylinder_flow (ss n)) (Gs n) y <= (ds:num->real) n`
  (LABEL_TAC "L0") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "EB" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3E_LCK_DIST2_POS THEN EXISTS_TAC `ball(z0:real^3,r)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lck_dist2 ((ks:num->num) n) (cylinder_flow ((ss:num->real) n))
                            ((Gs:num->real^3->real^3^3) n) (y:real^3)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `ball(z0:real^3,r)` THEN
        ASM_REWRITE_TAC[LE_0];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m e. &0 < e
          ==> ?N:num. !n:num y. N <= n /\ y IN ball(z0:real^3,r)
                        ==> lck_dist2 m (cylinder_flow (&0))
                              (\z. (Gs:num->real^3->real^3^3) n z + cylinder_flow (&0) z -
                                   cylinder_flow ((ss:num->real) n) z) y < e`
  (LABEL_TAC "SH") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "KS" (X_CHOOSE_TAC `N2:num` o SPEC `m:num`) THEN
    SUBGOAL_THEN `&0 < B pow (m + 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "DS" (MP_TAC o SPEC `e / B pow (m + 2)` o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
    ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DIST_0; NORM_LIFT] THEN DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
    EXISTS_TAC `N0 + N1 + N2 + N3:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "EB" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`m:num`; `&0`; `(ss:num->real) n`; `ball(z0:real^3,r)`;
                   `(Gs:num->real^3->real^3^3) n`; `y:real^3`] P3E_LCK_CYL_SHIFT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b < c ==> a <= b ==> a < c`) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `B pow (m + 2) * (ds:num->real) n` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; USE_THEN "LAM" MATCH_MP_TAC THEN ASM_ARITH_TAC];
        MATCH_MP_TAC P3E_LCK_DIST2_POS THEN EXISTS_TAC `ball(z0:real^3,r)` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `lck_dist2 ((ks:num->num) n) (cylinder_flow ((ss:num->real) n))
                              ((Gs:num->real^3->real^3^3) n) (y:real^3)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `ball(z0:real^3,r)` THEN
          ASM_REWRITE_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
      SUBGOAL_THEN `B pow (m + 2) * ds(n:num) <= B pow (m + 2) * abs(ds n)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `abs(ds(n:num)) < e / B pow (m + 2)` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?N:num. !n:num. N <= n
            ==> metric_field (ball(z0:real^3,r))
                  (\z. (Gs:num->real^3->real^3^3) n z + cylinder_flow (&0) z -
                       cylinder_flow ((ss:num->real) n) z)`
  (X_CHOOSE_THEN `N4:num` (LABEL_TAC "MH")) THENL
   [SUBGOAL_THEN `&0 < inv(B pow 2)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "DS" (MP_TAC o SPEC `inv(B pow 2)` o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
    ASM_REWRITE_TAC[DIST_0; NORM_LIFT] THEN DISCH_THEN(X_CHOOSE_TAC `N5:num`) THEN
    EXISTS_TAC `N0 + N1 + N5:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "EB" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    MATCH_MP_TAC P3E_SHIFT_METRIC_FIELD THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "L0" (MP_TAC o SPECL [`n:num`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `&0 <= ds(n:num)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(ds(n:num)) < inv B` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_INV] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `B * sqrt(ds(n:num))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC; USE_THEN "LAM" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `B * sqrt(ds(n:num)) < B * inv B` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `B * inv B = &1` (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(z0:real^3,r)`; `cylinder_flow (&0)`;
                 `\n z. (Gs:num->real^3->real^3^3) n z + cylinder_flow (&0) z -
                        cylinder_flow ((ss:num->real) n) z`; `z0:real^3`; `r / &2`]
         P3E_LCK_MNEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_HALF] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "MCY" MATCH_MP_TAC THEN REAL_ARITH_TAC;
      EXISTS_TAC `N4:num` THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`m:num`; `e:real`] THEN DISCH_TAC THEN
      USE_THEN "SH" (MP_TAC o SPECL [`m:num`; `e:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p2cm_mnear] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`r:real`; `N0:num`] THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "EB" (MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2CI_NEAR_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`\n z. ((vectorize:real^3^3->real^(3,3)finite_prod)
              ((Gs:num->real^3->real^3^3) n z + cylinder_flow (&0) z -
               cylinder_flow ((ss:num->real) n) z) +
            --(vectorize(cylinder_flow (&0) z))) +
           vectorize(cylinder_flow (ss n) z)`;
    `\z. ((vectorize:real^3^3->real^(3,3)finite_prod) (cylinder_flow (&0) z) +
          --(vectorize(cylinder_flow (&0) z))) +
         vectorize(cylinder_flow s z)`;
    `r:real`; `0`] THEN
  ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[VECTORIZE_ADD; VECTORIZE_SUB] THEN VECTOR_ARITH_TAC;
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC] THEN
  MATCH_MP_TAC P2CI_NEAR_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CI_NEAR_ADD THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
         can (find_term (fun t -> t = `p2ci_near:real^3->(num->real^3->real^(3,3)finite_prod)->(real^3->real^(3,3)finite_prod)->bool`)) (concl th))) THEN
      REWRITE_TAC[o_DEF];
      MATCH_MP_TAC P2CI_NEAR_NEG THEN MATCH_MP_TAC P2CI_NEAR_CONST THEN
      EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "MCY" (MP_TAC o SPEC `&0`) THEN REWRITE_TAC[REAL_LT_01] THEN
      SIMP_TAC[metric_field; o_DEF]];
    MP_TAC(ISPECL [`z0:real^3`; `ss:num->real`; `s:real`] P3E_CYL_SEQ_NEAR) THEN
    ASM_REWRITE_TAC[o_DEF]]);;


(* ========================================================================= *)
(* Unit pc_cmp_index (comparison-geometry layer CMP): the index inequality   *)
(* along a unit-speed minimizing geodesic, and S6 (MT Claim 3.24).  For a    *)
(* continuous field X along gamma on [0,d], smooth on the pieces of a        *)
(* partition and zero at the ends, the variation exp(s X(t)) has total      *)
(* energy E(s) >= d = E(0) (per piece 2 L_i <= w_i + E_i, and the triangle   *)
(* inequality), so by CMPV_PIECE_VARIATION the second variation              *)
(* sum_i int 2 (|D_t X_i|^2 - <X_i, R(X_i,T)T>) is >= 0 (CMPI_SECVAR_NONNEG).*)
(* Tent fields on a parallel orthonormal frame (parallel fields are smooth,  *)
(* CMPI_PARALLEL_SFIELD) then give CMP_RICCI_INTEGRAL:                       *)
(* |- !u n. CMP_RICCI_INTEGRAL_STATEMENT u n.  Jacobi's theorem, S5 and the  *)
(* no-corner lemma follow in pc_cmp_min.                                     *)
(* ========================================================================= *)

needs "src/pc_cmp_pull.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* Real-analysis helpers: a positive lower bound of finitely                 *)
(* many positive numbers, the second-derivative test at a local minimum,    *)
(* and 2 c int f <= c^2 (b - a) + int f^2.                                   *)
(* ========================================================================= *)

let CMPI_POS_MIN = prove
 (`!m (f:num->real). (!i. i < m ==> &0 < f i)
                     ==> ?d. &0 < d /\ !i. i < m ==> d <= f i`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[LT; REAL_LT_01];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f:num->real`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `i < m ==> i < SUC m`]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d ((f:num->real) m)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_MESON_TAC[ARITH_RULE `m < SUC m`];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[LT] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d:real` THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]);;

(* The second-derivative test. *)

let CMPI_LOCAL_MIN_DERIV = prove
 (`!E E1 E2 d.
        &0 < d /\
        (!s. abs s < d ==> E(&0) <= E s) /\
        (!s. abs s < d ==> (E has_real_derivative E1 s) (atreal s)) /\
        (E1 has_real_derivative E2) (atreal (&0))
        ==> E1(&0) = &0 /\ &0 <= E2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(E1:real->real)(&0) = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_ZERO_MAXMIN THEN
    MAP_EVERY EXISTS_TAC [`E:real->real`; `&0`; `real_interval(--d,d)`] THEN
    REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      DISJ2_TAC THEN X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `(E1 has_real_derivative E2) (atreal (&0))` THEN
  ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; REALLIM_ATREAL; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `--E2 / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!s. &0 < s /\ s < e ==> (E1:real->real) s < &0` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(E1:real->real) s / s < &0` MP_TAC THENL
     [MP_TAC(SPEC `(E1:real->real) s / s - E2` REAL_ABS_LE) THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  ABBREV_TAC `s0 = min e d / &2` THEN
  SUBGOAL_THEN `&0 < s0 /\ s0 < e /\ s0 < d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`E:real->real`; `E1:real->real`; `&0`; `s0:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `(E1:real->real) y` THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(E1:real->real) y < &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(E:real->real)(&0) <= E s0` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(E1:real->real) y * (s0 - &0) < &0` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < b * --a ==> a * b < &0`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* 2 c int f <= c^2 (b - a) + int f^2 on [a,b]. *)

let CMPI_SQ_INTEGRAL = prove
 (`!f a b c.
        a <= b /\ f real_integrable_on real_interval[a,b] /\
        (\t. f t pow 2) real_integrable_on real_interval[a,b]
        ==> &2 * c * real_integral (real_interval[a,b]) f <=
            c pow 2 * (b - a) + real_integral (real_interval[a,b]) (\t. f t pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t:real. (&2 * c) * (f:real->real) t) real_integrable_on real_interval[a,b]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\t:real. c pow 2 - (&2 * c) * (f:real->real) t) real_integrable_on
    real_interval[a,b]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= real_integral (real_interval[a,b])
            (\t. (c pow 2 - (&2 * c) * (f:real->real) t) + f t pow 2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_POS THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(SPEC `c - (f:real->real) t` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_ADD; REAL_INTEGRAL_SUB; REAL_INTEGRAL_CONST;
               REAL_INTEGRABLE_CONST] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; ETA_AX] THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Curve helpers: C^1 curves join their endpoints, distance                  *)
(* along a chain of joinable points, the within-interval velocity of a       *)
(* family slice is the two-sided one, and 2 L <= (b - a) + E on a piece.     *)
(* ========================================================================= *)

let CMPI_C1_JOINABLE = prove
 (`!top atlas (gamma:real->A) a b.
        mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b
        ==> mfd_joinable (top,atlas) (gamma a) (gamma b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_joinable] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_AFFINE_CURVE) THEN
  EXISTS_TAC `(gamma:real->A) o (\x. a + (b - a) * x)` THEN ASM_REWRITE_TAC[]);;

let CMPI_DIST_CHAIN = prove
 (`!top atlas (g:A->real^N^N) m (p:num->A).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        p 0 IN topspace top /\
        (!i. 1 <= i /\ i <= m ==> mfd_joinable (top,atlas) (p(i - 1)) (p i))
        ==> mfd_joinable (top,atlas) (p 0) (p m) /\
            mfd_dist (top,atlas) g (p 0) (p m) <=
            sum(1..m) (\i. mfd_dist (top,atlas) g (p(i - 1)) (p i))`,
  REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[MFD_JOINABLE_REFL; SUM_CLAUSES_NUMSEG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MFD_DIST_REFL; REAL_LE_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:num->A`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                  ((p:num->A) m) (p(SUC m))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `SUC m`) THEN
    REWRITE_TAC[ARITH_RULE `1 <= SUC m /\ SUC m <= SUC m`; SUC_SUB1];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC m`; SUC_SUB1] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^N^N) ((p:num->A) 0) (p m) +
              mfd_dist (top,atlas) g (p m) (p(SUC m))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* The within-[a,b] velocity of a family slice is the two-sided velocity. *)

let CMPI_SLICE_VELOCITY = prove
 (`!top atlas (f:real->real->A) S0 J r a b t.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        cmp_family (top,atlas) f S0 J /\ r IN S0 /\ a < b /\
        real_interval[a,b] SUBSET J /\ t IN real_interval[a,b]
        ==> mfd_velocity atlas (f r) a b t = mfd_vel atlas (f r) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_family]) THEN
  SUBGOAL_THEN `(t:real) IN J` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real->A) r t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPC_PAIR_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`S0:real->bool`; `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(f:real->real->A) r t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) r t)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `FST(c:(A->bool)#(A->real^N))`;
                 `\z. SND(c:(A->bool)#(A->real^N))
                        ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z)))`;
                 `r:real`] CMPC_LINE_T_SMOOTH) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. SND(c:(A->bool)#(A->real^N)) ((f:real->real->A) r (drop x)))
    differentiable at (lift t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{lift t | t IN J /\ (f:real->real->A) r t IN FST(c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_velocity; mfd_vel] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
  ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS]);;

(* On a piece of a family slice: C^1, and 2 L <= (b - a) + E. *)

let CMPI_PIECE_LENGTH = prove
 (`!top atlas (g:A->real^N^N) (f:real->real->A) S0 J r a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_family (top,atlas) f S0 J /\ r IN S0 /\ a <= b /\
        real_interval[a,b] SUBSET J
        ==> mfd_c1_curve (top,atlas) (f r) a b /\
            &2 * mfd_length atlas g (f r) a b <= (b - a) + cmp_energy atlas g (f r) a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) r) a b`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPC_LINE_T_C1 THEN
    MAP_EVERY EXISTS_TAC [`S0:real->bool`; `J:real->bool`] THEN
    ASM_MESON_TAC[cmp_family];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a:real = b` THENL
   [ASM_REWRITE_TAC[mfd_length; cmp_energy; REAL_INTEGRAL_REFL; REAL_SUB_REFL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[a,b]
        ==> mfd_speed atlas (g:A->real^N^N) ((f:real->real->A) r) a b t pow 2 =
            mfd_vel atlas (f r) t dot (g(f r t) ** mfd_vel atlas (f r) t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[mfd_speed] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:real->real->A`; `S0:real->bool`; `J:real->bool`; `r:real`;
                   `a:real`; `b:real`; `t:real`] CMPI_SLICE_VELOCITY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SQRT_POW_2 THEN
    SUBGOAL_THEN `(f:real->real->A) r t IN topspace top` ASSUME_TAC THENL
     [MATCH_MP_TAC CMPC_PAIR_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`S0:real->bool`; `J:real->bool`] THEN
      ASM_MESON_TAC[cmp_family; SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(f:real->real->A) r t`] GEOG_G_SYM_POS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_length; cmp_energy] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[a,b])
      (\t. mfd_vel atlas ((f:real->real->A) r) t dot
           ((g:A->real^N^N)(f r t) ** mfd_vel atlas (f r) t)) =
    real_integral (real_interval[a,b]) (\t. mfd_speed atlas g (f r) a b t pow 2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`mfd_speed atlas (g:A->real^N^N) ((f:real->real->A) r) a b`;
                 `a:real`; `b:real`; `&1`] CMPI_SQ_INTEGRAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC MFD_SPEED_CONTINUOUS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Piecewise fields along gamma on [0,d] and the energy of                  *)
(* their exponential variation: E(s) >= d = E(0).                            *)
(* ========================================================================= *)

(* A field along gamma on [0,d], given on the pieces [tp(i-1), tp i]        *)
(* (i = 1..m) by fields X i smooth along gamma on J, continuous at the      *)
(* break points and zero at both ends.                                      *)

let cmp_pwfield = new_definition
 `cmp_pwfield (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) (J:real->bool)
              m (tp:num->real) (X:num->real->real^N) d <=>
    1 <= m /\ tp 0 = &0 /\ tp m = d /\
    (!i. 1 <= i /\ i <= m ==> tp(i - 1) <= tp i /\ cmp_sfield atlas gamma J (X i)) /\
    (!i. 1 <= i /\ i < m ==> X i (tp i) = X (SUC i) (tp i)) /\
    X 1 (&0) = vec 0 /\ X m d = vec 0`;;

(* The second variation of energy of the exponential variation. *)

let cmp_secvar = new_definition
 `cmp_secvar (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (gamma:real->A)
             m (tp:num->real) (X:num->real->real^N) =
    sum(1..m) (\i. real_integral (real_interval[tp(i - 1),tp i])
                     (\t. &2 * cmp_idens atlas g gamma (X i) t))`;;

let CMPI_TP_MONO = prove
 (`!m (tp:num->real).
        (!i. 1 <= i /\ i <= m ==> tp(i - 1) <= tp i)
        ==> !i j. i <= j /\ j <= m ==> tp i <= tp j`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LE] THEN MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[LE] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(tp:num->real) j` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC j`) THEN REWRITE_TAC[SUC_SUB1] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CMPI_TELESCOPE = prove
 (`!m (tp:num->real). sum(1..m) (\i. tp i - tp(i - 1)) = tp m - tp 0`,
  GEN_TAC THEN GEN_TAC THEN SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC m`; SUC_SUB1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* The energy of the variation at s is at least d. *)

let CMPI_ENERGY_LOWER = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J d m (tp:num->real)
    (X:num->real->real^N) (dd:num->real) s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_geodesic (top,atlas) g gamma J /\
        mfd_dist (top,atlas) g (gamma(&0)) (gamma d) = d /\
        cmp_pwfield atlas gamma J m tp X d /\
        (!i. 1 <= i /\ i <= m
             ==> &0 < dd i /\ abs s < dd i /\
                 real_interval(tp(i - 1) - dd i,tp i + dd i) SUBSET J /\
                 cmp_family (top,atlas)
                   (\s t. mfd_exp (top,atlas) g (gamma t) (s % X i t))
                   (real_interval(--(dd i),dd i))
                   (real_interval(tp(i - 1) - dd i,tp i + dd i)) /\
                 (!t. t IN real_interval(tp(i - 1) - dd i,tp i + dd i)
                      ==> mfd_exp (top,atlas) g (gamma t) (&0 % X i t) = gamma t))
        ==> d <= sum(1..m) (\i. cmp_energy atlas g
                                  (\t. mfd_exp (top,atlas) g (gamma t) (s % X i t))
                                  (tp(i - 1)) (tp i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmp_pwfield] THEN
  DISCH_THEN(fun th -> EVERY (map2 LABEL_TAC
    ["h";"sm";"rm";"geo";"dist";"m1";"tp0";"tpm";"mono";"cont";"x1";"xm";"pc"]
    (CONJUNCTS th))) THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= m
        ==> mfd_c1_curve (top,atlas)
              (\t. mfd_exp (top,atlas) (g:A->real^N^N) ((gamma:real->A) t)
                     (s % (X:num->real->real^N) i t)) ((tp:num->real)(i - 1)) (tp i) /\
            &2 * mfd_length atlas g
                   (\t. mfd_exp (top,atlas) g (gamma t) (s % X i t)) (tp(i - 1)) (tp i) <=
            (tp i - tp(i - 1)) +
            cmp_energy atlas g (\t. mfd_exp (top,atlas) g (gamma t) (s % X i t))
              (tp(i - 1)) (tp i)`
  (LABEL_TAC "len") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "pc" (MP_TAC o C MP (CONJ (ASSUME `1 <= i`) (ASSUME `(i:num) <= m`)) o
                   SPEC `i:num`) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`;
                   `\s t. mfd_exp (top,atlas) (g:A->real^N^N) ((gamma:real->A) t)
                            (s % (X:num->real->real^N) i t)`;
                   `real_interval(--((dd:num->real) i),dd i)`;
                   `real_interval((tp:num->real)(i - 1) - (dd:num->real) i,tp i + dd i)`;
                   `s:real`; `(tp:num->real)(i - 1)`; `(tp:num->real) i`]
      CMPI_PIECE_LENGTH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_REAL_INTERVAL; SUBSET] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [USE_THEN "mono" (fun th -> ASM_MESON_TAC[th]); ALL_TAC] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `p = \j. if j = 0 then (gamma:real->A)(&0)
            else mfd_exp (top,atlas) (g:A->real^N^N) (gamma((tp:num->real) j))
                   (s % (X:num->real->real^N) j (tp j))` THEN
  SUBGOAL_THEN
   `mfd_exp (top,atlas) (g:A->real^N^N) ((gamma:real->A)(&0)) (vec 0) = gamma(&0) /\
    mfd_exp (top,atlas) g (gamma d) (vec 0) = gamma d`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "pc" (MP_TAC o C MP (CONJ (ARITH_RULE `1 <= 1`) (ASSUME `1 <= (m:num)`)) o
                     SPEC `1`) THEN
      CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `&0`) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN
      USE_THEN "mono" (MP_TAC o CONJUNCT1 o
        C MP (CONJ (ARITH_RULE `1 <= 1`) (ASSUME `1 <= (m:num)`)) o SPEC `1`) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < (dd:num->real) 1` THEN REAL_ARITH_TAC;
      USE_THEN "pc" (MP_TAC o C MP (CONJ (ASSUME `1 <= (m:num)`) (ARITH_RULE `(m:num) <= m`)) o
                     SPEC `m:num`) THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN
      USE_THEN "mono" (MP_TAC o CONJUNCT1 o
        C MP (CONJ (ASSUME `1 <= (m:num)`) (ARITH_RULE `(m:num) <= m`)) o
        SPEC `m:num`) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < (dd:num->real) m` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= m
        ==> mfd_exp (top,atlas) (g:A->real^N^N) ((gamma:real->A)((tp:num->real)(i - 1)))
              (s % (X:num->real->real^N) i (tp(i - 1))) = (p:num->A)(i - 1) /\
            mfd_exp (top,atlas) g (gamma(tp i)) (s % X i (tp i)) = p i`
  (LABEL_TAC "ends") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXPAND_TAC "p" THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i = 0)`] THEN
    ASM_CASES_TAC `i = 1` THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[VECTOR_MUL_RZERO];
      ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= i /\ ~(i = 1) ==> ~(i - 1 = 0)`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    USE_THEN "cont" (MP_TAC o SPEC `i - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> SUC(i - 1) = i`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&0:real) IN J` ASSUME_TAC THENL
   [USE_THEN "pc" (MP_TAC o C MP (CONJ (ARITH_RULE `1 <= 1`) (ASSUME `1 <= (m:num)`)) o
                   SPEC `1`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
                  check (is_binary "SUBSET" o concl)) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    USE_THEN "mono" (MP_TAC o CONJUNCT1 o
      C MP (CONJ (ARITH_RULE `1 <= 1`) (ASSUME `1 <= (m:num)`)) o SPEC `1`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < (dd:num->real) 1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `m:num`; `p:num->A`] CMPI_DIST_CHAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "p" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `J:real->bool`] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      USE_THEN "ends" (MP_TAC o C MP (CONJ (ASSUME `1 <= i`) (ASSUME `(i:num) <= m`)) o
                       SPEC `i:num`) THEN
      DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
      USE_THEN "len" (MP_TAC o CONJUNCT1 o
        C MP (CONJ (ASSUME `1 <= i`) (ASSUME `(i:num) <= m`)) o SPEC `i:num`) THEN
      DISCH_THEN(MP_TAC o MATCH_MP CMPI_C1_JOINABLE) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:num->A) 0 = (gamma:real->A)(&0) /\ p m = gamma d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= m ==> ~(m = 0)`; VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `d <= sum(1..m) (\i. mfd_length atlas (g:A->real^N^N)
                          (\t. mfd_exp (top,atlas) g ((gamma:real->A) t)
                                 (s % (X:num->real->real^N) i t))
                          ((tp:num->real)(i - 1)) (tp i))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..m) (\i. mfd_dist (top,atlas) (g:A->real^N^N)
                                 ((p:num->A)(i - 1)) (p i))` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    USE_THEN "ends" (MP_TAC o C MP (CONJ (ASSUME `1 <= i`) (ASSUME `(i:num) <= m`)) o
                     SPEC `i:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    USE_THEN "len" (ASSUME_TAC o CONJUNCT1 o
      C MP (CONJ (ASSUME `1 <= i`) (ASSUME `(i:num) <= m`)) o SPEC `i:num`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`;
                   `\t. mfd_exp (top,atlas) (g:A->real^N^N) ((gamma:real->A) t)
                          (s % (X:num->real->real^N) i t)`;
                   `(tp:num->real)(i - 1)`; `(tp:num->real) i`] MFD_DIST_LE_LENGTH) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * sum(1..m) (\i. mfd_length atlas (g:A->real^N^N)
                          (\t. mfd_exp (top,atlas) g ((gamma:real->A) t)
                                 (s % (X:num->real->real^N) i t))
                          ((tp:num->real)(i - 1)) (tp i)) <=
    d + sum(1..m) (\i. cmp_energy atlas g
                         (\t. mfd_exp (top,atlas) g (gamma t) (s % X i t))
                         (tp(i - 1)) (tp i))`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN
    SUBGOAL_THEN `d = sum(1..m) (\i. (tp:num->real) i - tp(i - 1))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[CMPI_TELESCOPE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "len" (MP_TAC o CONJUNCT2 o
      C MP (CONJ (ASSUME `1 <= i`) (ASSUME `(i:num) <= m`)) o SPEC `i:num`) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* The energy at s = 0 is d (gamma has unit speed). *)

let CMPI_ENERGY_ZERO = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J d m (tp:num->real)
    (X:num->real->real^N) (dd:num->real).
        (!t. t IN J
             ==> mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t) = &1) /\
        tp 0 = &0 /\ tp m = d /\ (!i. 1 <= i /\ i <= m ==> tp(i - 1) <= tp i) /\
        (!i. 1 <= i /\ i <= m
             ==> &0 < dd i /\ real_interval(tp(i - 1) - dd i,tp i + dd i) SUBSET J /\
                 (!t. t IN real_interval(tp(i - 1) - dd i,tp i + dd i)
                      ==> mfd_exp (top,atlas) g (gamma t) (&0 % X i t) = gamma t))
        ==> sum(1..m) (\i. cmp_energy atlas g
                             (\t. mfd_exp (top,atlas) g (gamma t) (&0 % X i t))
                             (tp(i - 1)) (tp i)) = d`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> EVERY (map2 LABEL_TAC
    ["unit";"tp0";"tpm";"mono";"pc"] (CONJUNCTS th))) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..m) (\i. (tp:num->real) i - tp(i - 1))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[CMPI_TELESCOPE] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[cmp_energy] THEN
  USE_THEN "pc" (MP_TAC o C MP (CONJ (ASSUME `1 <= i`) (ASSUME `(i:num) <= m`)) o
                 SPEC `i:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e0"))) THEN
  SUBGOAL_THEN `(tp:num->real)(i - 1) <= tp i` ASSUME_TAC THENL
   [USE_THEN "mono" (ACCEPT_TAC o C MP (CONJ (ASSUME `1 <= i`) (ASSUME `(i:num) <= m`)) o
                     SPEC `i:num`);
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[(tp:num->real)(i - 1),tp i]) (\t. &1)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!r. abs(r - t) < (dd:num->real) i
        ==> mfd_exp (top,atlas) (g:A->real^N^N) ((gamma:real->A) r)
              (&0 % (X:num->real->real^N) i r) = gamma r`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN USE_THEN "e0" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_vel atlas (\t. mfd_exp (top,atlas) (g:A->real^N^N) ((gamma:real->A) t)
                        (&0 % (X:num->real->real^N) i t)) t =
    mfd_vel atlas gamma t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC GEOM_VEL_LOCAL THEN EXISTS_TAC `(dd:num->real) i` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_exp (top,atlas) (g:A->real^N^N) ((gamma:real->A) t)
      (&0 % (X:num->real->real^N) i t) = gamma t`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "unit" MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
                check (is_binary "SUBSET" o concl)) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The index inequality.  Along a unit-speed minimizing                      *)
(* geodesic on [0,d], the second variation of energy of the exponential     *)
(* variation of a piecewise smooth field vanishing at the ends is >= 0.      *)
(* ========================================================================= *)

let CMPI_SECVAR_NONNEG = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J d m (tp:num->real)
    (X:num->real->real^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_geodesic (top,atlas) g gamma J /\
        (!t. t IN J
             ==> mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t) = &1) /\
        real_interval[&0,d] SUBSET J /\
        mfd_dist (top,atlas) g (gamma(&0)) (gamma d) = d /\
        cmp_pwfield atlas gamma J m tp X d
        ==> &0 <= cmp_secvar atlas g gamma m tp X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> EVERY (map2 LABEL_TAC
    ["m1";"tp0";"tpm";"mono";"cont";"x1";"xm"]
    (CONJUNCTS(GEN_REWRITE_RULE I [cmp_pwfield] th)))) THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= m
        ==> real_interval[(tp:num->real)(i - 1),tp i] SUBSET real_interval[&0,d]`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`m:num`; `tp:num->real`] CMPI_TP_MONO) THEN
    ANTS_TAC THENL [USE_THEN "mono" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(SPECL [`0`; `i - 1`] th) THEN
                         MP_TAC(SPECL [`i:num`; `m:num`] th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ?dd E1. 1 <= i /\ i <= m
                ==> &0 < dd /\
                    real_interval((tp:num->real)(i - 1) - dd,tp i + dd) SUBSET J /\
                    cmp_family (top,atlas)
                      (\s t. mfd_exp (top,atlas) (g:A->real^N^N) ((gamma:real->A) t)
                               (s % (X:num->real->real^N) i t))
                      (real_interval(--dd,dd)) (real_interval(tp(i - 1) - dd,tp i + dd)) /\
                    (!t. t IN real_interval(tp(i - 1) - dd,tp i + dd)
                         ==> mfd_exp (top,atlas) g (gamma t) (&0 % X i t) = gamma t) /\
                    (!s. s IN real_interval(--dd,dd)
                         ==> ((\r. cmp_energy atlas g
                                     (\t. mfd_exp (top,atlas) g (gamma t) (r % X i t))
                                     (tp(i - 1)) (tp i))
                              has_real_derivative E1 s) (atreal s)) /\
                    (E1 has_real_derivative
                     real_integral (real_interval[tp(i - 1),tp i])
                       (\t. &2 * cmp_idens atlas g gamma (X i) t)) (atreal (&0))`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `1 <= i /\ i <= m` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMPV_PIECE_VARIATION THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [USE_THEN "mono" (fun th -> ASM_MESON_TAC[th]); ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "mono" (fun th -> ASM_MESON_TAC[th]); ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval[&0,d]` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:num->real` (X_CHOOSE_THEN `E1:num->real->real`
    (LABEL_TAC "pv"))) THEN
  MP_TAC(ISPECL [`m:num`; `\i. (dd:num->real)(SUC i)`] CMPI_POS_MIN) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "pv" (MP_TAC o SPEC `SUC i`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= m ==> delta <= (dd:num->real) i` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> SUC(i - 1) = i`];
    ALL_TAC] THEN
  REWRITE_TAC[cmp_secvar] THEN
  MP_TAC(ISPECL
   [`\s. sum(1..m) (\i. cmp_energy atlas (g:A->real^N^N)
                          (\t. mfd_exp (top,atlas) g ((gamma:real->A) t)
                                 (s % (X:num->real->real^N) i t))
                          ((tp:num->real)(i - 1)) (tp i))`;
    `\s. sum(1..m) (\i. (E1:num->real->real) i s)`;
    `sum(1..m) (\i. real_integral (real_interval[(tp:num->real)(i - 1),tp i])
                      (\t. &2 * cmp_idens atlas (g:A->real^N^N) (gamma:real->A)
                                 ((X:num->real->real^N) i) t))`;
    `delta:real`] CMPI_LOCAL_MIN_DERIV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `d:real`; `m:num`;
                   `tp:num->real`; `X:num->real->real^N`; `dd:num->real`]
      CMPI_ENERGY_ZERO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "mono" (fun th -> MESON_TAC[th]);
        USE_THEN "pv" (fun th -> MESON_TAC[th])];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC CMPI_ENERGY_LOWER THEN
    MAP_EVERY EXISTS_TAC [`J:real->bool`; `dd:num->real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "pv" (MP_TAC o C MP (CONJ (ASSUME `1 <= i`) (ASSUME `(i:num) <= m`)) o
                   SPEC `i:num`) THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `delta:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "pv" (MP_TAC o C MP (CONJ (ASSUME `1 <= i`) (ASSUME `(i:num) <= m`)) o
                   SPEC `i:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
               CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    SUBGOAL_THEN `delta <= (dd:num->real) i` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  USE_THEN "pv" (MP_TAC o C MP (CONJ (ASSUME `1 <= i`) (ASSUME `(i:num) <= m`)) o
                 SPEC `i:num`) THEN
  SIMP_TAC[ETA_AX]);;


(* ========================================================================= *)
(* Parallel fields along a geodesic are smooth (cmp_sfield):                 *)
(* in a chart their representation solves the linear ODE                     *)
(* e' = -Gamma(y)(y', e) with smooth coefficients, and solutions of smooth   *)
(* linear ODEs are smooth (bootstrapping).                                    *)
(* ========================================================================= *)

let CMPI_LINEAR_ODE_SMOOTH = prove
 (`!s (M:real^1->real^N^N) (e:real^1->real^N).
        open s /\ smooth_map_on s ((vectorize:real^N^N->real^(N,N)finite_prod) o M) /\
        (!x. x IN s ==> (e has_vector_derivative (M x ** e x)) (at x))
        ==> smooth_map_on s e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    EXISTS_TAC `(M:real^1->real^N^N) x ** (e:real^1->real^N) x` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN
  EXISTS_TAC `\x:real^1 h:real^1. drop h % ((M:real^1->real^N^N) x ** (e:real^1->real^N) x)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[GSYM has_vector_derivative] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `h:real^1` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`n:num`; `s:real^1->bool`;
                 `\(m:real^(N,N)finite_prod) (v:real^N). (matrify m:real^N^N) ** v`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (M:real^1->real^N^N)`;
                 `e:real^1->real^N`] CONTINUOUSLY_DIFFERENTIABLE_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; o_THM; MATRIFY_VECTORIZE] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `smooth_map_on s ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                (M:real^1->real^N^N))` THEN
  SIMP_TAC[smooth_map_on]);;

(* Christoffel symbols along a smooth curve, against a smooth field, are     *)
(* smooth.                                                                    *)

let CMPI_CHRISTOFFEL_CURVE_SMOOTH = prove
 (`!U (G:real^N->real^N^N) (s:real^1->bool) (y:real^1->real^N) (u:real^1->real^N) w.
        metric_field U G /\ open s /\ smooth_map_on s y /\ smooth_map_on s u /\
        (!x. x IN s ==> y x IN U)
        ==> smooth_map_on s (\x. christoffel G (y x) (u x) w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open (U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\x. vsum(1..dimindex(:N))
                    (\k. drop(lift(((u:real^1->real^N) x)$k)) %
                         christoffel (G:real^N->real^N^N) ((y:real^1->real^N) x)
                           (basis k) (w:real^N))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    MP_TAC(ISPECL [`\a. christoffel (G:real^N->real^N^N) ((y:real^1->real^N) x) a
                          (w:real^N)`;
                   `1..dimindex(:N)`; `\k. ((u:real^1->real^N) x)$k`;
                   `basis:num->real^N`] LINEAR_VSUM_MUL) THEN
    REWRITE_TAC[FINITE_NUMSEG; BASIS_EXPANSION] THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(y:real^1->real^N) x`]
        LRG_CHRISTOFFEL_LINEAR) THEN
      ASM_SIMP_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^1->bool`; `u:real^1->real^N`; `\v:real^N. lift(v$k)`]
      SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT; o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. christoffel (G:real^N->real^N^N) ((y:real^1->real^N) x) (basis k) (w:real^N)) =
    (\z. christoffel G z (basis k) w) o y`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[LRG_CHRISTOFFEL_SMOOTH] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]);;

(* The vector derivative of a differentiable curve is its Frechet           *)
(* derivative at vec 1.                                                      *)

let CMPI_VD_FRECHET = prove
 (`!(f:real^1->real^N) x.
        f differentiable at x
        ==> vector_derivative f (at x) = frechet_derivative f (at x) (vec 1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [VECTOR_DERIVATIVE_WORKS]) THEN
  REWRITE_TAC[has_vector_derivative] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[DROP_VEC; VECTOR_MUL_LID]);;

(* Parallel fields along a geodesic are smooth. *)

let CMPI_PARALLEL_SFIELD = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Y:real->real^N).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ mfd_parallel atlas g gamma J Y
        ==> cmp_sfield atlas gamma J Y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmp_sfield] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `c:(A->bool)#(A->real^N)`] MFD_GEODESIC_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOL_GEODESIC_BASIC) THEN
  SUBGOAL_THEN
   `!a b. a <= b /\ real_interval[a,b] SUBSET J
          ==> mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) a b`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPG_GEODESIC_C1 THEN EXISTS_TAC `g:A->real^N^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                 (metric_local atlas c (g:A->real^N^N))`
  ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  ABBREV_TAC `S = {lift t | t IN J /\ (gamma:real->A) t IN FST(c:(A->bool)#(A->real^N))}` THEN
  ABBREV_TAC `y = \s:real^1. SND(c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))` THEN
  MATCH_MP_TAC CMPI_LINEAR_ODE_SMOOTH THEN
  EXISTS_TAC
   `\x. matrix(\w. --(christoffel (metric_local atlas (c:(A->bool)#(A->real^N))
                                    (g:A->real^N^N))
                        ((y:real^1->real^N) x) (frechet_derivative y (at x) (vec 1)) w))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[LRG_SMOOTH_VECTORIZE] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_COMPONENT] THEN
    MP_TAC(ISPECL [`S:real^1->bool`;
                   `\x. --(christoffel (metric_local atlas (c:(A->bool)#(A->real^N))
                                         (g:A->real^N^N))
                             ((y:real^1->real^N) x) (frechet_derivative y (at x) (vec 1))
                             (basis j))`;
                   `\v:real^N. lift(v$i)`] SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMPI_CHRISTOFFEL_CURVE_SMOOTH THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "S" THEN EXPAND_TAC "y" THEN
      REWRITE_TAC[FORALL_IN_GSPEC; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_parallel]) THEN
  SUBGOAL_THEN
   `(\s. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N)
           (c:(A->bool)#(A->real^N)) (drop s)) differentiable at (lift t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOJ_FIELD_DIFF_IMP_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^1->real^N) differentiable at (lift t)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `S:real^1->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `Y:real->real^N`;
                 `c:(A->bool)#(A->real^N)`; `t:real`] MFD_COVD_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `mfd_field_rep atlas (gamma:real->A) (mfd_covd atlas (g:A->real^N^N) gamma Y)
      (c:(A->bool)#(A->real^N)) t = vec 0`
  SUBST1_TAC THENL
   [REWRITE_TAC[mfd_field_rep] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(ISPEC `chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                   ((gamma:real->A) t)) (c:(A->bool)#(A->real^N))
                          ((gamma:real->A) t)` LINEAR_0) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(gamma:real->A) t`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)`;
                   `c:(A->bool)#(A->real^N)`] GEOL_CHART_TRANS_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `(gamma:real->A) t` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    DISCH_THEN(ACCEPT_TAC o MATCH_MP LRG_HAS_DERIVATIVE_IMP_LINEAR);
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP
    (VECTOR_ARITH `vec 0 = a + b ==> a:real^N = --b`)) THEN
  MP_TAC(GEN_REWRITE_RULE I [VECTOR_DERIVATIVE_WORKS]
   (ASSUME `(\s. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N)
                    (c:(A->bool)#(A->real^N)) (drop s)) differentiable at (lift t)`)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `frechet_derivative (y:real^1->real^N) (at (lift t)) (vec 1) =
                vector_derivative y (at (lift t))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMPI_VD_FRECHET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^1->real^N) (lift t) = SND(c:(A->bool)#(A->real^N)) ((gamma:real->A) t)`
  SUBST1_TAC THENL [EXPAND_TAC "y" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `linear (\w. --(christoffel (metric_local atlas (c:(A->bool)#(A->real^N))
                                   (g:A->real^N^N))
                       (SND c ((gamma:real->A) t))
                       (vector_derivative (y:real^1->real^N) (at (lift t))) w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE_NEG THEN
    MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                   `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                   `SND(c:(A->bool)#(A->real^N)) ((gamma:real->A) t)`]
      LRG_CHRISTOFFEL_LINEAR) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; ETA_AX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;


(* ========================================================================= *)
(* Affine multiples of parallel frame fields: smoothness and                 *)
(* index density b^2 - (a + b t)^2 R_jj.                                     *)
(* ========================================================================= *)

let CMPI_CHART_JAC_LINEAR = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) p.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ p IN topspace top /\
        p IN FST c
        ==> linear (chart_jac (chart_at atlas p) c p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)`;
                 `c:(A->bool)#(A->real^N)`] GEOL_CHART_TRANS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `p:A` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP LRG_HAS_DERIVATIVE_IMP_LINEAR));;

let CMPI_SFIELD_AFFINE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (X:real->real^N) a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_sfield atlas gamma J X
        ==> cmp_sfield atlas gamma J (\t. (a + b * t) % X t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cmp_sfield]) THEN
  DISCH_THEN(LABEL_TAC "sf") THEN
  REWRITE_TAC[cmp_sfield] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `c:(A->bool)#(A->real^N)`] MFD_GEODESIC_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\s. drop(lift(a + b * drop s)) %
                  mfd_field_rep atlas (gamma:real->A) (X:real->real^N)
                    (c:(A->bool)#(A->real^N)) (drop s)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC; LIFT_DROP] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REWRITE_TAC[mfd_field_rep] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LINEAR_CMUL THEN
    MATCH_MP_TAC CMPI_CHART_JAC_LINEAR THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_ADD; LIFT_CMUL; LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    USE_THEN "sf" (ACCEPT_TAC o C MP (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`) o
                   SPEC `c:(A->bool)#(A->real^N)`)]);;

(* The index density of (a + b t) Fr_j for a parallel orthonormal frame. *)

let CMPI_IDENS_FRAME = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Fr:num->real->real^N) j a b t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_pframe atlas g gamma J Fr /\
        1 <= j /\ j <= dimindex(:N) /\ t IN J
        ==> cmp_idens atlas g gamma (\t. (a + b * t) % Fr j t) t =
            b pow 2 - (a + b * t) pow 2 * cmp_rmat atlas g gamma Fr t$j$j`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_pframe]) THEN
  SUBGOAL_THEN `mfd_parallel atlas (g:A->real^N^N) (gamma:real->A) J
                  ((Fr:num->real->real^N) j)` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_parallel] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOL_GEODESIC_BASIC) THEN
  SUBGOAL_THEN
   `!a b. a <= b /\ real_interval[a,b] SUBSET J
          ==> mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) a b`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPG_GEODESIC_C1 THEN EXISTS_TAC `g:A->real^N^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
      (\t. (a + b * t) % (Fr:num->real->real^N) j t) t = b % Fr j t`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `(Fr:num->real->real^N) j`; `\t:real. a + b * t`; `b:real`; `t:real`]
      CMPG_COVD_SCALAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cmp_idens] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`]
    CMPF_RIEMANN_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`a + b * t`; `(Fr:num->real->real^N) j t`] o
             MATCH_MP LINEAR_CMUL) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN
   `(Fr:num->real->real^N) j t dot ((g:A->real^N^N)((gamma:real->A) t) ** Fr j t) = &1`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma:real->A`; `J:real->bool`; `Fr:num->real->real^N`;
                   `basis j:real^N`; `basis j:real^N`; `t:real`] CMPJ_FRAME_GRAM) THEN
    ASM_SIMP_TAC[CMPJ_FMAT_COLUMN; DOT_BASIS_BASIS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[cmp_rmat; LAMBDA_BETA] THEN REAL_ARITH_TAC);;

(* The diagonal curvature entries are continuous along gamma. *)

let CMPI_RMAT_REAL_CONTINUOUS = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Fr:num->real->real^N) i j.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_pframe atlas g gamma J Fr
        ==> (\t. cmp_rmat atlas g gamma Fr t$i$j) real_continuous_on J`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON; o_DEF] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `Fr:num->real->real^N`]
    GEOJ_RMAT_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* One piece of the index form of (a + b t) Fr_j. *)

let CMPI_PIECE_INTEGRAL = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Fr:num->real->real^N) j a b p q.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_pframe atlas g gamma J Fr /\
        1 <= j /\ j <= dimindex(:N) /\ p <= q /\ real_interval[p,q] SUBSET J
        ==> (\t. (a + b * t) pow 2 * cmp_rmat atlas g gamma Fr t$j$j)
            real_integrable_on real_interval[p,q] /\
            real_integral (real_interval[p,q])
              (\t. &2 * cmp_idens atlas g gamma (\t. (a + b * t) % Fr j t) t) =
            &2 * (b pow 2 * (q - p) -
                  real_integral (real_interval[p,q])
                    (\t. (a + b * t) pow 2 * cmp_rmat atlas g gamma Fr t$j$j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t. (a + b * t) pow 2 * cmp_rmat atlas (g:A->real^N^N) (gamma:real->A)
           (Fr:num->real->real^N) t$j$j) real_integrable_on real_interval[p,q]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `J:real->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMPI_RMAT_REAL_CONTINUOUS THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[p,q])
                (\t. &2 * (b pow 2 - (a + b * t) pow 2 *
                           cmp_rmat atlas (g:A->real^N^N) (gamma:real->A)
                             (Fr:num->real->real^N) t$j$j))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC CMPI_IDENS_FRAME THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\t. b pow 2 - (a + b * t) pow 2 *
                   cmp_rmat atlas (g:A->real^N^N) (gamma:real->A)
                     (Fr:num->real->real^N) t$j$j) real_integrable_on real_interval[p,q]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; REAL_INTEGRAL_SUB; REAL_INTEGRABLE_CONST;
               REAL_INTEGRAL_CONST]);;

let CMPI_SUM_THREE = prove
 (`!f. sum(1..3) f = f 1 + f 2 + f 3`,
  GEN_TAC THEN REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; SUM_CLAUSES_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* The index inequality for the tent field f Fr_j (f = t/r0, 1, (d-t)/r0). *)

let CMPI_TENT_ONE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J d (Fr:num->real->real^N) j r0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_geodesic (top,atlas) g gamma J /\
        (!t. t IN J
             ==> mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t) = &1) /\
        real_interval[&0,d] SUBSET J /\
        mfd_dist (top,atlas) g (gamma(&0)) (gamma d) = d /\
        cmp_pframe atlas g gamma J Fr /\ 1 <= j /\ j <= dimindex(:N) /\
        &0 < r0 /\ &2 * r0 <= d
        ==> real_integral (real_interval[&0,r0])
              (\t. (&0 + inv r0 * t) pow 2 * cmp_rmat atlas g gamma Fr t$j$j) +
            real_integral (real_interval[r0,d - r0])
              (\t. (&1 + &0 * t) pow 2 * cmp_rmat atlas g gamma Fr t$j$j) +
            real_integral (real_interval[d - r0,d])
              (\t. (d / r0 + --inv r0 * t) pow 2 * cmp_rmat atlas g gamma Fr t$j$j)
            <= &2 / r0`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `tp = \i. if i = 0 then &0 else if i = 1 then r0
                       else if i = 2 then d - r0 else d` THEN
  ABBREV_TAC `aa = \i. if i = 1 then &0 else if i = 2 then &1 else d / r0` THEN
  ABBREV_TAC `bb = \i. if i = 1 then inv r0 else if i = 2 then &0 else --inv r0` THEN
  SUBGOAL_THEN
   `(tp:num->real) 0 = &0 /\ tp 1 = r0 /\ tp 2 = d - r0 /\ tp 3 = d /\
    (aa:num->real) 1 = &0 /\ aa 2 = &1 /\ aa 3 = d / r0 /\
    (bb:num->real) 1 = inv r0 /\ bb 2 = &0 /\ bb 3 = --inv r0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tp"; "aa"; "bb"] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. 1 <= j /\ j <= dimindex(:N)
                    ==> mfd_parallel atlas (g:A->real^N^N) (gamma:real->A) J
                          ((Fr:num->real->real^N) j)`
  ASSUME_TAC THENL [ASM_MESON_TAC[cmp_pframe]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `d:real`; `3`;
                 `tp:num->real`;
                 `\i t. ((aa:num->real) i + (bb:num->real) i * t) %
                        (Fr:num->real->real^N) j t`] CMPI_SECVAR_NONNEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[cmp_pwfield] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN STRIP_TAC THEN CONJ_TAC THENL
       [SUBGOAL_THEN `i = 1 \/ i = 2 \/ i = 3` MP_TAC THENL
         [ASM_ARITH_TAC; STRIP_TAC] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[] THEN MATCH_MP_TAC CMPI_SFIELD_AFFINE THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`] THEN
        ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC CMPI_PARALLEL_SFIELD THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`] THEN
        ASM_SIMP_TAC[]];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN
      SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL
       [ASM_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < r0` THEN CONV_TAC REAL_FIELD;
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; VECTOR_MUL_LZERO];
      SUBGOAL_THEN `d / r0 + --inv r0 * d = &0` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < r0` THEN CONV_TAC REAL_FIELD;
        REWRITE_TAC[VECTOR_MUL_LZERO]]];
    ALL_TAC] THEN
  REWRITE_TAC[cmp_secvar; CMPI_SUM_THREE] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!p q. &0 <= p /\ p <= q /\ q <= d ==> real_interval[p,q] SUBSET J`
  (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `real_interval[&0,d]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun (a,b,p,q) ->
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `Fr:num->real->real^N`; `j:num`; a; b; p; q] CMPI_PIECE_INTEGRAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        USE_THEN "sub" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      DISCH_THEN(SUBST1_TAC o CONJUNCT2)])
   [(`&0`,`inv r0`,`&0`,`r0:real`);
    (`&1`,`&0`,`r0:real`,`d - r0`);
    (`d / r0`,`--inv r0`,`d - r0`,`d:real`)] THEN
  SUBGOAL_THEN `inv r0 pow 2 * (r0 - &0) = inv r0 /\
                (--inv r0) pow 2 * (d - (d - r0)) = inv r0 /\
                &0 pow 2 * (d - r0 - r0) = &0 /\ &2 / r0 = &2 * inv r0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN UNDISCH_TAC `&0 < r0` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Weighted integrals of Ric(T,T) as sums of the normal diagonal entries. *)

let CMPI_RICCI_SUM_INTEGRAL = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Fr:num->real->real^N) a b p q.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_pframe atlas g gamma J Fr /\
        (!t. t IN J ==> Fr 1 t = mfd_vel atlas gamma t) /\
        p <= q /\ real_interval[p,q] SUBSET J
        ==> real_integral (real_interval[p,q])
              (\t. (a + b * t) pow 2 *
                   mfd_ricci atlas g (gamma t) (mfd_vel atlas gamma t)
                     (mfd_vel atlas gamma t)) =
            sum(2..dimindex(:N))
              (\j. real_integral (real_interval[p,q])
                     (\t. (a + b * t) pow 2 * cmp_rmat atlas g gamma Fr t$j$j))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[p,q])
                (\t. sum(2..dimindex(:N))
                       (\j. (a + b * t) pow 2 *
                            cmp_rmat atlas (g:A->real^N^N) (gamma:real->A)
                              (Fr:num->real->real^N) t$j$j))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(t:real) IN J` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
     [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `J:real->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `Fr:num->real->real^N`; `t:real`] CMPJ_FRAME_RICCI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[trace] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; DIMINDEX_GE_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x + y = y`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `Fr:num->real->real^N`; `t:real`;
                   `&1`; `1`] CMPF_RMAT_TANGENT) THEN
    ASM_SIMP_TAC[VECTOR_MUL_LID; LE_REFL; DIMINDEX_GE_1];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\j t. (a + b * t) pow 2 *
                         cmp_rmat atlas (g:A->real^N^N) (gamma:real->A)
                           (Fr:num->real->real^N) t$j$j`;
                 `real_interval[p,q]`; `2..dimindex(:N)`] REAL_INTEGRAL_SUM) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `Fr:num->real->real^N`; `j:num`; `a:real`; `b:real`; `p:real`; `q:real`]
    CMPI_PIECE_INTEGRAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]]);;

(* Summing the tent inequality over the normal frame vectors. *)

let CMPI_TENT_RICCI = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J d (Fr:num->real->real^N) r0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_geodesic (top,atlas) g gamma J /\
        (!t. t IN J
             ==> mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t) = &1) /\
        real_interval[&0,d] SUBSET J /\
        mfd_dist (top,atlas) g (gamma(&0)) (gamma d) = d /\
        cmp_pframe atlas g gamma J Fr /\
        (!t. t IN J ==> Fr 1 t = mfd_vel atlas gamma t) /\
        &0 < r0 /\ &2 * r0 <= d
        ==> real_integral (real_interval[&0,r0])
              (\t. (&0 + inv r0 * t) pow 2 *
                   mfd_ricci atlas g (gamma t) (mfd_vel atlas gamma t)
                     (mfd_vel atlas gamma t)) +
            real_integral (real_interval[r0,d - r0])
              (\t. (&1 + &0 * t) pow 2 *
                   mfd_ricci atlas g (gamma t) (mfd_vel atlas gamma t)
                     (mfd_vel atlas gamma t)) +
            real_integral (real_interval[d - r0,d])
              (\t. (d / r0 + --inv r0 * t) pow 2 *
                   mfd_ricci atlas g (gamma t) (mfd_vel atlas gamma t)
                     (mfd_vel atlas gamma t))
            <= &2 * &(dimindex(:N) - 1) / r0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!p q. &0 <= p /\ p <= q /\ q <= d ==> real_interval[p,q] SUBSET J`
  (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `real_interval[&0,d]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun (a,b,p,q) ->
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `Fr:num->real->real^N`; a; b; p; q] CMPI_RICCI_SUM_INTEGRAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        USE_THEN "sub" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      DISCH_THEN SUBST1_TAC])
   [(`&0`,`inv r0`,`&0`,`r0:real`);
    (`&1`,`&0`,`r0:real`,`d - r0`);
    (`d / r0`,`--inv r0`,`d - r0`,`d:real`)] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(2..dimindex(:N)) (\j. &2 / r0)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC CMPI_TENT_ONE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG] THEN
    SIMP_TAC[ARITH_RULE `1 <= n ==> (n + 1) - 2 = n - 1`; DIMINDEX_GE_1] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* MT Claim 3.24 along a unit-speed minimizing geodesic: with                *)
(* Ric <= (n-1) K on the end balls of radius r0 <= d/2,                      *)
(* int_0^d Ric(T,T) <= 2(n-1)(2/3 K r0 + 1/r0).                               *)
(* ========================================================================= *)

(* Points of a unit-speed geodesic segment of length < r lie in the balls of *)
(* radius r around its ends.                                                  *)

let CMPI_GEO_POINT_BALL = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J a b r.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\
        (!t. t IN J
             ==> mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t) = &1) /\
        a <= b /\ real_interval[a,b] SUBSET J /\ b - a < r
        ==> gamma b IN mfd_ball (top,atlas) g (gamma a) r /\
            gamma a IN mfd_ball (top,atlas) g (gamma b) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `a:real`; `b:real`]
    MFD_GEODESIC_C1_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:real) IN J` ASSUME_TAC THENL
   [UNDISCH_TAC `real_interval[a,b] SUBSET J` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_length atlas (g:A->real^N^N) (gamma:real->A) a b = b - a`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[mfd_tnorm; SQRT_1; REAL_MUL_RID]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`]
    MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMPI_C1_JOINABLE) THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_DIST_SYM; REAL_LET_TRANS]);;

(* Ric(T,T) along gamma is continuous. *)

let CMPI_RICCI_CONTINUOUS = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Fr:num->real->real^N).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_pframe atlas g gamma J Fr
        ==> (\t. mfd_ricci atlas g (gamma t) (mfd_vel atlas gamma t)
                   (mfd_vel atlas gamma t)) real_continuous_on J`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\t. sum(1..dimindex(:N))
                    (\i. cmp_rmat atlas (g:A->real^N^N) (gamma:real->A)
                           (Fr:num->real->real^N) t$i$i)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[GSYM trace] THEN
    MATCH_MP_TAC CMPJ_FRAME_RICCI THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC CMPI_RMAT_REAL_CONTINUOUS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

(* The end weights 1 - f^2 of the tent have integral 2/3 r0. *)

let CMPI_END_WEIGHTS = prove
 (`!d r0. &0 < r0
          ==> real_integral (real_interval[&0,r0])
                (\t. &1 - (&0 + inv r0 * t) pow 2) = &2 / &3 * r0 /\
              real_integral (real_interval[d - r0,d])
                (\t. &1 - (d / r0 + --inv r0 * t) pow 2) = &2 / &3 * r0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THENL
   [MP_TAC(ISPECL [`\t. t - t pow 3 / (&3 * r0 pow 2)`;
                   `\t. &1 - (&0 + inv r0 * t) pow 2`; `&0`; `r0:real`]
      REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS);
    MP_TAC(ISPECL [`\t. t + (d - t) pow 3 / (&3 * r0 pow 2)`;
                   `\t. &1 - (d / r0 + --inv r0 * t) pow 2`; `d - r0`; `d:real`]
      REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS)] THEN
  (ANTS_TAC THENL
    [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     X_GEN_TAC `x:real` THEN DISCH_TAC THEN
     MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
     REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
     UNDISCH_TAC `&0 < r0` THEN CONV_TAC REAL_FIELD;
     ALL_TAC]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < r0` THEN CONV_TAC REAL_FIELD);;

(* Integrals against a nonnegative affine-square weight. *)

let CMPI_WEIGHT_BOUND = prove
 (`!(R1:real->real) a b p q c.
        p <= q /\ R1 real_continuous_on real_interval[p,q] /\
        (!t. t IN real_interval[p,q] ==> &0 <= &1 - (a + b * t) pow 2) /\
        (!t. t IN real_interval[p,q] /\ ~(&1 - (a + b * t) pow 2 = &0) ==> R1 t <= c)
        ==> real_integral (real_interval[p,q]) (\t. (&1 - (a + b * t) pow 2) * R1 t) <=
            real_integral (real_interval[p,q]) (\t. &1 - (a + b * t) pow 2) * c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\t. &1 - (a + b * t) pow 2) real_continuous_on real_interval[p,q]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\t. &1 - (a + b * t) pow 2) real_integrable_on real_interval[p,q]`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_INTEGRAL_RMUL] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC REAL_INTEGRABLE_RMUL THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `&1 - (a + b * t) pow 2 = &0` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[]]);;

(* MT Claim 3.24 for a unit-speed minimizing geodesic on [0,d]. *)

let CMPI_RICCI_UNIT = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J d (Fr:num->real->real^N) r0 K.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_geodesic (top,atlas) g gamma J /\
        (!t. t IN J
             ==> mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t) = &1) /\
        real_interval[&0,d] SUBSET J /\
        mfd_dist (top,atlas) g (gamma(&0)) (gamma d) = d /\
        cmp_pframe atlas g gamma J Fr /\
        (!t. t IN J ==> Fr 1 t = mfd_vel atlas gamma t) /\
        &0 < r0 /\ &2 * r0 <= d /\
        (!y w. y IN mfd_ball (top,atlas) g (gamma(&0)) r0 UNION
                    mfd_ball (top,atlas) g (gamma d) r0
               ==> mfd_ricci atlas g y w w <=
                   &(dimindex(:N) - 1) * K * (w dot (g y ** w)))
        ==> (\t. mfd_ricci atlas g (gamma t) (mfd_vel atlas gamma t)
                   (mfd_vel atlas gamma t)) real_integrable_on real_interval[&0,d] /\
            real_integral (real_interval[&0,d])
              (\t. mfd_ricci atlas g (gamma t) (mfd_vel atlas gamma t)
                     (mfd_vel atlas gamma t)) <=
            &2 * &(dimindex(:N) - 1) * (&2 / &3 * K * r0 + inv r0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "ric") THEN
  ABBREV_TAC `R1 = \t. mfd_ricci atlas (g:A->real^N^N) ((gamma:real->A) t)
                         (mfd_vel atlas gamma t) (mfd_vel atlas gamma t)` THEN
  SUBGOAL_THEN `(R1:real->real) real_continuous_on J` ASSUME_TAC THENL
   [EXPAND_TAC "R1" THEN MATCH_MP_TAC CMPI_RICCI_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `Fr:num->real->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p q. &0 <= p /\ p <= q /\ q <= d ==> real_interval[p,q] SUBSET J`
  (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `real_interval[&0,d]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q a b. &0 <= p /\ p <= q /\ q <= d
              ==> (R1:real->real) real_integrable_on real_interval[p,q] /\
                  (\t. (a + b * t) pow 2 * R1 t) real_integrable_on real_interval[p,q] /\
                  (\t. (&1 - (a + b * t) pow 2) * R1 t) real_integrable_on
                  real_interval[p,q]`
  (LABEL_TAC "int") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(R1:real->real) real_continuous_on real_interval[p,q]` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `J:real->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\t. a + b * t) real_continuous_on real_interval[p,q]` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[ETA_AX] THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "int" (MP_TAC o SPECL [`&0`; `d:real`; `&0`; `&0`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `c = &(dimindex(:N) - 1) * K` THEN
  SUBGOAL_THEN `!t. t IN J ==> mfd_vel atlas (gamma:real->A) t dot
                                ((g:A->real^N^N)(gamma t) ** mfd_vel atlas gamma t) = &1`
  (LABEL_TAC "unit") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t < r0 ==> (R1:real->real) t <= c`
  (LABEL_TAC "left") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "R1" THEN EXPAND_TAC "c" THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(t:real) IN J` ASSUME_TAC THENL
     [USE_THEN "sub" (MP_TAC o SPECL [`&0`; `d:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    USE_THEN "unit" (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
      [GSYM(MATCH_MP th (ASSUME `(t:real) IN J`))]) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN USE_THEN "ric" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `&0`; `t:real`;
                   `r0:real`] CMPI_GEO_POINT_BALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      TRY(USE_THEN "sub" MATCH_MP_TAC) THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. d - r0 < t /\ t <= d ==> (R1:real->real) t <= c`
  (LABEL_TAC "right") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "R1" THEN EXPAND_TAC "c" THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(t:real) IN J` ASSUME_TAC THENL
     [USE_THEN "sub" (MP_TAC o SPECL [`&0`; `d:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    USE_THEN "unit" (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
      [GSYM(MATCH_MP th (ASSUME `(t:real) IN J`))]) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN USE_THEN "ric" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `t:real`; `d:real`;
                   `r0:real`] CMPI_GEO_POINT_BALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      TRY(USE_THEN "sub" MATCH_MP_TAC) THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. mfd_ricci atlas (g:A->real^N^N) ((gamma:real->A) t) (mfd_vel atlas gamma t)
          (mfd_vel atlas gamma t) = (R1:real->real) t`
  (LABEL_TAC "r1") THENL [EXPAND_TAC "R1" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `d:real`;
                 `Fr:num->real->real^N`; `r0:real`] CMPI_TENT_RICCI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&0,d]) (R1:real->real) =
    real_integral (real_interval[&0,r0]) R1 +
    real_integral (real_interval[r0,d - r0]) R1 +
    real_integral (real_interval[d - r0,d]) R1`
  SUBST1_TAC THENL
   [USE_THEN "int" (MP_TAC o SPECL [`r0:real`; `d:real`; `&0`; `&0`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "int" (MP_TAC o SPECL [`&0`; `d:real`; `&0`; `&0`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`R1:real->real`; `&0`; `d:real`; `r0:real`] REAL_INTEGRAL_COMBINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`R1:real->real`; `r0:real`; `d:real`; `d - r0`] REAL_INTEGRAL_COMBINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[r0,d - r0]) (R1:real->real) =
    real_integral (real_interval[r0,d - r0]) (\t. (&1 + &0 * t) pow 2 * R1 t)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q a b. &0 <= p /\ p <= q /\ q <= d
              ==> real_integral (real_interval[p,q]) (R1:real->real) =
                  real_integral (real_interval[p,q]) (\t. (a + b * t) pow 2 * R1 t) +
                  real_integral (real_interval[p,q]) (\t. (&1 - (a + b * t) pow 2) * R1 t)`
  (LABEL_TAC "split") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "int" (MP_TAC o SPECL [`p:real`; `q:real`; `a:real`; `b:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL_ADD] THEN
    MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "split" (MP_TAC o SPECL [`&0`; `r0:real`; `&0`; `inv r0`]) THEN
  USE_THEN "split" (MP_TAC o SPECL [`d - r0`; `d:real`; `d / r0`; `--inv r0`]) THEN
  REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&0,r0]) (\t. (&1 - (&0 + inv r0 * t) pow 2) * R1 t) <=
    &2 / &3 * r0 * c /\
    real_integral (real_interval[d - r0,d])
      (\t. (&1 - (d / r0 + --inv r0 * t) pow 2) * R1 t) <= &2 / &3 * r0 * c`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`d:real`; `r0:real`] CMPI_END_WEIGHTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `real_integral (real_interval[&0,r0])
                    (\t. &1 - (&0 + inv r0 * t) pow 2) * c`;
      EXISTS_TAC `real_integral (real_interval[d - r0,d])
                    (\t. &1 - (d / r0 + --inv r0 * t) pow 2) * c`] THEN
    (CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]]) THEN
    MATCH_MP_TAC CMPI_WEIGHT_BOUND THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `J:real->bool` THEN
       ASM_REWRITE_TAC[] THEN USE_THEN "sub" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THEN X_GEN_TAC `t:real` THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x pow 2 <= &1 ==> &0 <= &1 - x pow 2`) THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_ADD_LID] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "left" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(&1 - (&0 + inv r0 * t) pow 2 = &0)` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < r0` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC(REAL_ARITH `x pow 2 <= &1 ==> &0 <= &1 - x pow 2`) THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN
      SUBGOAL_THEN `d / r0 + --inv r0 * t = (d - t) / r0` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < r0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_SUB_LE] THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "right" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(&1 - (d / r0 + --inv r0 * t) pow 2 = &0)` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `&0 < r0` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * &(dimindex(:N) - 1) * (&2 / &3 * K * r0 + inv r0) =
    &2 * (&2 / &3 * r0 * c) + &2 * &(dimindex(:N) - 1) / r0`
  SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* S6 (CMP_RICCI_INTEGRAL_STATEMENT of pc_cmp_defs), MT Claim                *)
(* 3.24 for the [0,1] parametrization t |-> exp_x(t v), by rescaling to     *)
(* unit speed.                                                               *)
(* ========================================================================= *)

let CMPI_RICCI_SCALE = prove
 (`!top atlas (g:A->real^N^N) y c w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        y IN topspace top
        ==> mfd_ricci atlas g y (c % w) (c % w) = c pow 2 * mfd_ricci atlas g y w w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[mfd_ricci] THEN
  ABBREV_TAC `G = metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A))
                    (g:A->real^N^N)` THEN
  ABBREV_TAC `p = SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)) y` THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                        (FST(chart_at atlas y))`;
                 `G:real^N->real^N^N`; `p:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lricci (G:real^N->real^N^N) p (c % w) (c % w) = c * lricci G p w (c % w) /\
    lricci G p w (c % w) = c * lricci G p w w`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM LIFT_EQ; LIFT_CMUL] THENL
     [MP_TAC(ISPECL [`\a. lift(lricci (G:real^N->real^N^N) p a (c % w))`; `c:real`;
                     `w:real^N`] LINEAR_CMUL);
      MP_TAC(ISPECL [`\b. lift(lricci (G:real^N->real^N^N) p w b)`; `c:real`;
                     `w:real^N`] LINEAR_CMUL)] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* The geodesic of a nonzero vector v and its unit-speed reparametrization. *)

let CMPI_UNIT_GEO = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x /\ &0 < mfd_tnorm g x v
        ==> mfd_geodesic (top,atlas) g (mfd_geo (top,atlas) g x (inv(mfd_tnorm g x v) % v))
                         (mfd_geo_maxint (top,atlas) g x (inv(mfd_tnorm g x v) % v)) /\
            real_interval[&0,mfd_tnorm g x v] SUBSET
            mfd_geo_maxint (top,atlas) g x (inv(mfd_tnorm g x v) % v) /\
            mfd_geo (top,atlas) g x (inv(mfd_tnorm g x v) % v) (&0) = x /\
            mfd_geo (top,atlas) g x (inv(mfd_tnorm g x v) % v) (mfd_tnorm g x v) =
            mfd_exp (top,atlas) g x v /\
            mfd_vel atlas (mfd_geo (top,atlas) g x (inv(mfd_tnorm g x v) % v)) (&0) =
            inv(mfd_tnorm g x v) % v /\
            (!t. t IN mfd_geo_maxint (top,atlas) g x (inv(mfd_tnorm g x v) % v)
                 ==> mfd_vel atlas (mfd_geo (top,atlas) g x (inv(mfd_tnorm g x v) % v)) t dot
                     (g(mfd_geo (top,atlas) g x (inv(mfd_tnorm g x v) % v) t) **
                      mfd_vel atlas (mfd_geo (top,atlas) g x (inv(mfd_tnorm g x v) % v)) t) =
                     &1) /\
            real_interval[&0,&1] SUBSET mfd_geo_maxint (top,atlas) g x v /\
            (!t. t IN mfd_geo_maxint (top,atlas) g x v
                 ==> mfd_tnorm g x v * t IN
                     mfd_geo_maxint (top,atlas) g x (inv(mfd_tnorm g x v) % v) /\
                     mfd_geo (top,atlas) g x v t =
                     mfd_geo (top,atlas) g x (inv(mfd_tnorm g x v) % v) (mfd_tnorm g x v * t) /\
                     mfd_vel atlas (mfd_geo (top,atlas) g x v) t =
                     mfd_tnorm g x v %
                     mfd_vel atlas (mfd_geo (top,atlas) g x (inv(mfd_tnorm g x v) % v))
                       (mfd_tnorm g x v * t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = mfd_tnorm (g:A->real^N^N) x v` THEN
  ABBREV_TAC `u:real^N = inv d % v` THEN
  SUBGOAL_THEN `(v:real^N) = d % u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `gamma = mfd_geo (top,atlas) (g:A->real^N^N) x (u:real^N)` THEN
  ABBREV_TAC `J = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x (u:real^N)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `d:real`] MFD_EXP_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(v:real^N) = d % u` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN SUBST_ALL_TAC(SYM th)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_interval[&0,d] SUBSET J` (LABEL_TAC "dJ") THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    UNDISCH_TAC `is_realinterval J` THEN REWRITE_TAC[is_realinterval] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&0`; `d:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A)`;
                   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A)`;
                   `t:real`; `&0`] MFD_PARALLEL_INNER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CMPG_GEODESIC_C1 THEN EXISTS_TAC `g:A->real^N^N` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC MFD_GEODESIC_VEL_PARALLEL THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))] THEN
                         SUBST1_TAC(SYM(ASSUME `inv d % v = (u:real^N)`)) THEN
                         REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 th))]) THEN
    REWRITE_TAC[ASSUME `mfd_tnorm (g:A->real^N^N) x v = d`; REAL_ABS_INV] THEN
    SIMP_TAC[ASSUME `&0 < d`; REAL_ARITH `&0 < d ==> abs d = d`; REAL_MUL_LINV;
             REAL_LT_IMP_NZ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d % (u:real^N) = v` (LABEL_TAC "du") THENL
   [SUBST1_TAC(SYM(ASSUME `inv d % v = (u:real^N)`)) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `d:real`] MFD_GEO_RESCALE) THEN
  USE_THEN "du" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "dJ" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                (\t. (gamma:real->A)(d * t + &0)) t` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GEOM_VEL_LOCAL THEN
    SUBGOAL_THEN `real_open {t | d * t IN J}` MP_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[real_open; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[REAL_ADD_RID] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `d:real`; `&0`]
    MFD_GEODESIC_AFFINE) THEN
  ASM_REWRITE_TAC[REAL_ADD_RID] THEN ASM_SIMP_TAC[]);;

(* A parallel orthonormal frame along a unit-speed geodesic from x, with   *)
(* Fr_1 = gamma'.                                                           *)

let CMPI_FRAME_UNIT = prove
 (`!top atlas (g:A->real^N^N) (x:A) u.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ mfd_tnorm g x u = &1
        ==> ?Fr. cmp_pframe atlas g (mfd_geo (top,atlas) g x u)
                            (mfd_geo_maxint (top,atlas) g x u) Fr /\
                 (!t. t IN mfd_geo_maxint (top,atlas) g x u
                      ==> Fr 1 t = mfd_vel atlas (mfd_geo (top,atlas) g x u) t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  SUBGOAL_THEN `mfd_orthonormal_frame (g:A->real^N^N) x (E:real^N^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_orthonormal_frame]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible(E:real^N^N)` ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_DET_NZ] THEN DISCH_TAC THEN
    UNDISCH_TAC `transp(E:real^N^N) ** (g:A->real^N^N) x ** E = mat 1` THEN
    DISCH_THEN(MP_TAC o AP_TERM `det:real^N^N->real`) THEN
    ASM_REWRITE_TAC[DET_MUL; DET_I; REAL_MUL_RZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u':real^N = matrix_inv(E:real^N^N) ** (u:real^N)` THEN
  SUBGOAL_THEN `(E:real^N^N) ** u' = u` ASSUME_TAC THENL
   [EXPAND_TAC "u'" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(u':real^N) = &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:A->real^N^N`; `x:A`; `E:real^N^N`; `u':real^N`]
      CMPP_TNORM_FRAME) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?P:real^N^N. orthogonal_matrix P /\ P ** basis 1 = u'`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`basis 1:real^N`; `u':real^N`] ORTHOGONAL_TRANSFORMATION_EXISTS_1) THEN
    ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `matrix(f:real^N->real^N)` THEN
    FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ORTHOGONAL_TRANSFORMATION]) THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `P:real^N^N`; `u':real^N`]
    CMPP_FRAME_ALONG) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* S6 (MT Claim 3.24): the integral of Ric(gamma',gamma') along a           *)
(* minimizing geodesic t |-> exp_x(t v), t in [0,1].                         *)

let CMP_RICCI_INTEGRAL = prove
 (`!(u:A->bool) (n:N->bool). CMP_RICCI_INTEGRAL_STATEMENT u n`,
  REWRITE_TAC[CMP_RICCI_INTEGRAL_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "ric") THEN
  ABBREV_TAC `d = mfd_tnorm (g:A->real^N^N) x v` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] CMPI_UNIT_GEO) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `gamma = mfd_geo (top,atlas) (g:A->real^N^N) x (inv d % v)` THEN
  ABBREV_TAC `J = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x (inv d % v)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) x (inv d % v) = &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `inv d % (v:real^N)`] CMPI_FRAME_UNIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fr:num->real->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `d:real`;
                 `Fr:num->real->real^N`; `r0:real`; `K:real`] CMPI_RICCI_UNIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "ric" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  ABBREV_TAC `R1 = \t. mfd_ricci atlas (g:A->real^N^N) ((gamma:real->A) t)
                         (mfd_vel atlas gamma t) (mfd_vel atlas gamma t)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `((\t. d pow 2 * (R1:real->real)(d * t)) has_real_integral
     (d * real_integral (real_interval[&0,d]) R1)) (real_interval[&0,&1])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`R1:real->real`; `real_integral (real_interval[&0,d]) (R1:real->real)`;
                   `&0`; `d:real`; `d:real`] HAS_REAL_INTEGRAL_STRETCH) THEN
    ASM_SIMP_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL; REAL_LT_IMP_NZ] THEN
    SUBGOAL_THEN `IMAGE (\x. inv d * x) (real_interval[&0,d]) = real_interval[&0,&1]`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `(\x. inv d * x) = (\x. inv d * x + &0)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ADD_RID]; ALL_TAC] THEN
      REWRITE_TAC[IMAGE_AFFINITY_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> ~(d < &0)`; REAL_LE_INV_EQ; REAL_LT_IMP_LE;
                   REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `d pow 2` o MATCH_MP HAS_REAL_INTEGRAL_LMUL) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`] THEN
    UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> d pow 2 * (R1:real->real)(d * t) =
            mfd_ricci atlas (g:A->real^N^N) (mfd_geo (top,atlas) g x v t)
              (mfd_vel atlas (mfd_geo (top,atlas) g x v) t)
              (mfd_vel atlas (mfd_geo (top,atlas) g x v) t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `t IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> tm = `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v`))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "R1" THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMPI_RICCI_SCALE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_EQ o
    CONJ (ASSUME `!t. t IN real_interval[&0,&1]
                      ==> d pow 2 * (R1:real->real)(d * t) =
                          mfd_ricci atlas (g:A->real^N^N) (mfd_geo (top,atlas) g x v t)
                            (mfd_vel atlas (mfd_geo (top,atlas) g x v) t)
                            (mfd_vel atlas (mfd_geo (top,atlas) g x v) t)`)) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HAS_REAL_INTEGRAL_INTEGRABLE) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_binary "real_le" o concl)) THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;


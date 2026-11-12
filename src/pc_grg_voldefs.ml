(* ========================================================================= *)
(* pc_grg_voldefs: the definitions of Riemannian volume and integration on  *)
(* a manifold, with a few cheap sanity theorems; the theory itself follows  *)
(* in pc_grg_vol.  The Riemannian density in a chart is sqrt(det g_ij)      *)
(* (Lee, Introduction to Smooth Manifolds, 2nd ed., Prop. 15.31 p. 389 and  *)
(* Prop. 16.45 p. 432).  As in Lee Ch. 16 (p. 432, integral of a density    *)
(* supported in one chart, then summed over pieces; Exercise 16.44: cutting *)
(* the manifold into pieces), an integral is a sum of chart integrals, but  *)
(* over a countable measurable chart partition instead of a smooth          *)
(* partition of unity, and for absolutely (Lebesgue) integrable functions   *)
(* instead of compactly supported densities.                                 *)
(* ========================================================================= *)

needs "src/pc_grg_dist.ml";;

prioritize_real();;
type_invention_error := true;;

(* The Riemannian density sqrt(det g_c) in the chart c. *)

let mfd_density = new_definition
 `mfd_density (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N))
              (g:A->real^N^N) (y:real^N) =
    sqrt(det(metric_local atlas c g y))`;;

(* The integrand of f : A -> real in the chart c, as a real^1-valued map on  *)
(* real^N (HOL integrals are vector-valued).                                 *)

let mfd_chart_integrand = new_definition
 `mfd_chart_integrand (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                      (f:A->real) (c:(A->bool)#(A->real^N)) (y:real^N) =
    lift(f(chart_inv c y) * mfd_density atlas c g y)`;;

(* Lebesgue measurable subsets of the manifold: measurable in every chart. *)

let mfd_lebesgue_measurable = new_definition
 `mfd_lebesgue_measurable (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                          (S:A->bool) <=>
    S SUBSET topspace top /\
    !c. c IN atlas ==> lebesgue_measurable (IMAGE (SND c) (FST c INTER S))`;;

(* A countable measurable chart partition (c n, E n) of S: disjoint pieces,  *)
(* each inside the domain of its chart with Lebesgue measurable image.  An  *)
(* empty piece may carry any chart, so that the empty manifold (empty atlas) *)
(* has partitions of the empty set.                                          *)

let mfd_chart_partition = new_definition
 `mfd_chart_partition (atlas:((A->bool)#(A->real^N))->bool) (S:A->bool)
                      (c:num->(A->bool)#(A->real^N)) (E:num->A->bool) <=>
    (!n. (E n = {} \/ c n IN atlas) /\ E n SUBSET FST(c n) /\
         lebesgue_measurable (IMAGE (SND(c n)) (E n))) /\
    (!m n. ~(m = n) ==> DISJOINT (E m) (E n)) /\
    UNIONS {E n | n IN (:num)} = S`;;

(* f is (Lebesgue, i.e. absolutely) integrable over S with integral v: for   *)
(* some chart partition of S, f is absolutely integrable on every piece,    *)
(* the integrals of |f| over the pieces are summable, and the integrals     *)
(* over the pieces sum to v.  The value and the integrability do not depend *)
(* on the partition (MFD_HAS_INTEGRAL_UNIQUE, MFD_HAS_INTEGRAL_PARTITION).   *)
(* top is not used; it is kept for a uniform (top,atlas) interface.         *)

let mfd_has_integral = new_definition
 `mfd_has_integral (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                   (g:A->real^N^N) (f:A->real) (S:A->bool) (v:real) <=>
    ?c E. mfd_chart_partition atlas S c E /\
          (!n. mfd_chart_integrand atlas g f (c n) absolutely_integrable_on
               IMAGE (SND(c n)) (E n)) /\
          real_summable (from 0)
            (\n. drop(integral (IMAGE (SND(c n)) (E n))
                       (\y. lift(norm(mfd_chart_integrand atlas g f (c n) y))))) /\
          ((\n. drop(integral (IMAGE (SND(c n)) (E n))
                      (mfd_chart_integrand atlas g f (c n)))) real_sums v) (from 0)`;;

let mfd_integrable_on = new_definition
 `mfd_integrable_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                    (g:A->real^N^N) (f:A->real) (S:A->bool) <=>
    ?v. mfd_has_integral (top,atlas) g f S v`;;

let mfd_integral = new_definition
 `mfd_integral (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
               (g:A->real^N^N) (S:A->bool) (f:A->real) =
    @v. mfd_has_integral (top,atlas) g f S v`;;

(* Finite volume v of S, and the volume (unspecified if S has no finite     *)
(* volume, as for HOL's measure).                                            *)

let mfd_has_volume = new_definition
 `mfd_has_volume (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                 (g:A->real^N^N) (S:A->bool) (v:real) <=>
    mfd_has_integral (top,atlas) g (\x. &1) S v`;;

let mfd_volume = new_definition
 `mfd_volume (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
             (g:A->real^N^N) (S:A->bool) =
    @v. mfd_has_volume (top,atlas) g S v`;;

(* ------------------------------------------------------------------------- *)
(* Sanity theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

let MFD_LEBESGUE_MEASURABLE_EMPTY = prove
 (`!top atlas. mfd_lebesgue_measurable
                 (top,atlas:((A->bool)#(A->real^N))->bool) {}`,
  REWRITE_TAC[mfd_lebesgue_measurable; EMPTY_SUBSET; INTER_EMPTY;
              IMAGE_CLAUSES; LEBESGUE_MEASURABLE_EMPTY]);;

let MFD_CHART_PARTITION_EMPTY = prove
 (`!atlas (c:(A->bool)#(A->real^N)).
        mfd_chart_partition atlas {} (\n. c) (\n. {})`,
  REWRITE_TAC[mfd_chart_partition; EMPTY_SUBSET; IMAGE_CLAUSES;
              LEBESGUE_MEASURABLE_EMPTY; DISJOINT_EMPTY] THEN
  SET_TAC[]);;

let MFD_HAS_INTEGRAL_EMPTY = prove
 (`!top atlas (g:A->real^N^N) f.
        mfd_has_integral (top,atlas) g f {} (&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_has_integral] THEN
  MAP_EVERY EXISTS_TAC
   [`\n:num. ({}:A->bool,(\x:A. vec 0:real^N))`; `\n:num. {}:A->bool`] THEN
  REWRITE_TAC[MFD_CHART_PARTITION_EMPTY; IMAGE_CLAUSES;
              ABSOLUTELY_INTEGRABLE_ON_EMPTY; INTEGRAL_EMPTY; DROP_VEC;
              REAL_SUMMABLE_0; REAL_SERIES_0]);;

let MFD_HAS_VOLUME_EMPTY = prove
 (`!top atlas (g:A->real^N^N). mfd_has_volume (top,atlas) g {} (&0)`,
  REWRITE_TAC[mfd_has_volume; MFD_HAS_INTEGRAL_EMPTY]);;

let MFD_INTEGRABLE_INTEGRAL = prove
 (`!top atlas (g:A->real^N^N) f (S:A->bool).
        mfd_integrable_on (top,atlas) g f S <=>
        mfd_has_integral (top,atlas) g f S (mfd_integral (top,atlas) g S f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_integrable_on; mfd_integral] THEN
  CONV_TAC(RAND_CONV SELECT_CONV) THEN REWRITE_TAC[]);;

let MFD_HAS_INTEGRAL_CMUL = prove
 (`!top atlas (g:A->real^N^N) f S v k.
        mfd_has_integral (top,atlas) g f S v
        ==> mfd_has_integral (top,atlas) g (\x. k * f x) S (k * v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_has_integral] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `E:num->A->bool` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`c:num->(A->bool)#(A->real^N)`; `E:num->A->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!c0. mfd_chart_integrand atlas (g:A->real^N^N) (\x. k * f x) c0 =
         (\y. k % mfd_chart_integrand atlas g f c0 y)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; mfd_chart_integrand; GSYM LIFT_CMUL; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                         ((c:num->(A->bool)#(A->real^N)) n) y)))
        integrable_on IMAGE (SND(c n)) ((E:num->A->bool) n)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[NORM_MUL; LIFT_CMUL] THEN
    ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN
    MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
                 ETA_AX] THEN
    MATCH_MP_TAC REAL_SERIES_LMUL THEN ASM_REWRITE_TAC[]]);;

let MFD_HAS_INTEGRAL_CONST = prove
 (`!top atlas (g:A->real^N^N) S v k.
        mfd_has_volume (top,atlas) g S v
        ==> mfd_has_integral (top,atlas) g (\x. k) S (k * v)`,
  REWRITE_TAC[mfd_has_volume] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:real` o MATCH_MP MFD_HAS_INTEGRAL_CMUL) THEN
  REWRITE_TAC[REAL_MUL_RID]);;

(* Teeth: for the flat metric in the identity chart of an open set of       *)
(* real^N the density is 1, and Lebesgue measure is a volume.               *)

let GRGV_DENSITY_EUCLIDEAN = prove
 (`!U y:real^N.
        open U /\ y IN U
        ==> mfd_density {(U,\x:real^N. x)} (U,\x. x) (\x. mat 1) y = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_density] THEN
  ASM_SIMP_TAC[GRGD_EUCLID_METRIC_LOCAL; DET_I; SQRT_1]);;

let GRGV_SUMS_FIRST = prove
 (`!a:num->real. (!n. ~(n = 0) ==> a n = &0) ==> (a real_sums a 0) (from 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:num->real`; `{0}`; `from 0`] REAL_SERIES_FINITE_SUPPORT) THEN
  SUBGOAL_THEN `{0} INTER from 0 = {0}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; IN_FROM] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_SING; SUM_SING; IN_SING]);;

let GRGV_EUCLIDEAN_HAS_VOLUME = prove
 (`!U (S:real^N->bool) v.
        open U /\ S SUBSET U /\ S has_measure v
        ==> mfd_has_volume (subtopology euclidean U,{(U,\x:real^N. x)})
                           (\x. mat 1) S v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_has_volume; mfd_has_integral] THEN
  MAP_EVERY EXISTS_TAC
   [`\n:num. (U:real^N->bool,\x:real^N. x)`;
    `\n:num. if n = 0 then S else {}:real^N->bool`] THEN
  SUBGOAL_THEN `measurable(S:real^N->bool) /\ measure S = v` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[HAS_MEASURE_MEASURABLE_MEASURE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^N. y IN S
        ==> mfd_chart_integrand {(U,\x:real^N. x)} (\x. mat 1) (\x. &1)
                                (U,\x. x) y = vec 1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_chart_integrand; REAL_MUL_LID] THEN
    SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[GRGV_DENSITY_EUCLIDEAN; LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!H:real^N->real^1.
        (!y. y IN S ==> H y = vec 1)
        ==> ((\n. drop(integral (if n = 0 then S else {}) H)) real_sums v)
            (from 0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `v = (\n. drop(integral (if n = 0 then S else {}) (H:real^N->real^1))) 0`
    SUBST1_TAC THENL
     [REWRITE_TAC[] THEN
      TRANS_TAC EQ_TRANS `drop(integral S (\y:real^N. vec 1:real^1))` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[INTEGRAL_MEASURE; LIFT_DROP];
        AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]];
      MATCH_MP_TAC GRGV_SUMS_FIRST THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[INTEGRAL_EMPTY; DROP_VEC]];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_ID] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_chart_partition; IN_SING; IMAGE_ID; FST] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[EMPTY_SUBSET; LEBESGUE_MEASURABLE_EMPTY;
                   MEASURABLE_IMP_LEBESGUE_MEASURABLE];
      REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT COND_CASES_TAC THEN
      ASM_REWRITE_TAC[DISJOINT_EMPTY] THEN ASM_MESON_TAC[];
      GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool`
         (CONJUNCTS_THEN2 (X_CHOOSE_THEN `n:num` ASSUME_TAC) MP_TAC)) THEN
        ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY];
        DISCH_TAC THEN EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `0` THEN REWRITE_TAC[]]];
    GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[ABSOLUTELY_INTEGRABLE_ON_EMPTY] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
    EXISTS_TAC `\y:real^N. vec 1:real^1` THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_ON_CONST];
    REWRITE_TAC[real_summable] THEN EXISTS_TAC `v:real` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[NORM_1; DROP_VEC; REAL_ABS_NUM; LIFT_NUM];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;


(* ========================================================================= *)
(* Unit pc_cmc_global: locality of cm_harmonic and the global planar         *)
(* compactness of almost-harmonic sequences (Colding-Minicozzi 2008, Lemma   *)
(* B.23):                                                                    *)
(*   - linearity of the Euler-Lagrange density, the first variation          *)
(*     functional cmc_fv, locality of cm_harmonic (CMC_HARMONIC_LOCAL);      *)
(*   - cmc_l2conv (L^2 convergence with first partials) and its calculus:    *)
(*     subsequences, subsets, uniqueness, finite covers;                     *)
(*   - rational balls, separation, CMC_LOCAL_EV, CMC_DIAG_INC, energy        *)
(*     limits on rational balls, finite concentration set;                   *)
(*   - CMC_GLOBAL_DIAG and the global theorem CMC_GLOBAL.                    *)
(* ========================================================================= *)

needs "src/pc_cmc_local.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The Euler-Lagrange density is linear in the variation.                    *)
(* ------------------------------------------------------------------------- *)

let CMC_ELD_LINEAR = prove
 (`!S (G:real^K->real^K^K) d p q h1 h2 k1 k2 c.
     cm_target S G d /\ p IN S
     ==> hmrm_eld S G p q (h1 + h2) (k1 + k2) =
         hmrm_eld S G p q h1 k1 + hmrm_eld S G p q h2 k2 /\
         hmrm_eld S G p q (c % h1) (c % k1) = c * hmrm_eld S G p q h1 k1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o
     (\y. jacobian (closest_point S) (at y))) differentiable at (p:real^K) /\
    ((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K))
    differentiable at p`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:real^K. jacobian (closest_point S) (at y)`; `p:real^K`]
                LRG_MDERIV_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `p:real^K`] LRG_MDERIV_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[hmrm_eld] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
                  MATRIX_VECTOR_MUL_RMUL; MATRIX_VECTOR_LMUL;
                  DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  CONJ_TAC THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* The first variation functional cmc_fv of a smooth S-valued map.           *)
(* ------------------------------------------------------------------------- *)

let cmc_fv = new_definition
 `cmc_fv (S:real^K->bool) (G:real^K->real^K^K) (s:real^2->bool) (u:real^2->real^K)
         (phi:real^2->real^K) =
    sum(1..2) (\i. drop(integral s
      (\x. lift(hmrm_eld S G (u x) (partial_derivative i u x) (phi x)
                         (partial_derivative i phi x)))))`;;

let CMC_FV_FACTS = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) t (phi:real^2->real^K).
     cm_target S G d /\ open s /\ smooth_map_on s u /\ (!x. x IN s ==> u x IN S) /\
     open t /\ bounded t /\ closure t SUBSET s /\ wan_vtest t phi
     ==> (!i. 1 <= i /\ i <= 2
              ==> (\x. lift(hmrm_eld S G (u x) (partial_derivative i u x) (phi x)
                                     (partial_derivative i phi x))) integrable_on t) /\
         ((\e. cm_gen G t (\x. closest_point S (u x + e % phi x))) has_real_derivative
          cmc_fv S G t u phi / &2) (atreal (&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^2->bool) SUBSET s` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^2->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `u:real^2->real^K`; `t:real^2->bool`]
                CMC_W12_SMOOTH_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `t:real^2->bool`;
                 `u:real^2->real^K`; `phi:real^2->real^K`] HMRM_FIRST_VARIATION_W12) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> integral t (\x. lift(hmrm_eld S G ((u:real^2->real^K) x) (wan_wd t i u x)
                                  ((phi:real^2->real^K) x) (partial_derivative i phi x))) =
            integral t (\x. lift(hmrm_eld S G (u x) (partial_derivative i u x)
                                  (phi x) (partial_derivative i phi x))) /\
            ((\x. lift(hmrm_eld S G (u x) (wan_wd t i u x) (phi x)
                                (partial_derivative i phi x))) integrable_on t <=>
             (\x. lift(hmrm_eld S G (u x) (partial_derivative i u x) (phi x)
                                (partial_derivative i phi x))) integrable_on t)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CMC_ELD_SPIKE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..2) (\i. drop(integral t
       (\x. lift(hmrm_eld S G ((u:real^2->real^K) x) (wan_wd t i u x)
                          ((phi:real^2->real^K) x) (partial_derivative i phi x))))) =
    cmc_fv S G t u phi`
  (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[cmc_fv] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let CMC_HARMONIC_FV = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K).
     cm_target S G d /\ open s
     ==> (cm_harmonic S G s u <=>
          smooth_map_on s u /\ (!x. x IN s ==> u x IN S) /\
          !phi t. open t /\ bounded t /\ closure t SUBSET s /\ wan_vtest t phi
                  ==> cmc_fv S G t u phi = &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cm_harmonic] THEN
  ASM_CASES_TAC `smooth_map_on s (u:real^2->real^K)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `!x. x IN s ==> (u:real^2->real^K) x IN S` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`phi:real^2->real^K`; `t:real^2->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `t:real^2->bool`; `phi:real^2->real^K`] CMC_FV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`phi:real^2->real^K`; `t:real^2->bool`]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_DERIVATIVE_UNIQUE_ATREAL) THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`phi:real^2->real^K`; `t:real^2->bool`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO]]);;

(* The integrand vanishes off the support of the variation.                  *)

let CMC_ELD_ZERO = prove
 (`!S (G:real^K->real^K^K) d p q.
     cm_target S G d /\ p IN S ==> hmrm_eld S G p q (vec 0) (vec 0) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `p:real^K`; `q:real^K`;
                 `vec 0:real^K`; `vec 0:real^K`; `vec 0:real^K`; `vec 0:real^K`; `&0`]
                CMC_ELD_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; REAL_MUL_LZERO]);;

let CMC_FV_SUPPORT = prove
 (`!S (G:real^K->real^K^K) d (u:real^2->real^K) (phi:real^2->real^K) k t1 t2.
     cm_target S G d /\ compact k /\ (!x. ~(x IN k) ==> phi x = vec 0) /\
     k SUBSET t1 /\ k SUBSET t2 /\
     (!x. x IN t1 ==> u x IN S) /\ (!x. x IN t2 ==> u x IN S)
     ==> cmc_fv S G t1 u phi = cmc_fv S G t2 u phi`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i x. ~(x IN k) ==> partial_derivative i (phi:real^2->real^K) x = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`i:num`; `phi:real^2->real^K`; `\x:real^2. vec 0:real^K`;
                   `(:real^2) DIFF k`; `x:real^2`] PARTIAL_DERIVATIVE_LOCAL_OPEN) THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV;
                 PARTIAL_DERIVATIVE_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. k SUBSET t /\ (!x. x IN t ==> (u:real^2->real^K) x IN S)
        ==> !i. integral t (\x. lift(hmrm_eld S G (u x) (partial_derivative i u x)
                                       ((phi:real^2->real^K) x)
                                       (partial_derivative i phi x))) =
                integral k (\x. lift(hmrm_eld S G (u x) (partial_derivative i u x)
                                       (phi x) (partial_derivative i phi x)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^2` THEN
    ASM_CASES_TAC `(x:real^2) IN k` THENL
     [SUBGOAL_THEN `(x:real^2) IN t` (fun th -> ASM_REWRITE_TAC[th]) THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `hmrm_eld S G ((u:real^2->real^K) x) (partial_derivative i u x)
                      (vec 0) (vec 0) = &0` (fun th -> REWRITE_TAC[th; LIFT_NUM]) THEN
      MATCH_MP_TAC CMC_ELD_ZERO THEN EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[cmc_fv] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Additivity of the first variation and locality of cm_harmonic (a smooth   *)
(* partition of unity from smooth_bump on finitely many balls).              *)
(* ------------------------------------------------------------------------- *)

let CMC_ELD_VSUM = prove
 (`!S (G:real^K->real^K^K) d p q (h:real^2->real^K) (k:real^2->real^K) c.
     cm_target S G d /\ p IN S /\ FINITE c
     ==> hmrm_eld S G p q (vsum c h) (vsum c k) =
         sum c (\y. hmrm_eld S G p q (h y) (k y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN DISCH_TAC THEN
  SPEC_TAC(`c:real^2->bool`,`c:real^2->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; SUM_CLAUSES] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMC_ELD_ZERO THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real^2`; `c:real^2->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `p:real^K`; `q:real^K`;
                   `(h:real^2->real^K) x`; `vsum c (h:real^2->real^K)`;
                   `(k:real^2->real^K) x`; `vsum c (k:real^2->real^K)`; `&1`]
                  CMC_ELD_LINEAR) THEN
    ASM_SIMP_TAC[]]);;

let CMC_FV_VSUM = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) t (f:real^2->real^2->real^K) c.
     cm_target S G d /\ open s /\ smooth_map_on s u /\ (!x. x IN s ==> u x IN S) /\
     open t /\ bounded t /\ closure t SUBSET s /\ FINITE c /\
     (!y. y IN c ==> wan_vtest t (f y))
     ==> cmc_fv S G t u (\x. vsum c (\y. f y x)) = sum c (\y. cmc_fv S G t u (f y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^2->bool) SUBSET s` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^2->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y x. y IN c ==> (f:real^2->real^2->real^K) y differentiable at x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^2)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    ASM_MESON_TAC[wan_vtest];
    ALL_TAC] THEN
  REWRITE_TAC[cmc_fv] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_SWAP o rand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `integral t (\x. lift(hmrm_eld S G ((u:real^2->real^K) x) (partial_derivative i u x)
                      (vsum c (\y. (f:real^2->real^2->real^K) y x))
                      (partial_derivative i (\x. vsum c (\y. f y x)) x))) =
    integral t (\x. vsum c (\y. lift(hmrm_eld S G (u x) (partial_derivative i u x)
                                       (f y x) (partial_derivative i (f y) x))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`i:num`; `f:real^2->real^2->real^K`; `c:real^2->bool`; `x:real^2`]
                  PARTIAL_DERIVATIVE_VSUM) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `(u:real^2->real^K) x`; `partial_derivative i (u:real^2->real^K) x`;
                   `\y. (f:real^2->real^2->real^K) y x`;
                   `\y. partial_derivative i ((f:real^2->real^2->real^K) y) x`;
                   `c:real^2->bool`] CMC_ELD_VSUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) INTEGRAL_VSUM o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                   `u:real^2->real^K`; `t:real^2->bool`;
                   `(f:real^2->real^2->real^K) y`] CMC_FV_FACTS) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_VSUM; o_DEF]]);;

(* Translated bumps.                                                          *)

let CMC_BUMP_SMOOTH = prove
 (`!a b (y:real^2).
     &0 <= a /\ a < b
     ==> smooth_map_on (:real^2) (\x. lift(smooth_bump a b (x - y)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift(smooth_bump a b (x - y))) =
                (\x. lift(smooth_bump a b x)) o (\x:real^2. x - y)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
  ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_BUMP_SMOOTH] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

(* Locality: harmonic on a neighbourhood of each point implies harmonic.    *)

let CMC_HARMONIC_LOCAL = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K).
     cm_target S G d /\ open s /\ smooth_map_on s u /\ (!x. x IN s ==> u x IN S) /\
     (!x. x IN s ==> ?r. &0 < r /\ ball(x,r) SUBSET s /\ cm_harmonic S G (ball(x,r)) u)
     ==> cm_harmonic S G s u`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^2->real` (LABEL_TAC "R")) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`] CMC_HARMONIC_FV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`phi:real^2->real^K`; `t:real^2->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^2->bool) SUBSET s` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^2->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x. x IN k ==> &0 < (r:real^2->real) x /\ ball(x,r x) SUBSET s /\
                              cm_harmonic S G (ball(x,r x)) (u:real^2->real^K)`
  (LABEL_TAC "RK") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "R" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  (* A finite subcover of k by quarter balls. *)
  MP_TAC(ISPEC `k:real^2->bool` COMPACT_IMP_HEINE_BOREL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\y:real^2. ball(y,(r:real^2->real) y / &4)) k`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EXISTS_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    USE_THEN "RK" (MP_TAC o SPEC `x:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\y:real^2. ball(y,(r:real^2->real) y / &4)`; `k:real^2->bool`;
                 `ff:(real^2->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN k ==> ?y. y IN c /\ norm(x - y) < (r:real^2->real) y / &4`
  (LABEL_TAC "COV") THENL
   [UNDISCH_TAC `k SUBSET UNIONS (ff:(real^2->bool)->bool)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_BALL; dist; NORM_SUB] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN c ==> &0 < (r:real^2->real) y /\ ball(y,r y) SUBSET s /\
                              cm_harmonic S G (ball(y,r y)) (u:real^2->real^K)`
  (LABEL_TAC "RC") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "RK" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  (* The bumps and their sum. *)
  ABBREV_TAC `g = \x:real^2. sum c (\y. smooth_bump ((r:real^2->real) y / &4)
                                                    (r y / &2) (x - y))` THEN
  SUBGOAL_THEN `!y. y IN c ==> smooth_map_on (:real^2)
                    (\x. lift(smooth_bump ((r:real^2->real) y / &4) (r y / &2) (x - y)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_BUMP_SMOOTH THEN
    USE_THEN "RC" (MP_TAC o SPEC `y:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\x. lift((g:real^2->real) x))` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN
    MP_TAC(ISPECL [`(:real^2)`;
                   `\y x. lift(smooth_bump ((r:real^2->real) y / &4) (r y / &2) (x - y))`;
                   `c:real^2->bool`] SMOOTH_MAP_ON_LIFT_SUM) THEN
    ASM_SIMP_TAC[OPEN_UNIV; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN k ==> &1 <= (g:real^2->real) x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "COV" (MP_TAC o SPEC `x:real^2`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\y. smooth_bump ((r:real^2->real) y / &4) (r y / &2) ((x:real^2) - y)`;
                   `c:real^2->bool`; `y:real^2`] SUM_DELETE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `smooth_bump ((r:real^2->real) y / &4) (r y / &2) ((x:real^2) - y) = &1`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_1 THEN
      USE_THEN "RC" (MP_TAC o SPEC `y:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
      UNDISCH_TAC `norm((x:real^2) - y) < (r:real^2->real) y / &4` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> a = b - &1 ==> &1 <= b`) THEN
    MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[SMOOTH_BUMP_BOUNDS];
    ALL_TAC] THEN
  ABBREV_TAC `W = {x:real^2 | &1 / &2 < (g:real^2->real) x}` THEN
  SUBGOAL_THEN `open(W:real^2->bool) /\ (k:real^2->bool) SUBSET W` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `W = {x:real^2 | lift((g:real^2->real) x) IN {y:real^1 | y$1 > &1 / &2}}`
      SUBST1_TAC THENL
       [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM; GSYM drop; LIFT_DROP; real_gt];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
      REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN
      MP_TAC(ISPECL [`\x. lift((g:real^2->real) x)`; `(:real^2)`]
                    CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      EXPAND_TAC "W" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      ASM_MESON_TAC[REAL_ARITH `&1 <= g ==> &1 / &2 < g`]];
    ALL_TAC] THEN
  (* The pieces of the variation. *)
  ABBREV_TAC
   `p = \y x. (smooth_bump ((r:real^2->real) y / &4) (r y / &2) (x - y) *
               inv((g:real^2->real) x)) % (phi:real^2->real^K) x` THEN
  SUBGOAL_THEN
   `!y x. y IN c /\ (~(x IN k) \/ ~(x IN cball(y,(r:real^2->real) y / &2)))
          ==> (p:real^2->real^2->real^K) y x = vec 0`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^2`; `x:real^2`] THEN STRIP_TAC THEN EXPAND_TAC "p" THEN
    REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[VECTOR_MUL_RZERO];
      SUBGOAL_THEN `smooth_bump ((r:real^2->real) y / &4) (r y / &2) ((x:real^2) - y) = &0`
      (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO; VECTOR_MUL_LZERO]) THEN
      MATCH_MP_TAC SMOOTH_BUMP_0 THEN
      USE_THEN "RC" (MP_TAC o SPEC `y:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
      UNDISCH_TAC `~((x:real^2) IN cball(y,(r:real^2->real) y / &2))` THEN
      REWRITE_TAC[IN_CBALL; dist; NORM_SUB] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN c ==> smooth_map_on (:real^2) ((p:real^2->real^2->real^K) y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN X_GEN_TAC `x:real^2` THEN
    ASM_CASES_TAC `(x:real^2) IN W` THENL
     [EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "p" THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`W:real^2->bool`;
                     `\x. lift(smooth_bump ((r:real^2->real) y / &4) (r y / &2) (x - y) *
                               inv((g:real^2->real) x))`;
                     `phi:real^2->real^K`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
      REWRITE_TAC[LIFT_DROP; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`W:real^2->bool`;
                       `\x. lift(smooth_bump ((r:real^2->real) y / &4) (r y / &2) (x - y))`;
                       `\x. lift(inv((g:real^2->real) x))`] SMOOTH_MAP_ON_LIFT_MUL) THEN
        REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
          ASM_SIMP_TAC[SUBSET_UNIV];
          MP_TAC(ISPECL [`W:real^2->bool`; `\x. lift((g:real^2->real) x)`]
                        SMOOTH_MAP_ON_LIFT_INV) THEN
          REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
            ASM_REWRITE_TAC[SUBSET_UNIV];
            EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC]];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      EXISTS_TAC `(:real^2) DIFF k` THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\x:real^2. vec 0:real^K` THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; SMOOTH_MAP_ON_CONST; IN_DIFF; IN_UNIV]];
    ALL_TAC] THEN
  (* Each piece has vanishing first variation. *)
  SUBGOAL_THEN `!y. y IN c ==> cmc_fv S G t u ((p:real^2->real^2->real^K) y) = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    USE_THEN "RC" (MP_TAC o SPEC `y:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^2->real^K`;
                   `(p:real^2->real^2->real^K) y`; `k INTER cball(y:real^2,r y / &2)`;
                   `t:real^2->bool`; `ball(y:real^2,&3 * r y / &4)`] CMC_FV_SUPPORT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[COMPACT_INTER_CLOSED; CLOSED_CBALL; IN_INTER; DE_MORGAN_THM] THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        REWRITE_TAC[SUBSET; IN_INTER; IN_CBALL; IN_BALL] THEN
        UNDISCH_TAC `&0 < (r:real^2->real) y` THEN REAL_ARITH_TAC;
        ASM SET_TAC[];
        SUBGOAL_THEN `ball(y:real^2,&3 * r y / &4) SUBSET ball(y,r y)` MP_TAC THENL
         [MATCH_MP_TAC SUBSET_BALL THEN UNDISCH_TAC `&0 < (r:real^2->real) y` THEN
          REAL_ARITH_TAC;
          ASM SET_TAC[]]];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `ball(y:real^2,r y)`;
                   `u:real^2->real^K`] CMC_HARMONIC_FV) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    DISCH_THEN(MP_TAC o SPECL [`(p:real^2->real^2->real^K) y`; `ball(y:real^2,&3 * r y / &4)`] o
               CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `&0 < &3 * (r:real^2->real) y / &4` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < (r:real^2->real) y` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_BALL; BOUNDED_BALL; CLOSURE_BALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN UNDISCH_TAC `&0 < (r:real^2->real) y` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[wan_vtest] THEN ASM_SIMP_TAC[] THEN
    EXISTS_TAC `k INTER cball(y:real^2,r y / &2)` THEN
    ASM_SIMP_TAC[COMPACT_INTER_CLOSED; CLOSED_CBALL; IN_INTER; DE_MORGAN_THM] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_CBALL; IN_BALL] THEN
    UNDISCH_TAC `&0 < (r:real^2->real) y` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* The variation is the sum of its pieces. *)
  SUBGOAL_THEN `(phi:real^2->real^K) = (\x. vsum c (\y. (p:real^2->real^2->real^K) y x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^2` THEN
    ASM_CASES_TAC `(x:real^2) IN W` THENL
     [EXPAND_TAC "p" THEN REWRITE_TAC[VSUM_RMUL; SUM_RMUL] THEN
      SUBGOAL_THEN `sum c (\y. smooth_bump ((r:real^2->real) y / &4) (r y / &2) ((x:real^2) - y)) =
                    (g:real^2->real) x` SUBST1_TAC THENL
       [EXPAND_TAC "g" THEN REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~((g:real^2->real) x = &0)` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^2) IN W` THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID]];
      SUBGOAL_THEN `~((x:real^2) IN k)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_EQ_0 THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `t:real^2->bool`; `p:real^2->real^2->real^K`;
                 `c:real^2->bool`] CMC_FV_VSUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[wan_vtest] THEN ASM_SIMP_TAC[] THEN
    EXISTS_TAC `k INTER cball(y:real^2,(r:real^2->real) y / &2)` THEN
    ASM_SIMP_TAC[COMPACT_INTER_CLOSED; CLOSED_CBALL; IN_INTER; DE_MORGAN_THM] THEN
    ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* L^2 convergence of a planar sequence with its first weak partials on a    *)
(* set, and its behaviour under subsequences, subsets and finite covers.     *)
(* ------------------------------------------------------------------------- *)

let cmc_l2conv = new_definition
 `cmc_l2conv (E:real^2->bool) (w:num->real^2->real^K) (u:real^2->real^K) <=>
    (!j. (\x. w j x - u x) IN lspace E (&2)) /\
    ((\j. lnorm E (&2) (\x. w j x - u x)) ---> &0) sequentially /\
    !i. 1 <= i /\ i <= 2
        ==> (!j. (\x. wan_wd (:real^2) i (w j) x - partial_derivative i u x)
                 IN lspace E (&2)) /\
            ((\j. lnorm E (&2)
                    (\x. wan_wd (:real^2) i (w j) x - partial_derivative i u x))
             ---> &0) sequentially`;;

(* Eventual subsequences preserve null sequences.                             *)

let CMC_NULL_EVSUB = prove
 (`!(f:num->real) (k1:num->num) k2 N.
     (!j. N <= j ==> ?j'. j <= j' /\ k2 j = k1 j') /\
     ((\j. f (k1 j)) ---> &0) sequentially
     ==> ((\j. f (k2 j)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EV") (LABEL_TAC "L")) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "L" (MP_TAC o SPEC `e:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN EXISTS_TAC `N + M:num` THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  USE_THEN "EV" (MP_TAC o SPEC `j:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let CMC_L2CONV_EVSUB = prove
 (`!E (w:num->real^2->real^K) u (k1:num->num) k2 N.
     cmc_l2conv E (\j. w (k1 j)) u /\ (!j. N <= j ==> ?j'. j <= j' /\ k2 j = k1 j') /\
     (!j. ?m. k2 j = k1 m)
     ==> cmc_l2conv E (\j. w (k2 j)) u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_l2conv] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "A") (CONJUNCTS_THEN2 (LABEL_TAC "B") (LABEL_TAC "C")))
    (CONJUNCTS_THEN2 (LABEL_TAC "EV") (LABEL_TAC "IN"))) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN USE_THEN "IN" (X_CHOOSE_TAC `m:num` o SPEC `j:num`) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`\n. lnorm E (&2) (\x. (w:num->real^2->real^K) n x - u x)`;
                   `k1:num->num`; `k2:num->num`; `N:num`] CMC_NULL_EVSUB) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "C" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN USE_THEN "IN" (X_CHOOSE_TAC `m:num` o SPEC `j:num`) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`\n. lnorm E (&2) (\x. wan_wd (:real^2) i ((w:num->real^2->real^K) n) x -
                                          partial_derivative i (u:real^2->real^K) x)`;
                     `k1:num->num`; `k2:num->num`; `N:num`] CMC_NULL_EVSUB) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let CMC_L2CONV_SUBSEQ = prove
 (`!E (w:num->real^2->real^K) u (k:num->num).
     cmc_l2conv E w u /\ (!m n. m < n ==> k m < k n)
     ==> cmc_l2conv E (\j. w (k j)) u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_l2conv] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "A") (CONJUNCTS_THEN2 (LABEL_TAC "B") (LABEL_TAC "C")))
    ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\n. lnorm E (&2) (\x. (w:num->real^2->real^K) n x - u x)`;
                   `&0`; `k:num->num`] HMD_REALLIM_SUBSEQ) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "C" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\n. lnorm E (&2) (\x. wan_wd (:real^2) i ((w:num->real^2->real^K) n) x -
                                        partial_derivative i (u:real^2->real^K) x)`;
                   `&0`; `k:num->num`] HMD_REALLIM_SUBSEQ) THEN
    ASM_REWRITE_TAC[]]);;

let CMC_L2CONV_SUBSET = prove
 (`!E E' (w:num->real^2->real^K) u.
     cmc_l2conv E w u /\ lebesgue_measurable E' /\ E' SUBSET E
     ==> cmc_l2conv E' w u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_l2conv] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`E:real^2->bool`; `E':real^2->bool`;
                   `\j x. (w:num->real^2->real^K) j x - u x`] CMC_L2_RESTRICT_NULL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`E:real^2->bool`; `E':real^2->bool`;
                   `\j x. wan_wd (:real^2) i ((w:num->real^2->real^K) j) x -
                          partial_derivative i (u:real^2->real^K) x`]
                  CMC_L2_RESTRICT_NULL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness of L^2 limits; L^2 norms over finite covers; rational balls;   *)
(* uniform separation of finite sets.                                        *)
(* ------------------------------------------------------------------------- *)

let CMC_L2CONV_UNIQUE = prove
 (`!E (w:num->real^2->real^K) u1 u2.
     cmc_l2conv E w u1 /\ cmc_l2conv E w u2
     ==> negligible {x | x IN E /\ ~(u1 x = u2 x)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_l2conv] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "A1") (CONJUNCTS_THEN2 (LABEL_TAC "B1") (K ALL_TAC)))
    (CONJUNCTS_THEN2 (LABEL_TAC "A2") (CONJUNCTS_THEN2 (LABEL_TAC "B2") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `(\x. (u1:real^2->real^K) x - u2 x) IN lspace E (&2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. (u1:real^2->real^K) x - u2 x) =
                  (\x. ((w:num->real^2->real^K) 0 x - u2 x) - (w 0 x - u1 x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`E:real^2->bool`; `&2`; `\x. (u1:real^2->real^K) x - u2 x`] LNORM_EQ_0) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
  CONJ_TAC THENL [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  EXISTS_TAC `\j:num. lnorm E (&2) (\x. (u1:real^2->real^K) x - u2 x)` THEN
  EXISTS_TAC `\j. lnorm E (&2) (\x. (w:num->real^2->real^K) j x - u2 x) +
                  lnorm E (&2) (\x. w j x - u1 x)` THEN
  REWRITE_TAC[REALLIM_CONST; TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`sequentially`;
                   `\j. lnorm E (&2) (\x. (w:num->real^2->real^K) j x - u2 x)`;
                   `\j. lnorm E (&2) (\x. (w:num->real^2->real^K) j x - u1 x)`;
                   `&0`; `&0`] REALLIM_ADD) THEN
    ASM_REWRITE_TAC[REAL_ADD_LID];
    ALL_TAC] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. (u1:real^2->real^K) x - u2 x) =
                (\x. ((w:num->real^2->real^K) j x - u2 x) - (w j x - u1 x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lnorm E (&2) (\x. (w:num->real^2->real^K) j x - u2 x) +
              lnorm E (&2) (\x. --(w j x - u1 x))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_SUB] THEN
    MP_TAC(ISPECL [`E:real^2->bool`; `&2`; `\x. (w:num->real^2->real^K) j x + --u2 x`;
                   `\x. --((w:num->real^2->real^K) j x + --u1 x)`] LNORM_TRIANGLE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[GSYM VECTOR_SUB] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LSPACE_NEG THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_LE_LADD] THEN
    MP_TAC(ISPECL [`E:real^2->bool`; `&2`; `\x. (w:num->real^2->real^K) j x - u1 x`]
                  LNORM_NEG) THEN
    REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN(fun th -> REWRITE_TAC[th; REAL_LE_REFL])]);;

(* The square of an L^2 norm is subadditive over finite covers.             *)

let CMC_LNORM_COVER = prove
 (`!K (B:num->real^2->bool) A (f:real^2->real^K).
     FINITE A /\ f IN lspace K (&2) /\ (!m. m IN A ==> f IN lspace (B m) (&2)) /\
     K SUBSET UNIONS (IMAGE B A)
     ==> lnorm K (&2) f pow 2 <= sum A (\m. lnorm (B m) (&2) f pow 2)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ] THEN
  ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral (:real^2)
      (\x. vsum A (\m. if x IN (B:num->real^2->bool) m
                       then lift(norm((f:real^2->real^K) x) pow 2) else vec 0)))` THEN
  SUBGOAL_THEN
   `!m. m IN A
        ==> (\x. if x IN (B:num->real^2->bool) m
                 then lift(norm((f:real^2->real^K) x) pow 2) else vec 0)
            integrable_on (:real^2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTEGRABLE_VSUM THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[DROP_VSUM; o_DEF] THEN
      COND_CASES_TAC THENL
       [SUBGOAL_THEN `?m0. m0 IN A /\ (x:real^2) IN (B:num->real^2->bool) m0`
        STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `K SUBSET UNIONS (IMAGE (B:num->real^2->bool) A)` THEN
          REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`\m. drop(if (x:real^2) IN (B:num->real^2->bool) m
                                 then lift(norm((f:real^2->real^K) x) pow 2) else vec 0)`;
                       `A:num->bool`; `m0:num`] SUM_DELETE) THEN
        ASM_REWRITE_TAC[LIFT_DROP] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> a = b - c ==> c <= b`) THEN
        MATCH_MP_TAC SUM_POS_LE THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP; DROP_VEC; REAL_LE_POW_2; REAL_LE_REFL];
        REWRITE_TAC[DROP_VEC] THEN MATCH_MP_TAC SUM_POS_LE THEN GEN_TAC THEN
        DISCH_TAC THEN REWRITE_TAC[] THEN
        COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP; DROP_VEC; REAL_LE_POW_2; REAL_LE_REFL]]];
    ASM_SIMP_TAC[INTEGRAL_VSUM; DROP_VSUM; o_DEF] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[INTEGRAL_RESTRICT_UNIV] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_SOB_LNORM2_SQ THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let CMC_NULL_COVER = prove
 (`!K (B:num->real^2->bool) A (f:num->real^2->real^K).
     FINITE A /\ (!j. f j IN lspace K (&2)) /\
     (!m. m IN A ==> (!j. f j IN lspace (B m) (&2)) /\
                     ((\j. lnorm (B m) (&2) (f j)) ---> &0) sequentially) /\
     K SUBSET UNIONS (IMAGE B A)
     ==> ((\j. lnorm K (&2) (f j)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_SQ_NULL THEN
  MAP_EVERY EXISTS_TAC [`\j. sum A (\m. lnorm ((B:num->real^2->bool) m) (&2)
                                         ((f:num->real^2->real^K) j) pow 2)`; `&1`] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMC_LNORM_COVER THEN ASM_SIMP_TAC[]];
    SUBGOAL_THEN `&0 = sum A (\m:num. &0)` SUBST1_TAC THENL
     [REWRITE_TAC[SUM_0]; ALL_TAC] THEN
    MP_TAC(ISPECL [`sequentially`;
                   `\m j. lnorm ((B:num->real^2->bool) m) (&2)
                                ((f:num->real^2->real^K) j) pow 2`;
                   `\m:num. &0`; `A:num->bool`] REALLIM_SUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`sequentially`;
                   `\j. lnorm ((B:num->real^2->bool) m) (&2) ((f:num->real^2->real^K) j)`;
                   `2`] REALLIM_NULL_POW) THEN
    ASM_SIMP_TAC[ARITH_EQ]]);;

let CMC_L2CONV_COVER = prove
 (`!K (B:num->real^2->bool) A (w:num->real^2->real^K) u.
     FINITE A /\ (!m. m IN A ==> cmc_l2conv (B m) w u) /\ K SUBSET UNIONS (IMAGE B A) /\
     (!j. (\x. w j x - u x) IN lspace K (&2)) /\
     (!i j. 1 <= i /\ i <= 2
            ==> (\x. wan_wd (:real^2) i (w j) x - partial_derivative i u x)
                IN lspace K (&2))
     ==> cmc_l2conv K w u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cmc_l2conv] THEN ASM_SIMP_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMC_NULL_COVER THEN
    MAP_EVERY EXISTS_TAC [`B:num->real^2->bool`; `A:num->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
      is_forall(concl th) && is_imp(snd(dest_forall(concl th))))) THEN
    ASM_REWRITE_TAC[cmc_l2conv] THEN SIMP_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`K:real^2->bool`; `B:num->real^2->bool`; `A:num->bool`;
                   `\j x. wan_wd (:real^2) i ((w:num->real^2->real^K) j) x -
                          partial_derivative i (u:real^2->real^K) x`] CMC_NULL_COVER) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
      is_forall(concl th) && is_imp(snd(dest_forall(concl th))))) THEN
    ASM_REWRITE_TAC[cmc_l2conv] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Rational balls; separation of finite sets.                                *)
(* ------------------------------------------------------------------------- *)

let CMC_RATIONAL_BALL = prove
 (`!(x:real^2) rho m.
     &0 < rho /\ &1 <= m
     ==> ?c r. (!i. 1 <= i /\ i <= dimindex(:2) ==> rational(c$i)) /\
               rational r /\ &0 < r /\
               x IN ball(c,r / m) /\ ball(c,r) SUBSET ball(x,rho)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&3 * rho / &8`; `rho / &8`] RATIONAL_APPROXIMATION_STRADDLE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `rho / &4 < r /\ r < &3 * rho / &8` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `ball(x:real^2,rho / (&4 * m))` OPEN_SET_RATIONAL_COORDINATES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^2` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`c:real^2`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `dist(x:real^2,c) < rho / (&4 * m)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `rho / (&4 * m) = (rho / &4) / m` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < m` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `rho / (&4 * m) <= rho / &4` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rho / (&4 * m) < r / m` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `y:real^2` THEN
    MP_TAC(ISPECL [`x:real^2`; `c:real^2`; `y:real^2`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC]);;

(* Points of a finite set are uniformly separated.                          *)

let CMC_FINITE_SEPARATED = prove
 (`!X:real^2->bool.
     FINITE X
     ==> ?e. &0 < e /\ !x y. x IN X /\ y IN X /\ ~(x = y) ==> e <= norm(x - y)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = IMAGE (\z:real^2#real^2. norm(FST z - SND z))
                        {z | z IN (X:real^2->bool) CROSS X /\ ~(FST z = SND z)}` THEN
  SUBGOAL_THEN `FINITE(D:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `(X:real^2->bool) CROSS X` THEN ASM_SIMP_TAC[FINITE_CROSS] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN X /\ y IN X /\ ~(x = y) ==> norm(x - y:real^2) IN D`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "D" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `(x:real^2,y:real^2)` THEN ASM_REWRITE_TAC[IN_CROSS; FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN D ==> &0 < t` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `D:real->bool = {}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `D:real->bool` INF_FINITE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `inf(D:real->bool)` THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The regularity constants as one predicate; the local theorem with an      *)
(* eventual energy bound and the conclusion as cmc_l2conv.                   *)
(* ------------------------------------------------------------------------- *)

let cmc_regc = new_definition
 `cmc_regc (S:real^K->bool) (G:real^K->real^K^K) eL (C:num->real) <=>
    &0 < eL /\ (!k. &0 < C k) /\
    (!(a:real^2) r (u:real^2->real^K) l x.
        &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
        wan_gdir (ball(a,r)) G u <= eL /\
        ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ x IN ball(a,r / &2)
        ==> r pow (LENGTH l) * norm(iterated_partial l u x)
            <= C (LENGTH l) * sqrt(wan_gdir (ball(a,r)) G u)) /\
    (!(a:real^2) r (u:real^2->real^K).
        &0 < r /\ cm_cmap S (ball(a,r)) u /\ wan_gdir (ball(a,r)) G u <= eL
        ==> ?w. cm_minimizer S G (ball(a,r)) w /\
                wan_w120 (ball(a,r)) (\x. w x - u x) /\
                cm_cmap S (ball(a,r)) w /\ cm_harmonic S G (ball(a,r)) w /\
                (!x. x IN sphere(a,r) ==> w x = u x))`;;

let CMC_REGC_EXISTS = prove
 (`!S (G:real^K->real^K^K) d.
     CM_EPS_REG_STATEMENT (:K) /\ CM_REPLACEMENT_STATEMENT (:K) /\ cm_target S G d
     ==> ?eL C. cmc_regc S G eL C`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CMC_REP_CONSTS) THEN
  REWRITE_TAC[cmc_regc]);;

let CMC_LOCAL_EV = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0 (w:num->real^2->real^K) eta a R.
     cm_target S G d /\ cmc_regc S G eL C /\
     &0 < e0 /\ e0 <= eL /\ (eta ---> &0) sequentially /\
     (!j. cmc_pmap S (w j) /\ cmc_ah S G e0 (eta j) (w j)) /\
     &0 < R /\ eventually (\j. wan_gdir (ball(a,R)) G (w j) < e0) sequentially
     ==> ?(t:num->num) u. (!m n. m < n ==> t m < t n) /\
                          cm_harmonic S G (ball(a,R / &32)) u /\
                          cmc_l2conv (ball(a,R / &32)) (\j. w (t j)) u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_regc; EVENTUALLY_SEQUENTIALLY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`;
                 `C:num->real`; `e0:real`; `\j. (w:num->real^2->real^K) (N + j)`;
                 `\j. (eta:num->real) (N + j)`; `a:real^2`; `R:real`] CMC_LOCAL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`eta:num->real`; `&0`; `\j:num. N + j`] HMD_REALLIM_SUBSEQ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
      GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` (X_CHOOSE_THEN `u:real^2->real^K`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`\j. N + (t:num->num) j`; `u:real^2->real^K`] THEN
  ASM_REWRITE_TAC[cmc_l2conv; LT_ADD_LCANCEL] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Diagonal subsequences for properties of increasing index sequences        *)
(* (SUBSEQUENCE_DIAGONALIZATION_LEMMA of misc.ml, with the hypotheses only   *)
(* for strictly increasing sequences; same proof, initial sequence I).       *)
(* ------------------------------------------------------------------------- *)

let CMC_DIAG_INC = prove
 (`!P:num->(num->num)->bool.
    (!i (r:num->num). (!m n. m < n ==> r m < r n)
           ==> ?k:num->num. (!m n. m < n ==> k m < k n) /\ P i (r o k)) /\
    (!i (r:num->num) (k1:num->num) (k2:num->num) N.
        (!m n. m < n ==> r m < r n) /\ (!m n. m < n ==> k1 m < k1 n) /\
        (!m n. m < n ==> k2 m < k2 n) /\
        P i (r o k1) /\ (!j. N <= j ==> ?j'. j <= j' /\ k2 j = k1 j')
        ==> P i (r o k2))
    ==> ?k:num->num. (!m n. m < n ==> k m < k n) /\ (!i. P i k)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "MONO")) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:num->(num->num)->num->num` (LABEL_TAC "KK")) THEN
  (STRIP_ASSUME_TAC o prove_recursive_functions_exist num_RECURSION)
    `(rr 0 = (kk:num->(num->num)->num->num) 0 I) /\
     (!n. rr(SUC n) = rr n o kk (SUC n) (I o rr n))` THEN
  SUBGOAL_THEN
   `(!i. (!m n. m < n ==> (rr:num->num->num) i m < rr i n)) /\
    (!i. (P:num->(num->num)->bool) i (I o rr i))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[AND_FORALL_THM] THEN INDUCT_TAC THENL
     [USE_THEN "KK" (MP_TAC o SPECL [`0`; `I:num->num`]) THEN
      REWRITE_TAC[I_THM; I_O_ID] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    POP_ASSUM STRIP_ASSUME_TAC THEN
    USE_THEN "KK" (MP_TAC o SPECL [`SUC i`; `I o (rr:num->num->num) i`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[I_O_ID]; ALL_TAC] THEN
    ASM_REWRITE_TAC[o_ASSOC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[I_O_ID] THEN
    REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j n. i <= j ==> (rr:num->num->num) i n <= rr j n`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [LE_EXISTS] THEN
    SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN SPEC_TAC(`j:num`,`j:num`) THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN SIMP_TAC[FORALL_UNWIND_THM2] THEN
    INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] LE_TRANS)) THEN REWRITE_TAC[o_THM] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (MESON[LE_LT]
       `!f:num->num.
        (!m n. m < n ==> f m < f n) ==> (!m n. m <= n ==> f m <= f n)`) o
       SPEC `i + d:num`) THEN
    SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC MONOTONE_BIGGER THEN
    USE_THEN "KK" (MP_TAC o SPECL [`SUC(i + d)`; `I o (rr:num->num->num) (i + d)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[I_O_ID]; SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `\n. (rr:num->num->num) n n` THEN
  SUBGOAL_THEN `!m n. m < n ==> (\n. (rr:num->num->num) n n) m < (\n. rr n n) n`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `(rr:num->num->num) n m` THEN
    ASM_MESON_TAC[LT_IMP_LE];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!m n i. n <= m ==> ?j. i <= j /\ (rr:num->num->num) m i = rr n j`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `i:num` THEN
    USE_THEN "MONO" (MP_TAC o SPECL [`i:num`; `I:num->num`; `(rr:num->num->num) i`;
                                    `\n. (rr:num->num->num) n n`; `i:num`]) THEN
    REWRITE_TAC[I_O_ID; I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[I_O_ID];
      ASM_MESON_TAC[]]] THEN
  SUBGOAL_THEN
   `!p d i. ?j. i <= j /\ (rr:num->num->num) (p + d) i = rr p j`
   (fun th -> MESON_TAC[LE_EXISTS; th]) THEN
  X_GEN_TAC `p:num` THEN MATCH_MP_TAC num_INDUCTION THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN CONJ_TAC THENL
   [MESON_TAC[LE_REFL]; ALL_TAC] THEN
  X_GEN_TAC `d:num` THEN DISCH_THEN(LABEL_TAC "+") THEN
  X_GEN_TAC `i:num` THEN ASM_REWRITE_TAC[o_THM] THEN
  REMOVE_THEN "+" (MP_TAC o SPEC
   `(kk:num->(num->num)->num->num) (SUC(p + d))
        (I o (rr:num->num->num) (p + d)) i`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:num` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LE_TRANS) THEN
  SPEC_TAC(`i:num`,`i:num`) THEN MATCH_MP_TAC MONOTONE_BIGGER THEN
  USE_THEN "KK" (MP_TAC o SPECL [`SUC(p + d)`; `I o (rr:num->num->num) (p + d)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[I_O_ID]; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Energies of disjoint families; limits of the energies of all rational     *)
(* balls along a subsequence; finiteness of the concentration set.           *)
(* ------------------------------------------------------------------------- *)

let CMC_PEN_UNIONS = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) (B:real^2->real^2->bool) Y.
     cm_target S G d /\ cmc_pmap S w /\ FINITE Y /\
     (!y. y IN Y ==> lebesgue_measurable(B y)) /\
     (!y y'. y IN Y /\ y' IN Y /\ ~(y = y') ==> DISJOINT (B y) (B y'))
     ==> sum Y (\y. cmc_pen G (B y) w) = cmc_pen G (UNIONS (IMAGE B Y)) w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!Y. FINITE Y
        ==> ((!y. y IN Y ==> lebesgue_measurable((B:real^2->real^2->bool) y)) /\
             (!y y'. y IN Y /\ y' IN Y /\ ~(y = y') ==> DISJOINT (B y) (B y'))
             ==> sum Y (\y. cmc_pen G (B y) (w:real^2->real^K)) =
                 cmc_pen G (UNIONS (IMAGE B Y)) w)`
  (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES; IMAGE_CLAUSES; UNIONS_0; cmc_pen; INTEGRAL_EMPTY; DROP_VEC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^2`; `Z:real^2->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_CLAUSES; IMAGE_CLAUSES; UNIONS_INSERT] THEN
  SUBGOAL_THEN `sum Z (\y. cmc_pen G ((B:real^2->real^2->bool) y) (w:real^2->real^K)) =
                cmc_pen G (UNIONS (IMAGE B Z)) w` SUBST1_TAC THENL
   [USE_THEN "IH" MATCH_MP_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMC_PEN_UNION THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    MATCH_MP_TAC LEBESGUE_MEASURABLE_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DISJOINT] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let cmc_rq = new_definition
 `cmc_rq (c:real^2) (r:real) <=>
    (!i. 1 <= i /\ i <= dimindex(:2) ==> rational(c$i)) /\ rational r /\ &0 < r`;;

let CMC_GDIR_BALL_BOUNDS = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) c r.
     cm_target S G d /\ cmc_pmap S w
     ==> &0 <= wan_gdir (ball(c,r)) G w /\
         wan_gdir (ball(c,r)) G w <= wan_gdir (:real^2) G w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_gdir (ball(c,r)) G (w:real^2->real^K) = cmc_pen G (ball(c,r)) w /\
                wan_gdir (:real^2) G w = cmc_pen G (:real^2) w`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC CMC_GDIR_PEN THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_REWRITE_TAC[OPEN_BALL; OPEN_UNIV];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMC_PEN_POS THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL];
    MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL; OPEN_UNIV; SUBSET_UNIV]]);;

let CMC_RBALL_LIMITS = prove
 (`!S (G:real^K->real^K^K) d (w:num->real^2->real^K) E.
     cm_target S G d /\ (!j. cmc_pmap S (w j) /\ wan_gdir (:real^2) G (w j) <= E)
     ==> ?(k:num->num) nu.
           (!m n. m < n ==> k m < k n) /\
           !c r. cmc_rq c r
                 ==> ((\j. wan_gdir (ball(c,r)) G (w (k j))) ---> nu c r) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\j (z:real^(2,1)finite_sum).
                    lift(wan_gdir (ball(fstcart z,drop(sndcart z))) G
                                  ((w:num->real^2->real^K) j))`;
                 `{z:real^(2,1)finite_sum | cmc_rq (fstcart z) (drop(sndcart z))}`; `E:real`]
                FUNCTION_CONVERGENT_SUBSEQUENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_SUBSET THEN
      EXISTS_TAC `{c:real^2 | !i. 1 <= i /\ i <= dimindex(:2) ==> rational(c$i)} PCROSS
                  IMAGE lift rational` THEN
      SIMP_TAC[COUNTABLE_PCROSS; COUNTABLE_RATIONAL_COORDINATES; COUNTABLE_RATIONAL;
               COUNTABLE_IMAGE] THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; IN_ELIM_THM; PASTECART_IN_PCROSS; cmc_rq;
                  FSTCART_PASTECART; SNDCART_PASTECART; IN_IMAGE] THEN
      REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[];
        EXISTS_TAC `drop y` THEN ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[IN]];
      REWRITE_TAC[FORALL_PASTECART; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                  NORM_LIFT] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                     `(w:num->real^2->real^K) n`; `x:real^2`; `drop y`]
                    CMC_GDIR_BALL_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num->num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LIM")) THEN
  SUBGOAL_THEN `!c r. ?L. cmc_rq c r
                          ==> ((\j. wan_gdir (ball(c,r)) G
                                      ((w:num->real^2->real^K) ((k:num->num) j))) ---> L)
                              sequentially`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    USE_THEN "LIM" (MP_TAC o SPEC `pastecart (c:real^2) (lift r)`) THEN
    REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `l:real^1`) THEN EXISTS_TAC `drop l` THEN
    ASM_REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP];
    REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC[]]);;

(* The concentration set is finite.                                           *)

let CMC_CONC_CARD = prove
 (`!S (G:real^K->real^K^K) d (w:num->real^2->real^K) E (k:num->num) nu e0 Y.
     cm_target S G d /\ (!j. cmc_pmap S (w j) /\ wan_gdir (:real^2) G (w j) <= E) /\
     (!c r. cmc_rq c r ==> ((\j. wan_gdir (ball(c,r)) G (w (k j))) ---> nu c r)
                           sequentially) /\
     FINITE Y /\ Y SUBSET {x | !c r. cmc_rq c r /\ x IN ball(c,r) ==> e0 / &2 <= nu c r}
     ==> &(CARD Y) * (e0 / &2) <= E`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `Y:real^2->bool` CMC_FINITE_SEPARATED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y:real^2. ?c r. cmc_rq c r /\ y IN ball(c,r) /\ ball(c,r) SUBSET ball(y,e / &2)`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`y:real^2`; `e / &2`; `&1`] CMC_RATIONAL_BALL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_DIV_1; cmc_rq]] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^2->real^2` (X_CHOOSE_THEN `r:real^2->real`
    (LABEL_TAC "B"))) THEN
  SUBGOAL_THEN `!y y'. y IN Y /\ y' IN Y /\ ~(y = y')
                       ==> DISJOINT (ball((c:real^2->real^2) y,(r:real^2->real) y))
                                    (ball(c y',r y'))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^2`; `y':real^2`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `e <= norm(y - y':real^2)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "B" (MP_TAC o SPEC `y:real^2`) THEN USE_THEN "B" (MP_TAC o SPEC `y':real^2`) THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "B2"))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "B1"))) THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_BALL] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `dist(y:real^2,x) < e / &2 /\ dist(y':real^2,x) < e / &2` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `e <= norm(y - y':real^2)` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum Y (\y. (nu:real^2->real->real) ((c:real^2->real^2) y) ((r:real^2->real) y)) <= E`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
    EXISTS_TAC `\j. sum Y (\y. wan_gdir (ball((c:real^2->real^2) y,(r:real^2->real) y)) G
                                 ((w:num->real^2->real^K) ((k:num->num) j)))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`sequentially`;
                     `\y j. wan_gdir (ball((c:real^2->real^2) y,(r:real^2->real) y)) G
                              ((w:num->real^2->real^K) ((k:num->num) j))`;
                     `\y. (nu:real^2->real->real) ((c:real^2->real^2) y)
                                                  ((r:real^2->real) y)`;
                     `Y:real^2->bool`] REALLIM_SUM) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!y. wan_gdir (ball((c:real^2->real^2) y,(r:real^2->real) y)) G
            ((w:num->real^2->real^K) ((k:num->num) j)) =
          cmc_pen G (ball(c y,r y)) (w (k j))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC CMC_GDIR_PEN THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `(w:num->real^2->real^K) ((k:num->num) j)`;
                   `\y. ball((c:real^2->real^2) y,(r:real^2->real) y)`; `Y:real^2->bool`]
                  CMC_PEN_UNIONS) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_gdir (:real^2) G ((w:num->real^2->real^K) ((k:num->num) j))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `(w:num->real^2->real^K) ((k:num->num) j)`; `(:real^2)`] CMC_GDIR_PEN) THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_UNIV] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; LEBESGUE_MEASURABLE_OPEN; OPEN_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Y (\y. (nu:real^2->real->real) ((c:real^2->real^2) y)
                                                ((r:real^2->real) y))` THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[GSYM SUM_CONST] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  UNDISCH_TAC `Y SUBSET {x | !c r. cmc_rq c r /\ x IN ball(c,r) ==>
                                  e0 / &2 <= (nu:real^2->real->real) c r}` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let CMC_CONC_FINITE = prove
 (`!S (G:real^K->real^K^K) d (w:num->real^2->real^K) E (k:num->num) nu e0.
     cm_target S G d /\ (!j. cmc_pmap S (w j) /\ wan_gdir (:real^2) G (w j) <= E) /\
     &0 < e0 /\
     (!c r. cmc_rq c r ==> ((\j. wan_gdir (ball(c,r)) G (w (k j))) ---> nu c r)
                           sequentially)
     ==> FINITE {x | !c r. cmc_rq c r /\ x IN ball(c,r) ==> e0 / &2 <= nu c r}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `&2 * E / e0` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`SUC n`;
                 `{x | !c r. cmc_rq c r /\ x IN ball(c,r) ==>
                             e0 / &2 <= (nu:real^2->real->real) c r}`]
                CHOOSE_SUBSET_STRONG) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:num->real^2->real^K`;
                 `E:real`; `k:num->num`; `nu:real^2->real->real`; `e0:real`;
                 `Y:real^2->bool`] CMC_CONC_CARD) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&2 * E / e0 <= &n` THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; GSYM REAL_OF_NUM_SUC; REAL_FIELD
   `&0 < e0 ==> &2 * E / e0 = (&2 * E) / e0`] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* L^2 membership of the differences on compact sets; congruence and         *)
(* eventual subsequences for cmc_l2conv.                                     *)
(* ------------------------------------------------------------------------- *)

let CMC_LSPACE_AUTO = prove
 (`!S (w:real^2->real^K) U (u:real^2->real^K) K.
     compact S /\ cmc_pmap S w /\ open U /\ smooth_map_on U u /\ compact K /\ K SUBSET U
     ==> (\x. w x - u x) IN lspace K (&2) /\
         !i. 1 <= i /\ i <= 2
             ==> (\x. wan_wd (:real^2) i w x - partial_derivative i u x) IN lspace K (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_pmap]) THEN
  SUBGOAL_THEN `measurable(K:real^2->bool) /\ lebesgue_measurable(K:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_COMPACT; LEBESGUE_MEASURABLE_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `!g:real^2->real^K. g continuous_on U ==> ?B. !x. x IN K ==> norm(g x) <= B`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^2->real^K`; `K:real^2->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
      REWRITE_TAC[bounded; FORALL_IN_IMAGE]];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "BD") THEN
  SUBGOAL_THEN `?MS. !z:real^K. z IN S ==> norm z <= MS` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IMP_BOUNDED; bounded]; ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "BD" (MP_TAC o SPEC `u:real^2->real^K`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `Bu:real`) THEN
    MP_TAC(ISPECL [`K:real^2->bool`; `\x. (w:real^2->real^K) x - u x`; `MS + Bu`]
                  CMC_BOUNDED_LNORM) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV; ETA_AX];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^2->bool` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; ETA_AX]];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(a:real^K) <= m /\ norm(b:real^K) <= c ==> norm(a - b) <= m + c`) THEN
      ASM_SIMP_TAC[]];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV; ETA_AX] THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `i:num`] CMC_PMAP_WD) THEN
      ASM_SIMP_TAC[];
      USE_THEN "BD" (MP_TAC o SPEC `partial_derivative i (u:real^2->real^K)`) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[CMC_PD_CONTINUOUS]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `Bd:real`) THEN
      SUBGOAL_THEN `partial_derivative i (u:real^2->real^K) measurable_on K` ASSUME_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `U:real^2->bool` THEN ASM_SIMP_TAC[CMC_PD_CONTINUOUS];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`K:real^2->bool`; `partial_derivative i (u:real^2->real^K)`; `Bd:real`]
                    CMC_BOUNDED_LNORM) THEN
      ASM_SIMP_TAC[ETA_AX]]]);;

let CMC_L2CONV_CONG = prove
 (`!E (w:num->real^2->real^K) u u'.
     open E /\ (!x. x IN E ==> u x = u' x) /\ cmc_l2conv E w u ==> cmc_l2conv E w u'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i x. x IN E ==> partial_derivative i (u:real^2->real^K) x =
                                 partial_derivative i u' x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `E:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!j. (\x. (w:num->real^2->real^K) j x - u' x) IN lspace E (&2) <=>
         (\x. w j x - u x) IN lspace E (&2)) /\
    (!j. lnorm E (&2) (\x. (w:num->real^2->real^K) j x - u' x) =
         lnorm E (&2) (\x. w j x - u x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN
    MP_TAC(ISPECL [`E:real^2->bool`; `{}:real^2->bool`;
                   `\x. (w:num->real^2->real^K) j x - u' x`;
                   `\x. (w:num->real^2->real^K) j x - u x`; `&2`] WAN_LSPACE_LNORM_SPIKE) THEN
    ASM_SIMP_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i j. (\x. wan_wd (:real^2) i ((w:num->real^2->real^K) j) x -
                partial_derivative i u' x) IN lspace E (&2) <=>
           (\x. wan_wd (:real^2) i (w j) x - partial_derivative i u x) IN lspace E (&2)) /\
    (!i j. lnorm E (&2) (\x. wan_wd (:real^2) i ((w:num->real^2->real^K) j) x -
                             partial_derivative i u' x) =
           lnorm E (&2) (\x. wan_wd (:real^2) i (w j) x - partial_derivative i u x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`E:real^2->bool`; `{}:real^2->bool`;
                   `\x. wan_wd (:real^2) i ((w:num->real^2->real^K) j) x -
                        partial_derivative i (u':real^2->real^K) x`;
                   `\x. wan_wd (:real^2) i ((w:num->real^2->real^K) j) x -
                        partial_derivative i (u:real^2->real^K) x`; `&2`]
                  WAN_LSPACE_LNORM_SPIKE) THEN
    ASM_SIMP_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY];
    ALL_TAC] THEN
  UNDISCH_TAC `cmc_l2conv E (w:num->real^2->real^K) u` THEN
  ASM_REWRITE_TAC[cmc_l2conv]);;

(* ------------------------------------------------------------------------- *)
(* One subsequence converging on all good balls of a countable family.       *)
(* ------------------------------------------------------------------------- *)

let CMC_MONO_BIGGER = prove
 (`!(r:num->num) n. (!m n. m < n ==> r m < r n) ==> n <= r n`,
  MESON_TAC[MONOTONE_BIGGER]);;

let CMC_GLOBAL_DIAG = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0 (w:num->real^2->real^K) eta
    (k1:num->num) (cc:num->real^2) (rr:num->real).
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < e0 /\ e0 <= eL /\
     (eta ---> &0) sequentially /\
     (!j. cmc_pmap S (w j) /\ cmc_ah S G e0 (eta j) (w j)) /\
     (!m n. m < n ==> k1 m < k1 n)
     ==> ?kk:num->num.
           (!m n. m < n ==> kk m < kk n) /\
           !i. &0 < rr i /\
               eventually (\j. wan_gdir (ball(cc i,rr i)) G (w (k1 j)) < e0) sequentially
               ==> ?u. cm_harmonic S G (ball(cc i,rr i / &32)) u /\
                       cmc_l2conv (ball(cc i,rr i / &64)) (\j. w (k1 (kk j))) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  MATCH_MP_TAC(CMC_DIAG_INC) THEN CONJ_TAC THENL
   [(* existence along any increasing sequence *)
    MAP_EVERY X_GEN_TAC [`i:num`; `q:num->num`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `&0 < (rr:num->real) i /\
                   eventually (\j. wan_gdir (ball((cc:num->real^2) i,rr i)) G
                                     ((w:num->real^2->real^K) ((k1:num->num) j)) < e0)
                              sequentially` THENL
     [ALL_TAC;
      EXISTS_TAC `\n:num. n` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`;
                   `C:num->real`; `e0:real`;
                   `\j. (w:num->real^2->real^K) ((k1:num->num) ((q:num->num) j))`;
                   `\j. (eta:num->real) ((k1:num->num) ((q:num->num) j))`;
                   `(cc:num->real^2) i`; `(rr:num->real) i`] CMC_LOCAL_EV) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`eta:num->real`; `&0`; `\j. (k1:num->num) ((q:num->num) j)`]
                      HMD_REALLIM_SUBSEQ) THEN
        ASM_SIMP_TAC[];
        EXISTS_TAC `N:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(q:num->num) j` THEN
        CONJ_TAC THEN MATCH_MP_TAC CMC_MONO_BIGGER THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:num->num` (X_CHOOSE_THEN `u:real^2->real^K`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `t:num->num` THEN ASM_REWRITE_TAC[o_THM] THEN
    DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC `u:real^2->real^K` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMC_L2CONV_SUBSET THEN
    EXISTS_TAC `ball((cc:num->real^2) i,(rr:num->real) i / &32)` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL] THEN
    MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* stability under eventual subsequences *)
  MAP_EVERY X_GEN_TAC [`i:num`; `q:num->num`; `ka:num->num`; `kb:num->num`; `N:num`] THEN
  STRIP_TAC THEN DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC th) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^2->real^K` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u:real^2->real^K` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!j. (\x. (w:num->real^2->real^K) j x - u x) IN lspace (ball(cc i,rr i / &64)) (&2) /\
        !l. 1 <= l /\ l <= 2
            ==> (\x. wan_wd (:real^2) l (w j) x - partial_derivative l u x)
                IN lspace (ball((cc:num->real^2) i,(rr:num->real) i / &64)) (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `(w:num->real^2->real^K) j`;
                   `ball((cc:num->real^2) i,(rr:num->real) i / &32)`; `u:real^2->real^K`;
                   `cball((cc:num->real^2) i,(rr:num->real) i / &64)`] CMC_LSPACE_AUTO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_BALL; COMPACT_CBALL] THEN CONJ_TAC THENL
       [UNDISCH_TAC `cm_harmonic S G (ball((cc:num->real^2) i,(rr:num->real) i / &32))
                       (u:real^2->real^K)` THEN SIMP_TAC[cm_harmonic];
        REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
        UNDISCH_TAC `&0 < (rr:num->real) i` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN
      EXISTS_TAC `cball((cc:num->real^2) i,(rr:num->real) i / &64)` THEN
      ASM_SIMP_TAC[BALL_SUBSET_CBALL; LEBESGUE_MEASURABLE_OPEN; OPEN_BALL];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN
      EXISTS_TAC `cball((cc:num->real^2) i,(rr:num->real) i / &64)` THEN
      ASM_SIMP_TAC[BALL_SUBSET_CBALL; LEBESGUE_MEASURABLE_OPEN; OPEN_BALL]];
    ALL_TAC] THEN
  UNDISCH_TAC `cmc_l2conv (ball((cc:num->real^2) i,(rr:num->real) i / &64))
                 (\j. (w:num->real^2->real^K) ((k1:num->num) (((q:num->num) o ka) j))) u` THEN
  REWRITE_TAC[cmc_l2conv; o_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\n. lnorm (ball((cc:num->real^2) i,(rr:num->real) i / &64)) (&2)
                         (\x. (w:num->real^2->real^K) ((k1:num->num) ((q:num->num) n)) x -
                              u x)`;
                   `ka:num->num`; `kb:num->num`; `N:num`] CMC_NULL_EVSUB) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:num` o check (is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`\n. lnorm (ball((cc:num->real^2) i,(rr:num->real) i / &64)) (&2)
                         (\x. wan_wd (:real^2) l
                                ((w:num->real^2->real^K) ((k1:num->num) ((q:num->num) n))) x -
                              partial_derivative l (u:real^2->real^K) x)`;
                   `ka:num->num`; `kb:num->num`; `N:num`] CMC_NULL_EVSUB) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* L^2 limits of maps into a closed set stay in it; the global planar        *)
(* compactness theorem (CM Lemma B.23).                                      *)
(* ------------------------------------------------------------------------- *)

let CMC_L2_LIMIT_IN_CLOSED = prove
 (`!E (w:num->real^2->real^K) u TT.
     open E /\ closed TT /\ u continuous_on E /\
     (!j. w j IN lspace E (&2)) /\ (!j. (\x. w j x - u x) IN lspace E (&2)) /\
     (!j x. w j x IN TT) /\
     ((\j. lnorm E (&2) (\x. w j x - u x)) ---> &0) sequentially
     ==> !x. x IN E ==> u x IN TT`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^2->real^K) IN lspace E (&2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(u:real^2->real^K) = (\x. (w:num->real^2->real^K) 0 x - (w 0 x - u x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`E:real^2->bool`; `w:num->real^2->real^K`; `u:real^2->real^K`]
                WAN_L2_AE_SUBSEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->num` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `N:real^2->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `{x | x IN E /\ ~((u:real^2->real^K) x IN TT)} = {}` MP_TAC THENL
   [MATCH_MP_TAC(MESON[OPEN_NOT_NEGLIGIBLE] `open (s:real^2->bool) /\ negligible s ==> s = {}`) THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`u:real^2->real^K`; `E:real^2->bool`; `(:real^K) DIFF TT`]
                    CONTINUOUS_OPEN_IN_PREIMAGE) THEN
      ASM_REWRITE_TAC[GSYM closed] THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
      DISCH_TAC THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
      EXISTS_TAC `E:real^2->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `N:real^2->bool` THEN
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~((u:real^2->real^K) x IN TT)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_IN_CLOSED_SET) THEN
      EXISTS_TAC `\n. (w:num->real^2->real^K) ((q:num->num) n) x` THEN
      ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF]];
    SET_TAC[]]);;

(* The good balls cover the complement of the concentration set.             *)

let CMC_GOOD_COVER = prove
 (`!S (G:real^K->real^K^K) d (w:num->real^2->real^K) (k1:num->num) nu e0 x.
     cm_target S G d /\ (!j. cmc_pmap S (w j)) /\ &0 < e0 /\
     (!c r. cmc_rq c r ==> ((\j. wan_gdir (ball(c,r)) G (w (k1 j))) ---> nu c r)
                           sequentially) /\
     ~(x IN {x | !c r. cmc_rq c r /\ x IN ball(c,r) ==> e0 / &2 <= nu c r})
     ==> ?c r. cmc_rq c r /\ x IN ball(c,r / &64) /\
               eventually (\j. wan_gdir (ball(c,r)) G (w (k1 j)) < e0) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "LIM")
      (X_CHOOSE_THEN `c0:real^2` (X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC)))))) THEN
  MP_TAC(ISPECL [`x:real^2`; `r0 - dist(c0:real^2,x)`; `&64`] CMC_RATIONAL_BALL) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN ball(c0,r0)` THEN REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM cmc_rq] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^2` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ball(c:real^2,r) SUBSET ball(c0,r0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^2,r0 - dist(c0,x))` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    MP_TAC(ISPECL [`c0:real^2`; `x:real^2`] DIST_TRIANGLE) THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[cmc_rq]; ALL_TAC] THEN
  USE_THEN "LIM" (MP_TAC o SPECL [`c0:real^2`; `r0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `e0 / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `wan_gdir (ball(c0:real^2,r0)) G ((w:num->real^2->real^K) ((k1:num->num) j))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `!B. open B ==> wan_gdir B G ((w:num->real^2->real^K) ((k1:num->num) j)) =
                     cmc_pen G B (w (k1 j))`
    (fun th -> SIMP_TAC[th; OPEN_BALL]) THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_GDIR_PEN THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL]];
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The global planar compactness theorem: off a finite set, a subsequence    *)
(* converges in L^2 with first weak partials, on compact sets, to a smooth   *)
(* harmonic map with values in the closed set TT.                            *)
(* ------------------------------------------------------------------------- *)

let CMC_RQ_ENUM = prove
 (`?(cc:num->real^2) (rr:num->real).
     (!i. cmc_rq (cc i) (rr i)) /\ (!c r. cmc_rq c r ==> ?i. cc i = c /\ rr i = r)`,
  MP_TAC(ISPEC `{z:real^(2,1)finite_sum | cmc_rq (fstcart z) (drop(sndcart z))}`
               COUNTABLE_AS_IMAGE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_SUBSET THEN
      EXISTS_TAC `{c:real^2 | !i. 1 <= i /\ i <= dimindex(:2) ==> rational(c$i)} PCROSS
                  IMAGE lift rational` THEN
      SIMP_TAC[COUNTABLE_PCROSS; COUNTABLE_RATIONAL_COORDINATES; COUNTABLE_RATIONAL;
               COUNTABLE_IMAGE] THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; IN_ELIM_THM; PASTECART_IN_PCROSS; cmc_rq;
                  FSTCART_PASTECART; SNDCART_PASTECART; IN_IMAGE] THEN
      REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[];
        EXISTS_TAC `drop y` THEN ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[IN]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `pastecart (vec 0:real^2) (lift(&1))` THEN
      REWRITE_TAC[cmc_rq; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; VEC_COMPONENT;
                  RATIONAL_NUM; REAL_LT_01]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `en:num->real^(2,1)finite_sum`) THEN
  MAP_EVERY EXISTS_TAC [`\i. fstcart((en:num->real^(2,1)finite_sum) i)`;
                        `\i. drop(sndcart((en:num->real^(2,1)finite_sum) i))`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(en:num->real^(2,1)finite_sum) i IN
                  {z | cmc_rq (fstcart z) (drop(sndcart z))}` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[]; SIMP_TAC[IN_ELIM_THM]];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `pastecart (c:real^2) (lift r) IN
                  {z | cmc_rq (fstcart z) (drop(sndcart z))}` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      ASM_REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` (ASSUME_TAC o SYM)) THEN EXISTS_TAC `i:num` THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]]]);;

let CMC_GLOBAL = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0 (w:num->real^2->real^K) eta E TT.
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < e0 /\ e0 <= eL /\
     (eta ---> &0) sequentially /\ closed TT /\ (!j x. w j x IN TT) /\
     (!j. cmc_pmap S (w j) /\ cmc_ah S G e0 (eta j) (w j) /\
          wan_gdir (:real^2) G (w j) <= E)
     ==> ?(t:num->num) U (b:real^2->real^K).
           (!m n. m < n ==> t m < t n) /\ open U /\ FINITE((:real^2) DIFF U) /\
           cm_harmonic S G U b /\ (!x. x IN U ==> b x IN TT) /\
           (!K. compact K /\ K SUBSET U ==> cmc_l2conv K (\j. w (t j)) b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `!j. cmc_pmap S ((w:num->real^2->real^K) j)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `w:num->real^2->real^K`; `E:real`] CMC_RBALL_LIMITS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num->num` (X_CHOOSE_THEN `nu:real^2->real->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LIM")))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `w:num->real^2->real^K`; `E:real`; `k1:num->num`;
                 `nu:real^2->real->real`; `e0:real`] CMC_CONC_FINITE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  X_CHOOSE_THEN `cc:num->real^2` (X_CHOOSE_THEN `rr:num->real` STRIP_ASSUME_TAC)
    CMC_RQ_ENUM THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`;
                 `C:num->real`; `e0:real`; `w:num->real^2->real^K`; `eta:num->real`;
                 `k1:num->num`; `cc:num->real^2`; `rr:num->real`] CMC_GLOBAL_DIAG) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DG"))) THEN
  SUBGOAL_THEN
   `?good:num->bool.
      !i. good i <=> &0 < (rr:num->real) i /\
                     eventually (\j. wan_gdir (ball((cc:num->real^2) i,rr i)) G
                                       ((w:num->real^2->real^K) ((k1:num->num) j)) < e0)
                                sequentially`
  (X_CHOOSE_THEN `good:num->bool` (LABEL_TAC "GOOD")) THENL
   [EXISTS_TAC `\i. &0 < (rr:num->real) i /\
                    eventually (\j. wan_gdir (ball((cc:num->real^2) i,rr i)) G
                                      ((w:num->real^2->real^K) ((k1:num->num) j)) < e0)
                               sequentially` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?uu:num->real^2->real^K.
      !i. good i
          ==> cm_harmonic S G (ball((cc:num->real^2) i,(rr:num->real) i / &32)) (uu i) /\
              cmc_l2conv (ball(cc i,rr i / &64))
                (\j. (w:num->real^2->real^K) ((k1:num->num) ((kk:num->num) j))) (uu i)`
  (X_CHOOSE_THEN `uu:num->real^2->real^K` (LABEL_TAC "UU")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC `i:num` THEN
    DISCH_TAC THEN USE_THEN "DG" MATCH_MP_TAC THEN
    USE_THEN "GOOD" (fun th -> ASM_MESON_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. good i ==> &0 < (rr:num->real) i` ASSUME_TAC THENL
   [USE_THEN "GOOD" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  ABBREV_TAC `U = UNIONS (IMAGE (\i. ball((cc:num->real^2) i,(rr:num->real) i / &64))
                                {i:num | (good:num->bool) i})` THEN
  SUBGOAL_THEN `!x:real^2. x IN U <=> ?i. good i /\ x IN ball(cc i,(rr:num->real) i / &64)`
  ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(U:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC OPEN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL];
    ALL_TAC] THEN
  (* The complement of U lies in the concentration set. *)
  SUBGOAL_THEN `FINITE((:real^2) DIFF U)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{x:real^2 | !c r. cmc_rq c r /\ x IN ball(c,r) ==> e0 / &2 <=
                                  (nu:real^2->real->real) c r}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV] THEN X_GEN_TAC `x:real^2` THEN
    MATCH_MP_TAC(TAUT `(~q ==> p) ==> ~p ==> q`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                   `w:num->real^2->real^K`; `k1:num->num`; `nu:real^2->real->real`;
                   `e0:real`; `x:real^2`] CMC_GOOD_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^2` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^2`; `r:real`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `cmc_rq`)) (concl th) &&
      can (find_term is_exists) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN USE_THEN "GOOD" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[cmc_rq];
    ASM_REWRITE_TAC[]] THEN
  (* Smoothness and continuity of the local limits. *)
  SUBGOAL_THEN
   `!i. good i
        ==> smooth_map_on (ball((cc:num->real^2) i,(rr:num->real) i / &32))
                          ((uu:num->real^2->real^K) i) /\
            (!x. x IN ball(cc i,rr i / &32) ==> uu i x IN S) /\
            ball(cc i,rr i / &64) SUBSET ball(cc i,rr i / &32)`
  (LABEL_TAC "SM") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "UU" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[cm_harmonic]] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN
    ASM_MESON_TAC[REAL_ARITH `&0 < r ==> r / &64 <= r / &32`];
    ALL_TAC] THEN
  (* Consistency of the local limits. *)
  SUBGOAL_THEN
   `!i i' x. good i /\ good i' /\ x IN ball((cc:num->real^2) i,(rr:num->real) i / &64) /\
             x IN ball(cc i',rr i' / &64)
             ==> (uu:num->real^2->real^K) i x = uu i' x`
  (LABEL_TAC "CONS") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ball((cc:num->real^2) i,(rr:num->real) i / &64) INTER
                    ball(cc i',rr i' / &64)`;
                   `(uu:num->real^2->real^K) i`; `(uu:num->real^2->real^K) i'`]
                  HMD_CONT_AE_EQ) THEN
    ANTS_TAC THENL
     [SIMP_TAC[OPEN_INTER; OPEN_BALL] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `ball((cc:num->real^2) i,(rr:num->real) i / &32)` THEN
        USE_THEN "SM" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `ball((cc:num->real^2) i',(rr:num->real) i' / &32)` THEN
        USE_THEN "SM" (MP_TAC o SPEC `i':num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN SET_TAC[];
        MATCH_MP_TAC CMC_L2CONV_UNIQUE THEN
        EXISTS_TAC `\j. (w:num->real^2->real^K) ((k1:num->num) ((kk:num->num) j))` THEN
        CONJ_TAC THEN MATCH_MP_TAC CMC_L2CONV_SUBSET THENL
         [EXISTS_TAC `ball((cc:num->real^2) i,(rr:num->real) i / &64)` THEN
          SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_INTER; OPEN_BALL; INTER_SUBSET] THEN
          USE_THEN "UU" (MP_TAC o SPEC `i:num`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[ETA_AX]];
          EXISTS_TAC `ball((cc:num->real^2) i',(rr:num->real) i' / &64)` THEN
          SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_INTER; OPEN_BALL; INTER_SUBSET] THEN
          USE_THEN "UU" (MP_TAC o SPEC `i':num`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[ETA_AX]]]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  (* The glued map. *)
  ABBREV_TAC `b = \x:real^2. (uu:num->real^2->real^K)
                    (@i. good i /\ x IN ball((cc:num->real^2) i,(rr:num->real) i / &64)) x` THEN
  SUBGOAL_THEN
   `!i x. good i /\ x IN ball((cc:num->real^2) i,(rr:num->real) i / &64)
          ==> (b:real^2->real^K) x = (uu:num->real^2->real^K) i x`
  (LABEL_TAC "BU") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "b" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\i:num. (good:num->bool) i /\ (x:real^2) IN ball((cc:num->real^2) i,(rr:num->real) i / &64)`;
                   `i:num`] SELECT_AX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "CONS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN U ==> ?i r. good i /\ &0 < r /\
                   ball(x,r) SUBSET ball((cc:num->real^2) i,(rr:num->real) i / &64)`
  (LABEL_TAC "LOC") THENL
   [X_GEN_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `ball((cc:num->real^2) i,(rr:num->real) i / &64)` OPEN_CONTAINS_BALL) THEN
    REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\j. (k1:num->num) ((kk:num->num) j)` THEN
  EXISTS_TAC `U:real^2->bool` THEN EXISTS_TAC `b:real^2->real^K` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (b:real^2->real^K) /\ (!x. x IN U ==> b x IN S)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      USE_THEN "LOC" (MP_TAC o SPEC `x:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `ball((cc:num->real^2) i,(rr:num->real) i / &64)` THEN
      REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [UNDISCH_TAC `ball(x:real^2,r) SUBSET ball(cc i,(rr:num->real) i / &64)` THEN
        ASM_SIMP_TAC[SUBSET; CENTRE_IN_BALL];
        ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `(uu:num->real^2->real^K) i` THEN REWRITE_TAC[OPEN_BALL] THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "BU" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        USE_THEN "SM" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MESON_TAC[SMOOTH_MAP_ON_SUBSET]];
      X_GEN_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPECL [`i:num`; `x:real^2`] (ASSUME
       `!i x. good i /\ x IN ball((cc:num->real^2) i,(rr:num->real) i / &64)
              ==> (b:real^2->real^K) x = (uu:num->real^2->real^K) i x`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "SM" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* harmonic *)
    MATCH_MP_TAC CMC_HARMONIC_LOCAL THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "LOC" (MP_TAC o SPEC `x:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC HMD_HARMONIC_CONG THEN EXISTS_TAC `(uu:num->real^2->real^K) i` THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "BU" MATCH_MP_TAC THEN
      ASM SET_TAC[];
      MATCH_MP_TAC HMC_HARMONIC_SUBSET THEN
      EXISTS_TAC `ball((cc:num->real^2) i,(rr:num->real) i / &32)` THEN
      CONJ_TAC THENL [USE_THEN "UU" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]; ALL_TAC] THEN
      USE_THEN "SM" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM SET_TAC[]];
    (* values in TT *)
    X_GEN_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "BU" (MP_TAC o SPECL [`i:num`; `x:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "UU" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[cmc_l2conv]] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ball((cc:num->real^2) i,(rr:num->real) i / &64)`;
                   `\j. (w:num->real^2->real^K) ((k1:num->num) ((kk:num->num) j))`;
                   `(uu:num->real^2->real^K) i`; `TT:real^K->bool`]
                  CMC_L2_LIMIT_IN_CLOSED) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `ball((cc:num->real^2) i,(rr:num->real) i / &32)` THEN
        USE_THEN "SM" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
        X_GEN_TAC `j:num` THEN
        SUBGOAL_THEN `?MS. !z:real^K. z IN S ==> norm z <= MS` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[COMPACT_IMP_BOUNDED; bounded]; ALL_TAC] THEN
        MP_TAC(ISPECL [`ball((cc:num->real^2) i,(rr:num->real) i / &64)`;
                       `(w:num->real^2->real^K) ((k1:num->num) ((kk:num->num) j))`;
                       `MS:real`] CMC_BOUNDED_LNORM) THEN
        ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
        SIMP_TAC[MEASURABLE_BALL] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
          SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
          REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[cmc_pmap];
          ASM_MESON_TAC[cmc_pmap]]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* convergence on compact sets *)
    X_GEN_TAC `K:real^2->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPEC `K:real^2->bool` COMPACT_IMP_HEINE_BOREL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (\i. ball((cc:num->real^2) i,(rr:num->real) i / &64))
                                    {i:num | (good:num->bool) i}`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ff:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\i. ball((cc:num->real^2) i,(rr:num->real) i / &64)`;
                   `{i:num | (good:num->bool) i}`; `ff:(real^2->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `A:num->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC CMC_L2CONV_COVER THEN
    MAP_EVERY EXISTS_TAC [`\i. ball((cc:num->real^2) i,(rr:num->real) i / &64)`;
                          `A:num->bool`] THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(good:num->bool) m` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CMC_L2CONV_CONG THEN EXISTS_TAC `(uu:num->real^2->real^K) m` THEN
      REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "BU" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        USE_THEN "UU" (MP_TAC o SPEC `m:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
      UNDISCH_TAC `K SUBSET UNIONS (ff:(real^2->bool)->bool)` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `j:num` THEN
      MP_TAC(ISPECL [`S:real^K->bool`;
                     `(w:num->real^2->real^K) ((k1:num->num) ((kk:num->num) j))`;
                     `U:real^2->bool`; `b:real^2->real^K`; `K:real^2->bool`]
                    CMC_LSPACE_AUTO) THEN
      ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`l:num`; `j:num`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`S:real^K->bool`;
                     `(w:num->real^2->real^K) ((k1:num->num) ((kk:num->num) j))`;
                     `U:real^2->bool`; `b:real^2->real^K`; `K:real^2->bool`]
                    CMC_LSPACE_AUTO) THEN
      ASM_SIMP_TAC[]]]);;


(* ========================================================================= *)
(* pc_p2a_lbvp: the local boundary value problem for L-geodesics (L11,       *)
(* P2A_LOC_BVP_STATEMENT, proved as P2A_LOC_BVP).  The L-geodesics between   *)
(* nearby points on short s-intervals come from the shooting of pc_p2a_rflow *)
(* (P2A_RSHOOT, P2A_RFLOW_LGEOD) and minimize the L-length by the local      *)
(* convexity of pc_p2a_bvp (P2A_LOCAL_CONVEXITY).                            *)
(*                                                                           *)
(* Preliminaries: the open s-window (P2A_SWINDOW), the margin of a compact   *)
(* set in an open set (P2A_MARGIN), and the uniform bounds of the metric     *)
(* family needed by the convexity estimate (P2A_UNIFORM_BOUNDS).             *)
(* ========================================================================= *)

needs "src/pc_p2a_bvp.ml";;
needs "src/pc_p2a_rflow.ml";;

prioritize_real();;
type_invention_error := true;;

(* Copy of P4_FAMILY_LOWER (pc_p4_width.ml, line 2256), restated here to keep  *)
(* the closure of this unit free of the Part 4 layer.                       *)

let P2A_FAMILY_LOWER = prove
 (`!(G:real^M->real^N^N) S.
        compact S /\ (\z. vectorize(G z)) continuous_on S /\
        (!z v. z IN S /\ ~(v = vec 0) ==> &0 < v dot (G z ** v))
        ==> ?m. &0 < m /\
                !z v. z IN S ==> m * norm v pow 2 <= v dot (G z ** v)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `S:real^M->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\p:real^(M,N)finite_sum.
       sndcart p dot ((G:real^M->real^N^N) (fstcart p) ** sndcart p)`;
    `(S:real^M->bool) PCROSS sphere(vec 0:real^N,&1)`] CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[COMPACT_SPHERE];
      ASM_REWRITE_TAC[PCROSS_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
      REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART]] THEN
      SUBGOAL_THEN
       `(vectorize:real^N^N->real^(N,N)finite_prod) o
        (\p:real^(M,N)finite_sum. (G:real^M->real^N^N) (fstcart p)) =
        (\z. vectorize(G z)) o fstcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^M->bool` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
        SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_PCROSS; FORALL_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^M` (X_CHOOSE_THEN `u0:real^N`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `m = u0 dot ((G:real^M->real^N^N) z0 ** u0)` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `norm(u0:real^N) = &1` THEN
    ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `m:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`z:real^M`; `v:real^N`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `v:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; DOT_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^M`; `inv(norm v) % v:real^N`]) THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; GRGD_QUAD_HOMOG] THEN
  SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `q = v dot ((G:real^M->real^N^N) z ** v)` THEN
  ABBREV_TAC `n = norm(v:real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `q = (inv n * inv n * q) * n pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  ASM_REWRITE_TAC[REAL_MUL_ASSOC]);;


let P2A_SWINDOW = prove
 (`!ta tb tt sa sb.
     &0 <= sa /\ sa <= sb /\ ta < tt - sb pow 2 /\ tt - sa pow 2 < tb
     ==> ?sa' sb'. sa' < sa /\ sb < sb' /\
                   !s. sa' < s /\ s < sb' ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`interval[lift sa,lift sb]`;
                 `{x:real^1 | lift(tt - drop x pow 2) IN
                              {y:real^1 | y$1 <= ta} UNION {y:real^1 | y$1 >= tb}}`]
                SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_INTERVAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
      SIMP_TAC[CLOSED_UNION; CLOSED_HALFSPACE_COMPONENT_LE; CLOSED_HALFSPACE_COMPONENT_GE] THEN
      X_GEN_TAC `x:real^1` THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `lift(--(&2 * drop x))` THEN
      MP_TAC(ISPECL [`tt:real`; `drop x`] P2A_TIME_SQ_VDERIV) THEN REWRITE_TAC[LIFT_DROP];
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM; IN_UNION; IN_INTERVAL_1;
                  LIFT_DROP; GSYM drop] THEN
      X_GEN_TAC `x:real^1` THEN DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      SUBGOAL_THEN `sa pow 2 <= drop x pow 2 /\ drop x pow 2 <= sb pow 2` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`sa - d / &2`; `sb + d / &2`] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`lift(max sa (min sb s))`; `lift s`]) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; IN_ELIM_THM; IN_UNION; DIST_LIFT; GSYM drop] THEN
  ASM_REAL_ARITH_TAC);;

let P2A_MARGIN = prove
 (`!U (Kc:real^N->bool).
     open U /\ compact Kc /\ Kc SUBSET U
     ==> ?r. &0 < r /\ !y. y IN Kc ==> cball(y,r) SUBSET U`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Kc:real^N->bool`; `(:real^N) DIFF U`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[SUBSET; IN_CBALL] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `z:real^N`]) THEN
  ASM_CASES_TAC `(z:real^N) IN U` THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  ASM_REAL_ARITH_TAC);;

let P2A_PARTIAL_EQ = prove
 (`!O (H:real^(1,N)finite_sum->real^P) s v u.
     open O /\ smooth_map_on O H /\ pastecart (lift s) v IN O
     ==> frechet_derivative (\x. H(pastecart (lift s) x)) (at v) u =
         frechet_derivative H (at (pastecart (lift s) v)) (pastecart (vec 0) u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\x. (H:real^(1,N)finite_sum->real^P)(pastecart (lift s) x)) has_derivative
     (\u. frechet_derivative H (at (pastecart (lift s) v)) (pastecart (vec 0) u))) (at v)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`\x:real^N. pastecart (lift s) x`; `H:real^(1,N)finite_sum->real^P`;
                   `\u:real^N. pastecart (vec 0:real^1) u`;
                   `frechet_derivative (H:real^(1,N)finite_sum->real^P) (at (pastecart (lift s) v))`;
                   `v:real^N`] DIFF_CHAIN_AT) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
      MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`; `H:real^(1,N)finite_sum->real^P`]
                    SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_SIMP_TAC[]];
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)])]);;

let P2A_UB_SETUP = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt K a b.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ compact K /\ K SUBSET U /\
     sa < a /\ b < sb
     ==> open(interval(lift sa,lift sb) PCROSS U) /\
         compact(interval[lift a,lift b] PCROSS K) /\
         interval[lift a,lift b] PCROSS K SUBSET interval(lift sa,lift sb) PCROSS U /\
         smooth_map_on (interval(lift sa,lift sb) PCROSS U)
           (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                (Gt(tt - drop(fstcart z) pow 2) (sndcart z))) /\
         smooth_map_on (interval(lift sa,lift sb) PCROSS U)
           (\z. lift(lscalar (Gt(tt - drop(fstcart z) pow 2)) (sndcart z))) /\
         (!s. sa < s /\ s < sb ==> metric_field U (Gt(tt - s pow 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[] o MATCH_MP P2A_LSMOOTH_BASIC) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[] o MATCH_MP P2A_LSMOOTH_LSCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
  REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM SET_TAC[]);;

let P2A_UB_PARTIALS = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt s v u.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < s /\ s < sb /\ v IN U
     ==> vectorize(mderiv (Gt(tt - s pow 2)) v u) =
         frechet_derivative
           (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                (Gt(tt - drop(fstcart z) pow 2) (sndcart z)))
           (at (pastecart (lift s) v)) (pastecart (vec 0) u) /\
         frechet_derivative (\x. lift(lscalar (Gt(tt - s pow 2)) x)) (at v) u =
         frechet_derivative
           (\z. lift(lscalar (Gt(tt - drop(fstcart z) pow 2)) (sndcart z)))
           (at (pastecart (lift s) v)) (pastecart (vec 0) u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `{v:real^N}`; `s:real`; `s:real`] P2A_UB_SETUP) THEN
  ASM_REWRITE_TAC[COMPACT_SING; SING_SUBSET] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (lift s) (v:real^N) IN interval(lift sa,lift sb) PCROSS U`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mderiv; VECTORIZE_MATRIFY] THEN
    MP_TAC(ISPECL [`interval(lift sa,lift sb) PCROSS (U:real^N->bool)`;
                   `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((Gt:real->real^N->real^N^N)(tt - drop(fstcart z) pow 2) (sndcart z))`;
                   `s:real`; `v:real^N`; `u:real^N`] P2A_PARTIAL_EQ) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; o_DEF] THEN
    REWRITE_TAC[ETA_AX];
    MP_TAC(ISPECL [`interval(lift sa,lift sb) PCROSS (U:real^N->bool)`;
                   `\z. lift(lscalar ((Gt:real->real^N->real^N^N)(tt - drop(fstcart z) pow 2))
                                     (sndcart z))`;
                   `s:real`; `v:real^N`; `u:real^N`] P2A_PARTIAL_EQ) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]]);;

let P2A_SEGMENT_SLICE = prove
 (`!(c:real^M) (v:real^N) w K (Is:real^M->bool).
     c IN Is /\ segment[v,w] SUBSET K
     ==> segment[pastecart c v,pastecart c w] SUBSET Is PCROSS K`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_SEGMENT] THEN X_GEN_TAC `z:real^(M,N)finite_sum` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[GSYM PASTECART_CMUL; PASTECART_ADD; PASTECART_IN_PCROSS] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `(&1 - t) % c + t % c:real^M = c`] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN REWRITE_TAC[IN_SEGMENT] THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[]]);;

let P2A_UNIFORM_BOUNDS = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt K a b.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ compact K /\ K SUBSET U /\
     sa < a /\ b < sb
     ==> ?lam B0 B1 BR.
           &0 < lam /\ &0 <= B0 /\ &0 <= B1 /\ &0 <= BR /\
           !s v w u.
             a <= s /\ s <= b /\ segment[v,w] SUBSET K
             ==> lam * norm u pow 2 <= u dot (Gt(tt - s pow 2) w ** u) /\
                 norm(vectorize(Gt(tt - s pow 2) w - Gt(tt - s pow 2) v -
                                mderiv (Gt(tt - s pow 2)) v (w - v)))
                 <= B1 * norm(w - v) pow 2 /\
                 norm(vectorize(mderiv (Gt(tt - s pow 2)) v u)) <= B0 * norm u /\
                 abs(lscalar (Gt(tt - s pow 2)) w - lscalar (Gt(tt - s pow 2)) v -
                     drop(frechet_derivative (\x. lift(lscalar (Gt(tt - s pow 2)) x))
                                             (at v) (w - v)))
                 <= BR * norm(w - v) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `K:real^N->bool`; `a:real`; `b:real`] P2A_UB_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `O = interval(lift sa,lift sb) PCROSS (U:real^N->bool)` THEN
  ABBREV_TAC `S = interval[lift a,lift b] PCROSS (K:real^N->bool)` THEN
  ABBREV_TAC `H = \z:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
                    ((Gt:real->real^N->real^N^N)(tt - drop(fstcart z) pow 2) (sndcart z))` THEN
  ABBREV_TAC `R = \z:real^(1,N)finite_sum.
                    lift(lscalar ((Gt:real->real^N->real^N^N)(tt - drop(fstcart z) pow 2))
                                 (sndcart z))` THEN
  SUBGOAL_THEN `!z:real^(1,N)finite_sum. z IN S
                  ==> z IN O /\ metric_field U ((Gt:real->real^N->real^N^N)(tt - drop(fstcart z) pow 2)) /\
                      sndcart z IN U`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^(1,N)finite_sum) IN O` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:real^(1,N)finite_sum) IN O` THEN
    EXPAND_TAC "O" THEN REWRITE_TAC[GEOL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^(1,N)finite_sum. (Gt:real->real^N->real^N^N)(tt - drop(fstcart z) pow 2)
                                                                     (sndcart z)`;
                 `S:real^(1,N)finite_sum->bool`] P2A_FAMILY_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      MAP_EVERY X_GEN_TAC [`z:real^(1,N)finite_sum`; `y:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(1,N)finite_sum`) THEN ASM_REWRITE_TAC[metric_field] THEN
      ASM_MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`; `S:real^(1,N)finite_sum->bool`; `H:real^(1,N)finite_sum->real^(N,N)finite_prod`]
                GRGE_SMOOTH_TAYLOR1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`; `S:real^(1,N)finite_sum->bool`; `R:real^(1,N)finite_sum->real^1`] GRGE_SMOOTH_TAYLOR1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `BR:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?B0. &0 <= B0 /\
                     !z u. z IN S ==> norm(frechet_derivative (H:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                             (at z) u) <= B0 * norm u`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`; `H:real^(1,N)finite_sum->real^(N,N)finite_prod`] GRGE_SMOOTH_JACOBIAN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `bounded(IMAGE ((vectorize:real^(1,N)finite_sum^(N,N)finite_prod->real^((N,N)finite_prod,(1,N)finite_sum)finite_prod) o
                     (\z. matrix(frechet_derivative (H:real^(1,N)finite_sum->real^(N,N)finite_prod) (at z)))) S)`
    MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `M:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`z:real^(1,N)finite_sum`; `u:real^(1,N)finite_sum`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `linear(frechet_derivative (H:real^(1,N)finite_sum->real^(N,N)finite_prod) (at z))` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `onorm(frechet_derivative (H:real^(1,N)finite_sum->real^(N,N)finite_prod) (at z)) * norm(u:real^(1,N)finite_sum)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[ONORM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((vectorize:real^(1,N)finite_sum^(N,N)finite_prod->real^((N,N)finite_prod,(1,N)finite_sum)finite_prod)
                     (matrix(frechet_derivative (H:real^(1,N)finite_sum->real^(N,N)finite_prod) (at z))))` THEN
    ASM_SIMP_TAC[GRGE_ONORM_LE_VECTORIZE_LINEAR];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `B0:real`; `B1:real`; `BR:real`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `v:real^N`; `w:real^N`; `u:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN K /\ (w:real^N) IN K` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`v:real^N`; `w:real^N`] ENDS_IN_SEGMENT) THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift s) (v:real^N) IN S /\ pastecart (lift s) (w:real^N) IN S /\
                segment[pastecart (lift s) v,pastecart (lift s) w] SUBSET S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC P2A_SEGMENT_SLICE THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sa < s /\ s < sb /\ (v:real^N) IN U` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift s) (v:real^N)` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `O:real^(1,N)finite_sum->bool`)) (concl th) &&
      can (find_term ((=) `S:real^(1,N)finite_sum->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[SNDCART_PASTECART] THEN EXPAND_TAC "O" THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `s:real`; `v:real^N`] P2A_UB_PARTIALS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "partials") THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (lift s) (w:real^N)`; `u:real^N`] o
      check (fun th -> is_forall (concl th) && can (find_term ((=) `lam:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (lift s) (v:real^N)`; `pastecart (lift s) (w:real^N)`] o
      check (fun th -> is_forall (concl th) && can (find_term ((=) `B1:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART_0] THEN
    USE_THEN "partials" (fun th -> REWRITE_TAC[GSYM th]) THEN
    MAP_EVERY EXPAND_TAC ["H"] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; VECTORIZE_SUB];
    FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (lift s) (v:real^N)`; `pastecart (vec 0:real^1) (u:real^N)`] o
      check (fun th -> is_forall (concl th) && can (find_term ((=) `B0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[NORM_PASTECART_0] THEN
    USE_THEN "partials" (fun th -> REWRITE_TAC[GSYM th]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (lift s) (v:real^N)`; `pastecart (lift s) (w:real^N)`] o
      check (fun th -> is_forall (concl th) && can (find_term ((=) `BR:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART_0] THEN
    USE_THEN "partials" (fun th -> REWRITE_TAC[GSYM th]) THEN
    MAP_EVERY EXPAND_TAC ["R"] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= b ==> y <= b`) THEN
    REWRITE_TAC[GSYM NORM_LIFT; LIFT_SUB; LIFT_DROP]]);;


(* ========================================================================= *)
(* Competitor curves (P2A_C1_CURVE), the energy ball (P2A_ENERGY_BALL),      *)
(* local minimality of an L-geodesic among nearby C^1 curves (P2A_LOCAL_MIN, *)
(* from P2A_LOCAL_CONVEXITY with the equality case), constants               *)
(* (P2A_SMALL_POS, P2A_CONVEX_COND), the thickened compact set (P2A_KPRIME)  *)
(* and the properties of the curves obtained from the rescaled flow          *)
(* (P2A_SOL_FACTS).                                                          *)
(* ========================================================================= *)

let P2A_C1_CURVE = prove
 (`!(f:real^1->real^N) s1 s2.
     s1 < s2 /\ continuously_differentiable 1 (interval[lift s1,lift s2]) f
     ==> ?f'. (!x. x IN interval[lift s1,lift s2]
                   ==> (f has_vector_derivative f' x) (at x within interval[lift s1,lift s2])) /\
              f' continuous_on interval[lift s1,lift s2] /\
              (!s. s1 < s /\ s < s2 ==> vector_derivative f (at (lift s)) = f'(lift s))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_CONV `1`; continuously_differentiable] THEN STRIP_TAC THEN
  EXISTS_TAC `\x:real^1. (f':real^1->real^1->real^N) x (vec 1)` THEN
  SUBGOAL_THEN
   `!x. x IN interval[lift s1,lift s2]
        ==> (f has_vector_derivative (f':real^1->real^1->real^N) x (vec 1))
            (at x within interval[lift s1,lift s2])`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
    FIRST_ASSUM(MP_TAC o C MP (ASSUME `(x:real^1) IN interval[lift s1,lift s2]`) o
      SPEC `x:real^1` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative")) (concl th))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `linear((f':real^1->real^1->real^N) x)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[has_derivative] o
        check (fun th -> not(is_forall (concl th)) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative")) (concl th))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\t:real^1. drop t % (f':real^1->real^1->real^N) x (vec 1)) = f' x`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `t:real^1` THEN
      SUBGOAL_THEN `t = drop t % vec 1:real^1`
        (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
       [REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_VEC; REAL_MUL_RID]; ALL_TAC] THEN
      ASM_SIMP_TAC[LINEAR_CMUL];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  SUBGOAL_THEN `lift s IN interval(lift s1,lift s2) /\ lift s IN interval[lift s1,lift s2]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `\t:real^1. drop t % (f':real^1->real^1->real^N) (lift s) (vec 1)`;
                 `lift s`; `interval(lift s1,lift s2)`] HAS_DERIVATIVE_WITHIN_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `interval[lift s1,lift s2]` THEN ASM_REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED]);;

let P2A_ENERGY_BALL = prove
 (`!(z:real^1->real^N) z' s1 s2 E r.
     s1 <= s2 /\
     (!x. x IN interval[lift s1,lift s2]
          ==> (z has_vector_derivative z' x) (at x within interval[lift s1,lift s2])) /\
     z' continuous_on interval[lift s1,lift s2] /\
     real_integral (real_interval[s1,s2]) (\s. norm(z'(lift s)) pow 2) <= E /\
     (s2 - s1) * E <= r pow 2 /\ &0 <= r
     ==> !s. s1 <= s /\ s <= s2 ==> norm(z(lift s) - z(lift s1)) <= r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^1. (z:real^1->real^N) x - z(lift s1)`; `z':real^1->real^N`;
                 `s1:real`; `s2:real`] P2A_WIRTINGER) THEN
  REWRITE_TAC[VECTOR_SUB_REFL] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [VECTOR_ARITH `v:real^N = v - vec 0`] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
    ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_CONST];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[ARITH] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(s2 - s1) * real_integral (real_interval[s1,s2]) (\s. norm((z':real^1->real^N)(lift s)) pow 2)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s2 - s1) * E` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let P2A_LOCAL_MIN = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt sa sb (y:real^1->real^N) A (sig:real^1->real^N)
    s1 s2 C lam B0 B1 BR a0 r0 smax.
     lricci_flow U ta tb Gt /\ p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\
     sa < s1 /\ s1 < s2 /\ s2 < sb /\ convex C /\ C SUBSET U /\
     (!s. s1 <= s /\ s <= s2
          ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ s pow 2 <= smax /\
              y(lift s) IN C /\ sig(lift s) IN C /\
              (y has_vector_derivative A(lift s)) (at (lift s)) /\
              (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s)))
                (at (lift s)) /\
              norm(A(lift s)) <= a0 /\ norm(sig(lift s) - y(lift s)) <= r0) /\
     continuously_differentiable 1 (interval[lift s1,lift s2]) sig /\
     sig(lift s1) = y(lift s1) /\ sig(lift s2) = y(lift s2) /\
     &0 < lam /\ &0 <= B0 /\ &0 <= B1 /\ &0 <= BR /\ &0 <= a0 /\ &0 <= r0 /\ &0 <= smax /\
     (!s v w u. s1 <= s /\ s <= s2 /\ v IN C /\ w IN C
                ==> lam * norm u pow 2 <= u dot (Gt(tt - s pow 2) w ** u) /\
                    norm(vectorize(Gt(tt - s pow 2) w - Gt(tt - s pow 2) v -
                                   mderiv (Gt(tt - s pow 2)) v (w - v))) <=
                    B1 * norm(w - v) pow 2 /\
                    norm(vectorize(mderiv (Gt(tt - s pow 2)) v u)) <= B0 * norm u /\
                    abs(lscalar (Gt(tt - s pow 2)) w - lscalar (Gt(tt - s pow 2)) v -
                        drop(frechet_derivative (\x. lift(lscalar (Gt(tt - s pow 2)) x))
                                                (at v) (w - v))) <=
                    BR * norm(w - v) pow 2) /\
     lam / &4 <= lam / &2 - (B1 * r0 + B0) * a0 * (s2 - s1) -
                 inv(&2) * B1 * a0 pow 2 * (s2 - s1) pow 2 -
                 &2 * smax * BR * (s2 - s1) pow 2
     ==> p2a_cL Gt tt y s1 s2 <= p2a_cL Gt tt sig s1 s2 /\
         (p2a_cL Gt tt y s1 s2 = p2a_cL Gt tt sig s1 s2
          ==> !s. s1 <= s /\ s <= s2 ==> sig(lift s) = y(lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sig:real^1->real^N`; `s1:real`; `s2:real`] P2A_C1_CURVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z':real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `sa:real`; `sb:real`; `y:real^1->real^N`; `A:real^1->real^N`;
                 `sig:real^1->real^N`; `z':real^1->real^N`; `s1:real`; `s2:real`;
                 `C:real^N->bool`; `lam:real`; `B0:real`; `B1:real`; `BR:real`; `a0:real`;
                 `r0:real`; `smax:real`] P2A_LOCAL_CONVEXITY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_cL (Gt:real->real^N->real^N^N) tt y s1 s2 =
    real_integral (real_interval[s1,s2]) (\s. p2a_llag Gt tt s (y(lift s)) (A(lift s))) /\
    p2a_cL Gt tt sig s1 s2 =
    real_integral (real_interval[s1,s2]) (\s. p2a_llag Gt tt s (sig(lift s)) (z'(lift s)))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[p2a_cL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{s1:real,s2}` THEN
      SIMP_TAC[REAL_NEGLIGIBLE_FINITE; FINITE_INSERT; FINITE_EMPTY] THEN
      REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Q = real_integral (real_interval[s1,s2])
                    (\s. norm((z':real^1->real^N)(lift s) - (A:real^1->real^N)(lift s)) pow 2)` THEN
  SUBGOAL_THEN `(A:real^1->real^N) continuous_on interval[lift s1,lift s2]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MP_TAC(ISPECL [`\x:real^1. norm((z':real^1->real^N) x - (A:real^1->real^N) x) pow 2`;
                   `s1:real`; `s2:real`] P2A_REAL_CONT_OF_VEC) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[LIFT_CMUL; REAL_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`lam / &4`; `Q:real`] REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `Q <= &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Q:real`; `&0`; `lam / &4`] REAL_LE_LMUL_EQ) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^1. (sig:real^1->real^N) x - y x`;
                 `\x:real^1. (z':real^1->real^N) x - A x`; `s1:real`; `s2:real`]
                P2A_WIRTINGER) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; VECTOR_SUB_REFL] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
      STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP];
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC[]];
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s2 - s1:real`; `--Q:real`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_RNEG]] THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm((sig:real^1->real^N)(lift s) - y(lift s)) pow 2 = &0` MP_TAC THENL
   [MP_TAC(ISPEC `norm((sig:real^1->real^N)(lift s) - y(lift s))` REAL_LE_POW_2) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_EQ_0; NORM_EQ_0; VECTOR_SUB_EQ; ARITH]]);;

let P2A_SMALL_POS = prove
 (`!K e. &0 <= K /\ &0 < e ==> ?c. &0 < c /\ c <= &1 /\ K * c <= e`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `min (&1) (e / (K + &1))` THEN
  SUBGOAL_THEN `&0 < e / (K + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * e / (K + &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= K ==> &0 < K + &1`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e ==> K * e <= e * (K + &1)`) THEN ASM_REWRITE_TAC[]);;

let P2A_CONVEX_COND = prove
 (`!lam B0 B1 BR r c c' h smax.
     &0 < lam /\ &0 <= B0 /\ &0 <= B1 /\ &0 <= BR /\ &0 <= r /\ &0 <= c' /\ c' <= c /\
     c <= &1 /\ (B1 * &2 * r + B0 + B1) * c <= lam / &12 /\ &0 < h /\ h <= &1 /\
     &0 <= smax /\ (&2 * smax * BR) * h <= lam / &12
     ==> lam / &4 <= lam / &2 - (B1 * (&2 * r) + B0) * (c' / h) * h -
                     inv(&2) * B1 * (c' / h) pow 2 * h pow 2 -
                     &2 * smax * BR * h pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c' / h) * h = c' /\ (c' / h) pow 2 * h pow 2 = c' pow 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_DIV] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(B1 * (&2 * r) + B0) * c' <= lam / &12` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(B1 * &2 * r + B0 + B1) * c` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_ADD) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2) * B1 * c' pow 2 <= lam / &12` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B1 * c` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `c' pow 2 <= c` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c' * &1` THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B1 * c' pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> inv(&2) * x <= x`) THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(B1 * &2 * r + B0 + B1) * c` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> B1 <= a + b + B1`) THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * smax * BR * h pow 2 <= lam / &12` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * smax * BR) * h` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2A_KPRIME = prove
 (`!U (Kc:real^N->bool) r.
     compact Kc /\ &0 < r /\ (!y. y IN Kc ==> cball(y,&2 * r) SUBSET U)
     ==> compact {x + v | x IN Kc /\ v IN cball(vec 0,r)} /\
         {x + v | x IN Kc /\ v IN cball(vec 0,r)} SUBSET U /\
         !y. y IN Kc ==> cball(y,r) SUBSET {x + v | x IN Kc /\ v IN cball(vec 0,r)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL_0] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[SUBSET; IN_CBALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[dist] THEN
    REWRITE_TAC[VECTOR_ARITH `x - (x + v):real^N = --v`; NORM_NEG] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL; IN_CBALL_0] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`y:real^N`; `z - y:real^N`] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `y + (z - y):real^N = z`] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist]]);;

let P2A_SOL_FACTS = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (y1:real^N) V s1 s2 y2 rr
    (y:real^1->real^N) (A:real^1->real^N).
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ y1 IN U /\ sa < s1 /\ s1 < s2 /\ s2 < sb /\
     (!sig. &0 <= sig /\ sig <= &1
            ==> lift sig IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb)
                              (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1)))) /\
                norm(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift sig)
                       (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1)))) -
                     pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))) < rr) /\
     fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift(&1))
                       (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1)))))) = y2 /\
     (\v. fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb)
                 (lift((drop v - s1) / (s2 - s1)))
                 (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1))))))) = y /\
     (\v. inv(s2 - s1) % sndcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb)
                 (lift((drop v - s1) / (s2 - s1)))
                 (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1))))))) = A
     ==> y(lift s1) = y1 /\ y(lift s2) = y2 /\
         !s. s1 <= s /\ s <= s2
             ==> norm(y(lift s) - y1) < rr /\ norm(A(lift s)) * (s2 - s1) < rr /\
                 (y has_vector_derivative A(lift s)) (at (lift s)) /\
                 (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s)))
                   (at (lift s)) /\
                 vector_derivative y (at (lift s)) = A(lift s) /\
                 ((\v. vector_derivative y (at v)) has_vector_derivative
                  p2a_lacc Gt tt s (y(lift s)) (vector_derivative y (at (lift s))))
                 (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `h = s2 - s1` THEN
  SUBGOAL_THEN `&0 < h /\ ~(h = &0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `xx = pastecart (pastecart (y1:real^N) (V:real^N)) (pastecart (lift s1) (lift h))` THEN
  SUBGOAL_THEN `fstcart(fstcart(xx:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)) = y1 /\
                sndcart(fstcart xx) = V`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "xx" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  SUBGOAL_THEN `xx IN p2a_rdom (U:real^N->bool) sa sb` ASSUME_TAC THENL
   [EXPAND_TAC "xx" THEN ASM_REWRITE_TAC[P2A_RDOM_PASTE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `xx:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`] P2A_RFLOW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s2 = s1 + h` ASSUME_TAC THENL [EXPAND_TAC "h" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s'. lift((s' - s1) / h) IN ode_vf_maxint (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                                (p2a_rdom U sa sb) xx
         ==> (y has_vector_derivative (A:real^1->real^N)(lift s')) (at (lift s')) /\
             (A has_vector_derivative p2a_lacc Gt tt s' (y(lift s')) (A(lift s'))) (at (lift s'))`
  (LABEL_TAC "lgeod") THENL
   [X_GEN_TAC `s':real` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["y"; "A"] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `y1:real^N`; `V:real^N`; `s1:real`; `h:real`; `s':real`] P2A_RFLOW_LGEOD) THEN
    REWRITE_TAC[ASSUME `pastecart (pastecart (y1:real^N) (V:real^N)) (pastecart (lift s1) (lift h)) = xx`] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "y" THEN
    REWRITE_TAC[LIFT_DROP; REAL_SUB_REFL; real_div; REAL_MUL_LZERO; LIFT_NUM] THEN
    ASM_REWRITE_TAC[];
    EXPAND_TAC "y" THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (s - s1) / h /\ (s - s1) / h <= &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
    EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(s - s1) / h` o check (fun th -> is_forall (concl th) &&
    can (find_term ((=) `rr:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "lgeod" (MP_TAC o C MP (ASSUME
    `lift((s - s1) / h) IN ode_vf_maxint (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                             (p2a_rdom U sa sb) xx`) o SPEC `s:real`) THEN STRIP_TAC THEN
  ABBREV_TAC `z = ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)
                    (lift((s - s1) / h)) xx` THEN
  SUBGOAL_THEN `(y:real^1->real^N)(lift s) = fstcart(fstcart(z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)) /\
                (A:real^1->real^N)(lift s) = inv h % sndcart(fstcart z)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["y"; "A"] THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `vector_derivative (y:real^1->real^N) (at (lift s)) = A(lift s)` ASSUME_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `fstcart((z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) - pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0)))`
                 NORM_FSTCART) THEN
    MP_TAC(ISPEC `(z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) - pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))`
                 NORM_FSTCART) THEN
    REWRITE_TAC[FSTCART_SUB; FSTCART_PASTECART] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < h ==> abs h = h`] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c = (c * a) * b:real`] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LID] THEN
    MP_TAC(ISPEC `fstcart((z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) - pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0)))`
                 NORM_SNDCART) THEN
    MP_TAC(ISPEC `(z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) - pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))`
                 NORM_FSTCART) THEN
    REWRITE_TAC[FSTCART_SUB; SNDCART_SUB; FSTCART_PASTECART; SNDCART_PASTECART;
                VECTOR_SUB_RZERO] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN EXISTS_TAC `A:real^1->real^N` THEN
  FIRST_ASSUM(MP_TAC o SPEC `lift((s - s1) / h)` o REWRITE_RULE[OPEN_CONTAINS_BALL] o
    check (fun th -> try fst(dest_const(rator(concl th))) = "open" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d * h` THEN CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    USE_THEN "lgeod" (MP_TAC o SPEC `drop v`) THEN REWRITE_TAC[LIFT_DROP] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      (try fst(dest_const(rator(rator(concl th)))) = "SUBSET" with Failure _ -> false) &&
      can (find_term ((=) `d:real`)) (concl th))) THEN
    REWRITE_TAC[IN_BALL; DIST_LIFT] THEN
    SUBGOAL_THEN `(s - s1) / h - (drop v - s1) / h = (s - drop v) / h` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < h ==> abs h = h`; REAL_LT_LDIV_EQ] THEN
    UNDISCH_TAC `dist(v:real^1,lift s) < d * h` THEN
    REWRITE_TAC[dist; NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `A:real^1->real^N`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th) &&
    not(is_forall (concl th)))) THEN
  ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* The L-length of a flow curve as an integral over the unit sigma-interval  *)
(* of the rescaled Lagrangian p2a_rlag (P2A_CL_SIGMA, change of variables s  *)
(* = s1 + h sigma), its continuity on compact sets of initial data           *)
(* (P2A_CLSIG_CONTINUOUS).                                                   *)
(* ========================================================================= *)

let p2a_rlag = new_definition
 `p2a_rlag (Gt:real->real^N->real^N^N) (tt:real)
           (z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum) =
    drop(sndcart(sndcart z)) *
    p2a_llag Gt tt (drop(fstcart(sndcart z))) (fstcart(fstcart z))
             (inv(drop(sndcart(sndcart z))) % sndcart(fstcart z))`;;

let P2A_AFFINE_IMAGE_UNIT = prove
 (`!s1 s2. s1 < s2
           ==> IMAGE (\x. inv(s2 - s1) * (x - s1)) (real_interval[s1,s2]) =
               real_interval[&0,&1]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. inv(s2 - s1) * (x - s1)) = (\x. inv(s2 - s1) * x + --(inv(s2 - s1) * s1))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_AFFINITY_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY] THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_SUB_LE; REAL_LT_IMP_LE;
               REAL_ARITH `s1 < s2 ==> ~(s2 < s1)`] THEN
  SUBGOAL_THEN `inv(s2 - s1) * s1 + --(inv(s2 - s1) * s1) = &0 /\
                inv(s2 - s1) * s2 + --(inv(s2 - s1) * s1) = &1`
  (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `i * (b - a) = &1 ==> i * b + --(i * a) = &1`) THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC]);;

let P2A_CL_SIGMA = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (y1:real^N) V s1 s2 (y:real^1->real^N).
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ y1 IN U /\ sa < s1 /\ s1 < s2 /\ s2 < sb /\
     (!sig. &0 <= sig /\ sig <= &1
            ==> lift sig IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb)
                              (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1))))) /\
     (\v. fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb)
                 (lift((drop v - s1) / (s2 - s1)))
                 (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1))))))) = y
     ==> p2a_cL Gt tt y s1 s2 =
         real_integral (real_interval[&0,&1])
           (\sig. p2a_rlag Gt tt
                    (ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift sig)
                       (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `h = s2 - s1` THEN
  SUBGOAL_THEN `&0 < h /\ ~(h = &0) /\ s2 = s1 + h` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `xx = pastecart (pastecart (y1:real^N) (V:real^N)) (pastecart (lift s1) (lift h))` THEN
  ABBREV_TAC `A = \v. inv h % sndcart(fstcart(ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                       (p2a_rdom U sa sb) (lift((drop v - s1) / h)) xx))` THEN
  SUBGOAL_THEN `xx IN p2a_rdom (U:real^N->bool) sa sb` ASSUME_TAC THENL
   [EXPAND_TAC "xx" THEN ASM_REWRITE_TAC[P2A_RDOM_PASTE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `y1:real^N`; `V:real^N`; `s1:real`; `h:real`] P2A_RFLOW_SH) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `xx:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`] P2A_RFLOW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s2
        ==> (y has_vector_derivative (A:real^1->real^N)(lift s)) (at (lift s)) /\
            y(lift s) IN U`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["y"; "A"] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `y1:real^N`; `V:real^N`; `s1:real`; `h:real`; `s:real`] P2A_RFLOW_LGEOD) THEN
    REWRITE_TAC[ASSUME `pastecart (pastecart (y1:real^N) (V:real^N)) (pastecart (lift s1) (lift h)) = xx`] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `sig:real`)) (concl th))) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `g = \s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((y:real^1->real^N)(lift s))
                               ((A:real^1->real^N)(lift s))` THEN
  SUBGOAL_THEN `p2a_cL (Gt:real->real^N->real^N^N) tt y s1 (s1 + h) =
                real_integral (real_interval[s1,s1 + h]) g`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2a_cL] THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `g real_integrable_on real_interval[s1,s1 + h]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN EXPAND_TAC "g" THEN
    MATCH_MP_TAC P2A_LLAG_CURVE_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `sa:real`; `sb:real`] THEN
    ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
      STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`;
                     `tt:real`; `y1:real^N`; `V:real^N`; `s1:real`; `h:real`; `s:real`]
                    P2A_RFLOW_LGEOD) THEN
      REWRITE_TAC[ASSUME `pastecart (pastecart (y1:real^N) (V:real^N)) (pastecart (lift s1) (lift h)) = xx`] THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `sig:real`)) (concl th))) THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN MESON_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real->real`; `real_integral (real_interval[s1,s1 + h]) g`;
                 `s1:real`; `s1 + h`; `h:real`; `s1:real`] HAS_REAL_INTEGRAL_AFFINITY) THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL] THEN
  MP_TAC(ISPECL [`s1:real`; `s1 + h`] P2A_AFFINE_IMAGE_UNIT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(s1 + h) - s1 = h`] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < h ==> abs h = h`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `real_integral (real_interval[s1,s1 + h]) g =
                h * real_integral (real_interval[&0,&1]) (\x. g(h * x + s1))`
  SUBST1_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `h * real_integral (real_interval[&0,&1]) (\x. g(h * x + s1)) =
                real_integral (real_interval[&0,&1]) (\x. h * g(h * x + s1))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
    REWRITE_TAC[real_integrable_on] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["g"; "y"; "A"] THEN
  REWRITE_TAC[p2a_rlag; LIFT_DROP] THEN
  SUBGOAL_THEN `((h * x + s1) - s1) / h = x` SUBST1_TAC THENL
   [UNDISCH_TAC `~(h = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `sndcart(ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)
                  (lift x) xx) = pastecart (lift(s1 + h * x)) (lift h)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `lift x` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `sndcart:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->real^(1,1)finite_sum`)) (concl th))) THEN
    REWRITE_TAC[ASSUME `pastecart (pastecart (y1:real^N) (V:real^N)) (pastecart (lift s1) (lift h)) = xx`] THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `sig:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_DROP]];
    ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  REWRITE_TAC[REAL_ARITH `h * x + s1 = s1 + h * x`]);;

let P2A_RLAG_CONTINUOUS = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2))
     ==> (\z. lift(p2a_rlag Gt tt z)) continuous_on
         {z | z IN p2a_rdom U sa sb /\ ~(drop(sndcart(sndcart z)) = &0)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `S' = {z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum |
                     z IN p2a_rdom U sa sb /\ ~(drop(sndcart(sndcart z)) = &0)}` THEN
  SUBGOAL_THEN `(\z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum.
                   lift(drop(sndcart(sndcart z)))) continuous_on S'` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    REWRITE_TAC[linear; SNDCART_ADD; SNDCART_CMUL];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_rlag; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  ASM_REWRITE_TAC[o_DEF] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`]
                P2A_LLAG_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum.
       pastecart (fstcart(sndcart z))
                 (pastecart (fstcart(fstcart z))
                            (inv(drop(sndcart(sndcart z))) % sndcart(fstcart z)))`;
    `\z:real^(1,(N,N)finite_sum)finite_sum.
       lift(p2a_llag (Gt:real->real^N->real^N^N) tt (drop(fstcart z)) (fstcart(sndcart z))
                     (sndcart(sndcart z)))`;
    `S':real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool`] CONTINUOUS_ON_COMPOSE) THEN
  REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD;
                                                         FSTCART_CMUL; SNDCART_CMUL];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD;
                                                         FSTCART_CMUL; SNDCART_CMUL];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum.
                         drop(sndcart(sndcart z))`;
                     `S':real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool`] CONTINUOUS_ON_INV) THEN
      ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
      EXPAND_TAC "S'" THEN SIMP_TAC[IN_ELIM_THM];
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD;
                                                         FSTCART_CMUL; SNDCART_CMUL]];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "S'" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; P2A_RDOM_IN; PASTECART_IN_PCROSS;
                IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
    SIMP_TAC[]]);;

let P2A_RFLOW_H = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt x t.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ x IN p2a_rdom U sa sb /\
     t IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) x
     ==> drop(sndcart(sndcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) t x))) =
         drop(sndcart(sndcart x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `x = pastecart (pastecart (fstcart(fstcart x)) (sndcart(fstcart x)))
                              (pastecart (lift(drop(fstcart(sndcart x))))
                                         (lift(drop(sndcart(sndcart x)))))
                :real^((N,N)finite_sum,(1,1)finite_sum)finite_sum`
  SUBST_ALL_TAC THENL [REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `fstcart(fstcart(x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum))`;
                 `sndcart(fstcart(x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum))`;
                 `drop(fstcart(sndcart(x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)))`;
                 `drop(sndcart(sndcart(x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)))`]
                P2A_RFLOW_SH) THEN
  UNDISCH_TAC `pastecart (pastecart (fstcart(fstcart(x:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum)))
                    (sndcart(fstcart x)))
                 (pastecart (lift(drop(fstcart(sndcart x)))) (lift(drop(sndcart(sndcart x))))) IN
               p2a_rdom U sa sb` THEN
  REWRITE_TAC[P2A_RDOM_PASTE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SNDCART_PASTECART; LIFT_DROP]);;

let P2A_CLSIG_CONTINUOUS = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt K.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ compact K /\
     (!x. x IN K ==> x IN p2a_rdom U sa sb /\ ~(drop(sndcart(sndcart x)) = &0) /\
                     lift(&1) IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa sb) x)
     ==> (\x. lift(real_integral (real_interval[&0,&1])
                  (\sig. p2a_rlag Gt tt
                           (ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift sig) x))))
         continuous_on K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x sig. p2a_rlag (Gt:real->real^N->real^N^N) tt
                            (ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa sb) (lift sig) x)`;
                 `&0`; `&1`; `K:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool`]
                P2A_PARAM_REAL_INTEGRAL_CONTINUOUS) THEN
  REWRITE_TAC[LIFT_DROP; REAL_POS; ETA_AX] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`]
                P2A_RFLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum.
       ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb) (fstcart w) (sndcart w)`;
    `\z. lift(p2a_rlag (Gt:real->real^N->real^N^N) tt z)`;
    `interval[lift(&0),lift(&1)] PCROSS (K:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool)`]
   CONTINUOUS_ON_COMPOSE) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `!w. w IN interval[lift(&0),lift(&1)] PCROSS
              (K:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool)
        ==> w IN ode_vf_domain (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum` THEN
    REWRITE_TAC[GEOL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN REWRITE_TAC[P2A_VF_DOMAIN_PASTE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sndcart(w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `sndcart(w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)`;
                   `drop(fstcart(w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum))`]
                  P2A_RFLOW_MAXINT_UNIT) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `ode_vf_domain (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa sb)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `{z | z IN p2a_rdom (U:real^N->bool) sa sb /\ ~(drop(sndcart(sndcart z)) = &0)}` THEN
  ASM_SIMP_TAC[P2A_RLAG_CONTINUOUS] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum`) THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN REWRITE_TAC[P2A_VF_DOMAIN_PASTE] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_FST_SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `sndcart(w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)`]
                P2A_RFLOW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `sndcart(w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)`;
                 `fstcart(w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)`]
                P2A_RFLOW_H) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `w IN interval[lift(&0),lift(&1)] PCROSS
                    (K:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool)` THEN
  REWRITE_TAC[GEOL_IN_PCROSS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sndcart(w:real^(1,((N,N)finite_sum,(1,1)finite_sum)finite_sum)finite_sum)` o
    check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `K:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;


(* ========================================================================= *)
(* One datum of the boundary value problem (P2A_BVP_DATUM): the flow curve   *)
(* with the shooting velocity is an L-geodesic from y1 to y2 in U, and it    *)
(* minimizes the L-length among C^1 curves in U with Euclidean energy at     *)
(* most E, with equality only for the curve itself.                          *)
(* ========================================================================= *)

let P2A_BVP_DATUM = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt Kc E sa sb sa' sb' r lam B0 B1 BR c d1
    s1 s2 (y1:real^N) y2 V (y:real^1->real^N).
     lricci_flow U ta tb Gt /\ p2a_lsmooth U sa' sb' (\s. Gt(tt - s pow 2)) /\
     (!s. sa' < s /\ s < sb' ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb) /\
     sa' < sa /\ sb < sb' /\ &0 <= sa /\ &0 < r /\ &0 < E /\
     (!y. y IN Kc ==> cball(y,&2 * r) SUBSET U) /\
     &0 < lam /\ &0 <= B0 /\ &0 <= B1 /\ &0 <= BR /\
     (!s v w u. sa <= s /\ s <= sb /\
                segment[v,w] SUBSET {x + v | x IN Kc /\ v IN cball(vec 0,r)}
                ==> lam * norm u pow 2 <= u dot (Gt(tt - s pow 2) w ** u) /\
                    norm(vectorize(Gt(tt - s pow 2) w - Gt(tt - s pow 2) v -
                                   mderiv (Gt(tt - s pow 2)) v (w - v)))
                    <= B1 * norm(w - v) pow 2 /\
                    norm(vectorize(mderiv (Gt(tt - s pow 2)) v u)) <= B0 * norm u /\
                    abs(lscalar (Gt(tt - s pow 2)) w - lscalar (Gt(tt - s pow 2)) v -
                        drop(frechet_derivative (\x. lift(lscalar (Gt(tt - s pow 2)) x))
                                                (at v) (w - v)))
                    <= BR * norm(w - v) pow 2) /\
     &0 < c /\ c <= &1 /\ (B1 * &2 * r + B0 + B1) * c <= lam / &12 /\
     &0 < d1 /\ d1 <= &1 /\ (&2 * sb pow 2 * BR) * d1 <= lam / &12 /\
     sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= d1 /\ (s2 - s1) * E <= r pow 2 /\
     y1 IN Kc /\
     (!sig. &0 <= sig /\ sig <= &1
            ==> lift sig IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa' sb')
                              (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1)))) /\
                norm(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa' sb') (lift sig)
                       (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1)))) -
                     pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))) < min r c) /\
     fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa' sb') (lift(&1))
                       (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1)))))) = y2 /\
     (\v. fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa' sb')
                 (lift((drop v - s1) / (s2 - s1)))
                 (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1))))))) = y
     ==> y(lift s1) = y1 /\ y(lift s2) = y2 /\
         (!s. s1 <= s /\ s <= s2 ==> y(lift s) IN U) /\
         (!s. s1 <= s /\ s <= s2
              ==> (y has_vector_derivative vector_derivative y (at (lift s))) (at (lift s)) /\
                  ((\v. vector_derivative y (at v)) has_vector_derivative
                   p2a_lacc Gt tt s (y(lift s)) (vector_derivative y (at (lift s))))
                  (at (lift s))) /\
         !sig'. sig'(lift s1) = y1 /\ sig'(lift s2) = y2 /\
                (!s. s1 <= s /\ s <= s2 ==> sig'(lift s) IN U) /\
                continuously_differentiable 1 (interval[lift s1,lift s2]) sig' /\
                p2a_cE Gt tt sig' s1 s2 <= E
                ==> p2a_cL Gt tt y s1 s2 <= p2a_cL Gt tt sig' s1 s2 /\
                    (p2a_cL Gt tt y s1 s2 = p2a_cL Gt tt sig' s1 s2
                     ==> !s. s1 <= s /\ s <= s2 ==> sig'(lift s) = y(lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y1:real^N) IN U` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `y1:real^N` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `cball:real^N#real->real^N->bool`)) (concl th) &&
      not (can (find_term ((=) `lam:real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa':real`; `sb':real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `y1:real^N`; `V:real^N`; `s1:real`; `s2:real`; `y2:real^N`; `min r c`;
                 `y:real^1->real^N`;
                 `\v. inv(s2 - s1) %
                      sndcart(fstcart(ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                        (p2a_rdom U sa' sb') (lift((drop v - s1) / (s2 - s1)))
                        (pastecart (pastecart (y1:real^N) V) (pastecart (lift s1) (lift(s2 - s1))))))`]
                P2A_SOL_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `A = \v. inv(s2 - s1) %
                      sndcart(fstcart(ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                        (p2a_rdom U sa' sb') (lift((drop v - s1) / (s2 - s1)))
                        (pastecart (pastecart (y1:real^N) V) (pastecart (lift s1) (lift(s2 - s1))))))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sf"))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cball(y1:real^N,r) SUBSET U /\
                cball(y1,r) SUBSET {x + v | x IN Kc /\ v IN cball(vec 0,r)}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(y1:real^N,&2 * r)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL; IN_CBALL_0] THEN X_GEN_TAC `z:real^N` THEN
      DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`y1:real^N`; `z - y1:real^N`] THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `y + (z - y):real^N = z`] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= s2 ==> (y:real^1->real^N)(lift s) IN cball(y1,r)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "sf" (MP_TAC o C MP (CONJ (ASSUME `s1 <= s`) (ASSUME `s <= s2`)) o SPEC `s:real`) THEN
    STRIP_TAC THEN REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "sf" (MP_TAC o C MP (CONJ (ASSUME `s1 <= s`) (ASSUME `s <= s2`)) o SPEC `s:real`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `sig:real^1->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sig:real^1->real^N`; `s1:real`; `s2:real`] P2A_C1_CURVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z':real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `real_integral (real_interval[s1,s2]) (\s. norm((z':real^1->real^N)(lift s)) pow 2)
                <= E` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_cE (Gt:real->real^N->real^N^N) tt sig s1 s2 <= E` THEN
    REWRITE_TAC[p2a_cE] THEN MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= e ==> a <= e`) THEN
    MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{s1:real,s2}` THEN
    SIMP_TAC[REAL_NEGLIGIBLE_FINITE; FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[NORM_POW_2] THEN
    SUBGOAL_THEN `vector_derivative (sig:real^1->real^N) (at (lift s)) = z'(lift s)`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= s2 ==> (sig:real^1->real^N)(lift s) IN cball(y1,r)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sig:real^1->real^N`; `z':real^1->real^N`; `s1:real`; `s2:real`; `E:real`;
                   `r:real`] P2A_ENERGY_BALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `sa':real`; `sb':real`; `y:real^1->real^N`; `A:real^1->real^N`;
                 `sig:real^1->real^N`; `s1:real`; `s2:real`; `cball(y1:real^N,r)`;
                 `lam:real`; `B0:real`; `B1:real`; `BR:real`; `min r c / (s2 - s1)`;
                 `&2 * r`; `sb pow 2`] P2A_LOCAL_MIN) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `sa' < s1 /\ s2 < sb' /\ &0 < s2 - s1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= min r c / (s2 - s1) /\ &0 <= &2 * r /\ &0 <= sb pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s2
        ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ s pow 2 <= sb pow 2 /\
            (y:real^1->real^N)(lift s) IN cball(y1,r) /\
            (sig:real^1->real^N)(lift s) IN cball(y1,r) /\
            (y has_vector_derivative (A:real^1->real^N)(lift s)) (at (lift s)) /\
            (A has_vector_derivative p2a_lacc (Gt:real->real^N->real^N^N) tt s (y(lift s)) (A(lift s)))
              (at (lift s)) /\
            norm(A(lift s)) <= min r c / (s2 - s1) /\
            norm(sig(lift s) - y(lift s)) <= &2 * r`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "sf" (MP_TAC o C MP (CONJ (ASSUME `s1 <= s`) (ASSUME `s <= s2`)) o SPEC `s:real`) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `ta:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `ta:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(y:real^1->real^N)(lift s) IN cball(y1,r) /\
                    (sig:real^1->real^N)(lift s) IN cball(y1,r)` MP_TAC THENL
       [ASM_SIMP_TAC[]; REWRITE_TAC[IN_CBALL] THEN CONV_TAC NORM_ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s v w u. s1 <= s /\ s <= s2 /\ v IN cball(y1:real^N,r) /\ w IN cball(y1,r)
              ==> lam * norm u pow 2 <= u dot ((Gt:real->real^N->real^N^N)(tt - s pow 2) w ** u) /\
                  norm(vectorize(Gt(tt - s pow 2) w - Gt(tt - s pow 2) v -
                                 mderiv (Gt(tt - s pow 2)) v (w - v))) <=
                  B1 * norm(w - v) pow 2 /\
                  norm(vectorize(mderiv (Gt(tt - s pow 2)) v u)) <= B0 * norm u /\
                  abs(lscalar (Gt(tt - s pow 2)) w - lscalar (Gt(tt - s pow 2)) v -
                      drop(frechet_derivative (\x. lift(lscalar (Gt(tt - s pow 2)) x))
                                              (at v) (w - v))) <=
                  BR * norm(w - v) pow 2`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `lam:real`)) (concl th) &&
      can (find_term ((=) `Kc:real^N->bool`)) (concl th))) THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(y1:real^N,r)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `cball(y1:real^N,r)` CONVEX_CONTAINS_SEGMENT) THEN
    REWRITE_TAC[CONVEX_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lam:real`; `B0:real`; `B1:real`; `BR:real`; `r:real`; `c:real`; `min r c`;
                 `s2 - s1`; `sb pow 2`] P2A_CONVEX_COND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * sb pow 2 * BR) * d1` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[CONVEX_CBALL]);;


(* ========================================================================= *)
(* The local boundary value problem for L-geodesics, generic in N            *)
(* (P2A_LOC_BVP_GEN) and the headline instance L11 at N = 3 (P2A_LOC_BVP: |- *)
(* P2A_LOC_BVP_STATEMENT).                                                   *)
(* ========================================================================= *)

let P2A_LOC_BVP_GEN = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt Kc E sa sb.
       p2a_lsmooth U ta tb Gt /\ lricci_flow U ta tb Gt /\
       compact Kc /\ Kc SUBSET U /\ &0 <= sa /\ sa < sb /\
       ta < tt - sb pow 2 /\ tt - sa pow 2 < tb /\ &0 < E
       ==> ?delta rho (sol:real->real->real^N->real^N->real^1->real^N).
             &0 < delta /\ &0 < rho /\
             (!s1 s2 y1 y2.
                sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= delta /\
                y1 IN Kc /\ norm(y2 - y1) <= rho
                ==> sol s1 s2 y1 y2 (lift s1) = y1 /\ sol s1 s2 y1 y2 (lift s2) = y2 /\
                    (!s. s1 <= s /\ s <= s2 ==> sol s1 s2 y1 y2 (lift s) IN U) /\
                    (!s. s1 <= s /\ s <= s2
                         ==> (sol s1 s2 y1 y2 has_vector_derivative
                              vector_derivative (sol s1 s2 y1 y2) (at (lift s)))
                             (at (lift s)) /\
                             ((\v. vector_derivative (sol s1 s2 y1 y2) (at v))
                              has_vector_derivative
                              p2a_lacc Gt tt s (sol s1 s2 y1 y2 (lift s))
                                       (vector_derivative (sol s1 s2 y1 y2) (at (lift s))))
                             (at (lift s))) /\
                    !sig'. sig'(lift s1) = y1 /\ sig'(lift s2) = y2 /\
                           (!s. s1 <= s /\ s <= s2 ==> sig'(lift s) IN U) /\
                           continuously_differentiable 1 (interval[lift s1,lift s2]) sig' /\
                           p2a_cE Gt tt sig' s1 s2 <= E
                           ==> p2a_cL Gt tt (sol s1 s2 y1 y2) s1 s2 <= p2a_cL Gt tt sig' s1 s2 /\
                               (p2a_cL Gt tt (sol s1 s2 y1 y2) s1 s2 = p2a_cL Gt tt sig' s1 s2
                                ==> !s. s1 <= s /\ s <= s2
                                        ==> sig'(lift s) = sol s1 s2 y1 y2 (lift s))) /\
             (!s1 s2 y1 y2 s1n s2n y1n y2n.
                sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= delta /\
                y1 IN Kc /\ norm(y2 - y1) <= rho /\
                (!n:num. sa <= s1n n /\ s1n n < s2n n /\ s2n n <= sb /\
                         s2n n - s1n n <= delta /\ y1n n IN Kc /\
                         norm(y2n n - y1n n) <= rho) /\
                ((\n. lift(s1n n)) --> lift s1) sequentially /\
                ((\n. lift(s2n n)) --> lift s2) sequentially /\
                (y1n --> y1) sequentially /\ (y2n --> y2) sequentially
                ==> ((\n. lift(p2a_cL Gt tt (sol (s1n n) (s2n n) (y1n n) (y2n n))
                                     (s1n n) (s2n n)))
                     --> lift(p2a_cL Gt tt (sol s1 s2 y1 y2) s1 s2)) sequentially)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ta:real`; `tb:real`; `tt:real`; `sa:real`; `sb:real`] P2A_SWINDOW) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sa':real` (X_CHOOSE_THEN `sb':real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `p2a_lsmooth U sa' sb' (\s. (Gt:real->real^N->real^N^N)(tt - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_LSMOOTH_SFAMILY THEN MAP_EVERY EXISTS_TAC [`ta:real`; `tb:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LSMOOTH_BASIC o check (fun th ->
      can (find_term ((=) `ta:real`)) (concl th) &&
      (try fst(dest_const(fst(strip_comb(concl th)))) = "p2a_lsmooth" with Failure _ -> false))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `Kc:real^N->bool`] P2A_MARGIN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = r1 / &2` THEN
  SUBGOAL_THEN `&0 < r /\ !y:real^N. y IN Kc ==> cball(y,&2 * r) SUBSET U` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_SIMP_TAC[REAL_HALF; REAL_ARITH `&2 * r1 / &2 = r1`]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `Kc:real^N->bool`; `r:real`] P2A_KPRIME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa':real`; `sb':real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `{x + v | x IN (Kc:real^N->bool) /\ v IN cball(vec 0:real^N,r)}`;
                 `sa:real`; `sb:real`] P2A_UNIFORM_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `B0:real` (X_CHOOSE_THEN `B1:real`
    (X_CHOOSE_THEN `BR:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`B1 * &2 * r + B0 + B1`; `lam / &12`] P2A_SMALL_POS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE];
    DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`&2 * sb pow 2 * BR`; `lam / &12`] P2A_SMALL_POS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_POW_2];
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa':real`; `sb':real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `Kc:real^N->bool`; `sa:real`; `sb:real`; `min r c`] P2A_RSHOOT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dV:real` (X_CHOOSE_THEN `dh:real` (X_CHOOSE_THEN `rho:real`
    (X_CHOOSE_THEN `Vs:real^N->real^N->real->real->real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "small")
        (CONJUNCTS_THEN2 (LABEL_TAC "exu") (LABEL_TAC "cont")))))))))) THEN
  SUBGOAL_THEN `&0 < r pow 2 / E` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`min dh (min d1 (r pow 2 / E))`; `rho:real`;
    `\s1 s2 (y1:real^N) y2 v.
       fstcart(fstcart(ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa' sb')
         (lift((drop v - s1) / (s2 - s1)))
         (pastecart (pastecart y1 ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                    (pastecart (lift s1) (lift(s2 - s1))))))`] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s1 s2 y1 (y2:real^N).
      sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= min dh (min d1 (r pow 2 / E)) /\
      y1 IN Kc /\ norm(y2 - y1) <= rho
      ==> y1 IN U /\ sa' < s1 /\ s1 < sb' /\ s2 < sb' /\ ~(s2 - s1 = &0) /\
          norm((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)) <= dV /\
          fstcart(fstcart(ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa' sb')
            (lift(&1)) (pastecart (pastecart y1 ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                                  (pastecart (lift s1) (lift(s2 - s1)))))) = y2 /\
          (!sig. &0 <= sig /\ sig <= &1
                 ==> lift sig IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa' sb')
                       (pastecart (pastecart y1 ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                                  (pastecart (lift s1) (lift(s2 - s1)))) /\
                     norm(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa' sb') (lift sig)
                            (pastecart (pastecart y1 ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                                       (pastecart (lift s1) (lift(s2 - s1)))) -
                          pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))) < min r c)`
  (LABEL_TAC "adm") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "exu" (MP_TAC o SPECL [`y1:real^N`; `y2:real^N`; `s1:real`; `s2 - s1`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `y1:real^N` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `&2 * r`)) (concl th))) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `sig:real` THEN STRIP_TAC THEN USE_THEN "small" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s1:real`; `s2:real`; `y1:real^N`; `y2:real^N`] THEN STRIP_TAC THEN
    USE_THEN "adm" (MP_TAC o SPECL [`s1:real`; `s2:real`; `y1:real^N`; `y2:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `Kc:real^N->bool`; `E:real`; `sa:real`; `sb:real`; `sa':real`; `sb':real`;
                   `r:real`; `lam:real`; `B0:real`; `B1:real`; `BR:real`; `c:real`; `d1:real`;
                   `s1:real`; `s2:real`; `y1:real^N`; `y2:real^N`;
                   `(Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)`;
                   `\v. fstcart(fstcart(ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                          (p2a_rdom U sa' sb') (lift((drop v - s1) / (s2 - s1)))
                          (pastecart (pastecart (y1:real^N) ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                                     (pastecart (lift s1) (lift(s2 - s1))))))`]
                  P2A_BVP_DATUM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s1 s2 y1 (y2:real^N).
      sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= min dh (min d1 (r pow 2 / E)) /\
      y1 IN Kc /\ norm(y2 - y1) <= rho
      ==> p2a_cL (Gt:real->real^N->real^N^N) tt
            (\v. fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa' sb')
                   (lift((drop v - s1) / (s2 - s1)))
                   (pastecart (pastecart y1 ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                              (pastecart (lift s1) (lift(s2 - s1))))))) s1 s2 =
          real_integral (real_interval[&0,&1])
            (\sig. p2a_rlag Gt tt (ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa' sb') (lift sig)
                     (pastecart (pastecart y1 ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                                (pastecart (lift s1) (lift(s2 - s1))))))`
  (LABEL_TAC "sigma") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "adm" (MP_TAC o SPECL [`s1:real`; `s2:real`; `y1:real^N`; `y2:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC P2A_CL_SIGMA THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s1:real`; `s2:real`; `y1:real^N`; `y2:real^N`; `s1n:num->real`;
                       `s2n:num->real`; `y1n:num->real^N`; `y2n:num->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN pastecart (pastecart (y1:real^N) ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                       (pastecart (lift s1) (lift(s2 - s1))) INSERT
        IMAGE (\n. pastecart (pastecart ((y1n:num->real^N) n)
                     ((Vs:real^N->real^N->real->real->real^N) (y1n n) ((y2n:num->real^N) n) ((s1n:num->real) n)
                         ((s2n:num->real) n - s1n n)))
                     (pastecart (lift(s1n n)) (lift(s2n n - s1n n)))) (:num)
        ==> z IN p2a_rdom U sa' sb' /\ ~(drop(sndcart(sndcart z)) = &0) /\
            lift(&1) IN ode_vf_maxint (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                          (p2a_rdom U sa' sb') z`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_INSERT; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum` THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THENL
     [USE_THEN "adm" (MP_TAC o SPECL [`s1:real`; `s2:real`; `y1:real^N`; `y2:real^N`]);
      USE_THEN "adm" (MP_TAC o SPECL [`(s1n:num->real) n`; `(s2n:num->real) n`;
                                      `(y1n:num->real^N) n`; `(y2n:num->real^N) n`])] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[P2A_RDOM_PASTE; SNDCART_PASTECART; LIFT_DROP] THEN
    DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(SPEC `&1` (last(CONJUNCTS th)))) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa':real`; `sb':real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `pastecart (pastecart (y1:real^N) ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                            (pastecart (lift s1) (lift(s2 - s1))) INSERT
                  IMAGE (\n. pastecart (pastecart ((y1n:num->real^N) n)
                               ((Vs:real^N->real^N->real->real->real^N) (y1n n) ((y2n:num->real^N) n) ((s1n:num->real) n)
                                   ((s2n:num->real) n - s1n n)))
                               (pastecart (lift(s1n n)) (lift(s2n n - s1n n)))) (:num)`]
                P2A_CLSIG_CONTINUOUS) THEN
  SUBGOAL_THEN
   `((\n. pastecart (pastecart ((y1n:num->real^N) n)
            ((Vs:real^N->real^N->real->real->real^N) (y1n n) ((y2n:num->real^N) n) ((s1n:num->real) n) ((s2n:num->real) n - s1n n)))
            (pastecart (lift(s1n n)) (lift(s2n n - s1n n)))) -->
     pastecart (pastecart (y1:real^N) ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1))) (pastecart (lift s1) (lift(s2 - s1))))
    sequentially`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `((\n. lift((s2n:num->real) n - s1n n)) --> lift(s2 - s1)) sequentially`
    ASSUME_TAC THENL
     [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC LIM_PASTECART THEN CONJ_TAC) THEN ASM_REWRITE_TAC[ETA_AX] THEN
    USE_THEN "cont" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `s1n:num->real`)) (concl th) &&
      can (find_term ((=) `rho:real`)) (concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_SEQUENCE_WITH_LIMIT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\n. pastecart (pastecart ((y1n:num->real^N) n)
            ((Vs:real^N->real^N->real->real->real^N) (y1n n) ((y2n:num->real^N) n) ((s1n:num->real) n) ((s2n:num->real) n - s1n n)))
            (pastecart (lift(s1n n)) (lift(s2n n - s1n n)))`;
    `pastecart (pastecart (y1:real^N) ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1))) (pastecart (lift s1) (lift(s2 - s1)))`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INSERT; IN_IMAGE; IN_UNIV] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC(MESON[] `!(f:num->real^1) g l m.
     f = g /\ l = m ==> (f --> l) sequentially ==> (g --> m) sequentially`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "sigma" MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `s1n:num->real`)) (concl th) &&
      can (find_term ((=) `rho:real`)) (concl th))) THEN
    SIMP_TAC[];
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "sigma" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let P2A_LOC_BVP = prove
 (`P2A_LOC_BVP_STATEMENT`,
  REWRITE_TAC[P2A_LOC_BVP_STATEMENT] THEN MATCH_ACCEPT_TAC P2A_LOC_BVP_GEN);;



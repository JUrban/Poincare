(* ========================================================================= *)
(* Unit pc_cmp_comm (comparison-geometry layer CMP): the curvature           *)
(* commutator D_s D_t Z - D_t D_s Z = R(f_s,f_t) Z for a smooth              *)
(* two-parameter map f and a smooth field Z along it, MFD_COVD_COMMUTATOR,   *)
(* in the form used by pc_geo_iface.ml (the convention of lriemann and       *)
(* mfd_jacobi).  Needs only pc_geo_covd.ml (not pc_geo_iface.ml), so that    *)
(* pc_geo_jacobi can load it.                                                *)
(* ========================================================================= *)

needs "src/pc_geo_covd.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Derivatives along curves of bilinear families (Christoffel symbols at a   *)
(* moving point, applied to moving vectors).                                 *)
(* ========================================================================= *)

(* Expansion of a bilinear map in the standard basis. *)

let CMPC_BILINEAR_EXPAND = prove
 (`!(h:real^N->real^N->real^M) u v.
        bilinear h
        ==> h u v = vsum (1..dimindex(:N))
                      (\i. vsum (1..dimindex(:N))
                             (\j. (u$i * v$j) % h (basis i) (basis j)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^N. (h:real^N->real^N->real^M) x v =
               vsum (1..dimindex(:N)) (\j. v$j % h x (basis j))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN
    MP_TAC(ISPECL [`(h:real^N->real^N->real^M) x`;
                   `\j. (v:real^N)$j % basis j:real^N`;
                   `1..dimindex(:N)`] LINEAR_VSUM) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG] THEN
      UNDISCH_TAC `bilinear (h:real^N->real^N->real^M)` THEN
      SIMP_TAC[bilinear; ETA_AX];
      ALL_TAC] THEN
    REWRITE_TAC[BASIS_EXPANSION; o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC BILINEAR_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. (h:real^N->real^N->real^M) x v`;
                 `\i. (u:real^N)$i % basis i:real^N`;
                 `1..dimindex(:N)`] LINEAR_VSUM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN
    UNDISCH_TAC `bilinear (h:real^N->real^N->real^M)` THEN
    SIMP_TAC[bilinear];
    ALL_TAC] THEN
  REWRITE_TAC[BASIS_EXPANSION; o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP BILINEAR_LMUL th]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM VSUM_LMUL; VECTOR_MUL_ASSOC]);;

(* Coordinates of a curve with a vector derivative. *)

let CMPC_HAS_VD_COMPONENT = prove
 (`!(a:real^1->real^N) a' t i.
        1 <= i /\ i <= dimindex(:N) /\ (a has_vector_derivative a') (at t)
        ==> ((\r. lift(a r$i)) has_vector_derivative lift(a'$i)) (at t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N y:real^N. lift(x dot y)`; `\r:real^1. basis i:real^N`;
                 `a:real^1->real^N`; `vec 0:real^N`; `a':real^N`; `t:real^1`]
    HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_DOT; HAS_VECTOR_DERIVATIVE_CONST] THEN
  ASM_SIMP_TAC[DOT_BASIS; DOT_LZERO; LIFT_NUM; VECTOR_ADD_RID]);;

(* Product rule along a curve for a family of bilinear maps B r: if the      *)
(* family is bilinear near t, differentiable at t for fixed arguments with  *)
(* a bilinear derivative B', and a, b have derivatives a', b', then         *)
(* r |-> B r (a r) (b r) has derivative B'(a,b) + B(a',b) + B(a,b').        *)

let CMPC_BILINEAR_FAMILY_ALONG = prove
 (`!(B:real^1->real^N->real^N->real^M) B' (a:real^1->real^N) (b:real^1->real^N)
    a' b' t d.
        &0 < d /\ (!r. dist(r,t) < d ==> bilinear (B r)) /\ bilinear B' /\
        (!u v. ((\r. B r u v) has_vector_derivative B' u v) (at t)) /\
        (a has_vector_derivative a') (at t) /\
        (b has_vector_derivative b') (at t)
        ==> ((\r. B r (a r) (b r)) has_vector_derivative
             (B' (a t) (b t) + B t a' (b t) + B t (a t) b')) (at t)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC
   `\r. vsum (1..dimindex(:N))
          (\i. vsum (1..dimindex(:N))
                 (\j. ((a:real^1->real^N) r$i * (b:real^1->real^N) r$j) %
                      (B:real^1->real^N->real^N->real^M) r (basis i) (basis j)))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN BETA_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMPC_BILINEAR_EXPAND THEN
    REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `B' ((a:real^1->real^N) t) ((b:real^1->real^N) t) +
    (B:real^1->real^N->real^N->real^M) t a' (b t) + B t (a t) b' =
    vsum (1..dimindex(:N))
      (\i. vsum (1..dimindex(:N))
             (\j. ((a t)$i * (b t)$j) % B' (basis i) (basis j) +
                  ((a':real^N)$i * (b t)$j + (a t)$i * (b':real^N)$j) %
                  B t (basis i) (basis j)))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `bilinear ((B:real^1->real^N->real^N->real^M) t)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[DIST_REFL] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`B':real^N->real^N->real^M`; `(a:real^1->real^N) t`;
                   `(b:real^1->real^N) t`] CMPC_BILINEAR_EXPAND) THEN
    MP_TAC(ISPECL [`(B:real^1->real^N->real^N->real^M) t`; `a':real^N`;
                   `(b:real^1->real^N) t`] CMPC_BILINEAR_EXPAND) THEN
    MP_TAC(ISPECL [`(B:real^1->real^N->real^N->real^M) t`; `(a:real^1->real^N) t`;
                   `b':real^N`] CMPC_BILINEAR_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    REWRITE_TAC[GSYM VSUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[GSYM VSUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    BETA_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC GEOL_HAS_VECTOR_DERIVATIVE_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC GEOL_HAS_VECTOR_DERIVATIVE_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  MP_TAC(ISPECL
   [`\x:real^1 y:real^M. drop x % y`;
    `\r. lift((a:real^1->real^N) r$i * (b:real^1->real^N) r$j)`;
    `\r. (B:real^1->real^N->real^N->real^M) r (basis i) (basis j)`;
    `lift((a':real^N)$i * ((b:real^1->real^N) t)$j +
          ((a:real^1->real^N) t)$i * (b':real^N)$j)`;
    `(B':real^N->real^N->real^M) (basis i) (basis j)`; `t:real^1`]
   HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  REWRITE_TAC[LIFT_DROP; BILINEAR_DROP_MUL] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`\x:real^1 y:real^1. drop x % y`;
      `\r. lift((a:real^1->real^N) r$i)`; `\r. lift((b:real^1->real^N) r$j)`;
      `lift((a':real^N)$i)`; `lift((b':real^N)$j)`; `t:real^1`]
     HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
    REWRITE_TAC[LIFT_DROP; BILINEAR_DROP_MUL] THEN ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC CMPC_HAS_VD_COMPONENT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VECTOR_ADD_SYM]);;

(* Christoffel symbols at a moving point, applied to moving vectors.        *)

let CMPC_CHRISTOFFEL_ALONG = prove
 (`!U (G:real^N->real^N^N) (y:real^1->real^N) (a:real^1->real^N) (b:real^1->real^N)
    y' a' b' t.
        metric_field U G /\ y t IN U /\
        (y has_vector_derivative y') (at t) /\
        (a has_vector_derivative a') (at t) /\
        (b has_vector_derivative b') (at t)
        ==> ((\r. christoffel G (y r) (a r) (b r)) has_vector_derivative
             (frechet_derivative (\z. christoffel G z (a t) (b t)) (at (y t)) y' +
              christoffel G (y t) a' (b t) + christoffel G (y t) (a t) b')) (at t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open (U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\ !r. dist(r,t) < d ==> (y:real^1->real^N) r IN U`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^1->real^N) continuous (at t)` MP_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `y':real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at] THEN
    UNDISCH_TAC `open (U:real^N->bool)` THEN REWRITE_TAC[open_def] THEN
    DISCH_THEN(MP_TAC o SPEC `(y:real^1->real^N) t`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\r. christoffel (G:real^N->real^N^N) ((y:real^1->real^N) r)`;
    `\u v. frechet_derivative (\z. christoffel (G:real^N->real^N^N) z u v)
             (at ((y:real^1->real^N) t)) y'`;
    `a:real^1->real^N`; `b:real^1->real^N`; `a':real^N`; `b':real^N`;
    `t:real^1`; `d:real`] CMPC_BILINEAR_FAMILY_ALONG) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(y:real^1->real^N) t`]
      LRG_DCHRISTOFFEL_LINEAR) THEN
    ASM_REWRITE_TAC[bilinear] THEN STRIP_TAC THEN CONJ_TAC THEN GEN_TAC THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(y:real^1->real^N) t`;
                   `u:real^N`; `v:real^N`] LRG_CHRISTOFFEL_DIFF) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(y:real^1->real^N) t`]
      LRG_DCHRISTOFFEL_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`u:real^N`; `v:real^N`] o
      CONJUNCT1) THEN DISCH_TAC THEN
    UNDISCH_TAC `((y:real^1->real^N) has_vector_derivative y') (at t)` THEN
    REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`y:real^1->real^N`; `\z. christoffel (G:real^N->real^N^N) z u v`;
                   `\x:real^1. drop x % (y':real^N)`;
                   `frechet_derivative (\z. christoffel (G:real^N->real^N^N) z u v)
                      (at ((y:real^1->real^N) t))`; `t:real^1`] DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^1` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th])]);;

(* ========================================================================= *)
(* The coordinate lines of a smooth two-parameter map are C^1 curves, and    *)
(* fields smooth in charts are differentiable along them.                    *)
(* ========================================================================= *)

let CMPC_PAIR_LINE_T = prove
 (`!S0 J (P:real->real->bool) r.
        r IN S0
        ==> {x:real^1 | pastecart (lift r) x IN
                        {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ P s t}} =
            {lift t | t IN J /\ P r t}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; PASTECART_INJ; LIFT_EQ] THEN
  ASM_MESON_TAC[]);;

let CMPC_PAIR_LINE_S = prove
 (`!S0 J (P:real->real->bool) r.
        r IN J
        ==> {x:real^1 | pastecart x (lift r) IN
                        {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ P s t}} =
            {lift s | s IN S0 /\ P s r}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; PASTECART_INJ; LIFT_EQ] THEN
  ASM_MESON_TAC[]);;

(* Restrictions of a smooth map on a set of parameter pairs to the lines.   *)

let CMPC_LINE_T_SMOOTH = prove
 (`!top (f:real->real->A) S0 J (V:A->bool) (H:real^(1,1)finite_sum->real^M) r.
        real_open S0 /\ real_open J /\
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        open_in top V /\
        smooth_map_on {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN V} H /\
        r IN S0
        ==> open {lift t | t IN J /\ f r t IN V} /\
            smooth_map_on {lift t | t IN J /\ f r t IN V} (\x. H(pastecart (lift r) x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `V:A->bool`] GEOC_PAIR_CHART_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S0:real->bool`; `J:real->bool`;
                 `\s t. (f:real->real->A) s t IN V`; `r:real`] CMPC_PAIR_LINE_T) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `!x:real^1. (\x. pastecart (lift r) x) continuous at x` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x:real^1. pastecart (lift r) x`;
                   `{pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                     (f:real->real->A) s t IN V}`] CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^1. (H:real^(1,1)finite_sum->real^M) (pastecart (lift r) x)) =
    H o (\x. pastecart (lift r) x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
               (f:real->real->A) s t IN V}` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x:real^1. pastecart (lift r) x`;
                   `{pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                     (f:real->real->A) s t IN V}`] CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID] THEN
    MP_TAC(ISPECL [`\x:real^1. pastecart (lift r) x`;
                   `{pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                     (f:real->real->A) s t IN V}`] CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    ASM_REWRITE_TAC[]]);;

let CMPC_LINE_S_SMOOTH = prove
 (`!top (f:real->real->A) S0 J (V:A->bool) (H:real^(1,1)finite_sum->real^M) r.
        real_open S0 /\ real_open J /\
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        open_in top V /\
        smooth_map_on {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN V} H /\
        r IN J
        ==> open {lift s | s IN S0 /\ f s r IN V} /\
            smooth_map_on {lift s | s IN S0 /\ f s r IN V} (\x. H(pastecart x (lift r)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `V:A->bool`] GEOC_PAIR_CHART_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S0:real->bool`; `J:real->bool`;
                 `\s t. (f:real->real->A) s t IN V`; `r:real`] CMPC_PAIR_LINE_S) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `!x:real^1. (\x. pastecart x (lift r)) continuous at x` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x:real^1. pastecart x (lift r)`;
                   `{pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                     (f:real->real->A) s t IN V}`] CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^1. (H:real^(1,1)finite_sum->real^M) (pastecart x (lift r))) =
    H o (\x. pastecart x (lift r))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
               (f:real->real->A) s t IN V}` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x:real^1. pastecart x (lift r)`;
                   `{pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                     (f:real->real->A) s t IN V}`] CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID] THEN
    MP_TAC(ISPECL [`\x:real^1. pastecart x (lift r)`;
                   `{pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                     (f:real->real->A) s t IN V}`] CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    ASM_REWRITE_TAC[]]);;

let CMPC_PAIR_IN_TOPSPACE = prove
 (`!top (f:real->real->A) S0 J s t.
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        s IN S0 /\ t IN J
        ==> f s t IN topspace top`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift s) (lift t)` o CONJUNCT1 o
    GEN_REWRITE_RULE I [continuous_map]) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; FSTCART_PASTECART; SNDCART_PASTECART;
              LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* The coordinate lines are C^1 curves on compact subintervals. *)

let CMPC_LINE_T_C1 = prove
 (`!top atlas (f:real->real->A) S0 J r a b.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        real_open S0 /\ real_open J /\
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        (!c. c IN atlas
             ==> smooth_map_on
                   {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                   (\z. SND c (f (drop(fstcart z)) (drop(sndcart z))))) /\
        r IN S0 /\ a <= b /\ real_interval[a,b] SUBSET J
        ==> mfd_c1_curve (top,atlas) (f r) a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_c1_curve] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(f:real->real->A) r =
      (\z. f (drop(fstcart z)) (drop(sndcart z))) o (\x. pastecart (lift r) x) o lift`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J}` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^1)topology` THEN
      SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_LIFT] THEN
      ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; SUBSET_UNIV] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`r:real`; `x:real`] THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `FST(c:(A->bool)#(A->real^N))`;
                 `\z. SND (c:(A->bool)#(A->real^N))
                        ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z)))`;
                 `r:real`] CMPC_LINE_T_SMOOTH) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN(MP_TAC o SPEC `1` o REWRITE_RULE[smooth_map_on] o CONJUNCT2) THEN
  DISCH_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
  EXISTS_TAC `{lift t | t IN J /\ (f:real->real->A) r t IN FST(c:(A->bool)#(A->real^N))}` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
  EXISTS_TAC `drop x` THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  UNDISCH_TAC `x IN interval[lift a,lift b]` THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IN_IMAGE] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ASM SET_TAC[]);;

let CMPC_LINE_S_C1 = prove
 (`!top atlas (f:real->real->A) S0 J r a b.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        real_open S0 /\ real_open J /\
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        (!c. c IN atlas
             ==> smooth_map_on
                   {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                   (\z. SND c (f (drop(fstcart z)) (drop(sndcart z))))) /\
        r IN J /\ a <= b /\ real_interval[a,b] SUBSET S0
        ==> mfd_c1_curve (top,atlas) (\s. f s r) a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_c1_curve] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\s. (f:real->real->A) s r) =
      (\z. f (drop(fstcart z)) (drop(sndcart z))) o (\x. pastecart x (lift r)) o lift`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J}` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^1)topology` THEN
      SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_LIFT] THEN
      ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; SUBSET_UNIV] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:real`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `FST(c:(A->bool)#(A->real^N))`;
                 `\z. SND (c:(A->bool)#(A->real^N))
                        ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z)))`;
                 `r:real`] CMPC_LINE_S_SMOOTH) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN(MP_TAC o SPEC `1` o REWRITE_RULE[smooth_map_on] o CONJUNCT2) THEN
  DISCH_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
  EXISTS_TAC `{lift s | s IN S0 /\ (f:real->real->A) s r IN FST(c:(A->bool)#(A->real^N))}` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
  EXISTS_TAC `drop x` THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  UNDISCH_TAC `x IN interval[lift a,lift b]` THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; IN_IMAGE] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ASM SET_TAC[]);;

(* Fields smooth in all charts are differentiable along the lines. *)

let CMPC_LINE_T_FIELD_DIFF = prove
 (`!top atlas (f:real->real->A) (Z:real->real->real^N) S0 J r.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        real_open S0 /\ real_open J /\
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        (!c. c IN atlas
             ==> smooth_map_on
                  {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                  (\z. chart_jac (chart_at atlas (f (drop(fstcart z)) (drop(sndcart z))))
                                 c (f (drop(fstcart z)) (drop(sndcart z)))
                                 (Z (drop(fstcart z)) (drop(sndcart z))))) /\
        r IN S0
        ==> mfd_field_diff atlas (f r) (Z r) J`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_field_diff; mfd_field_rep] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:real->real->A) r t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPC_PAIR_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`S0:real->bool`; `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(f:real->real->A) r t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) r t)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`;
                 `\z. chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                 ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z))))
                       (c0:(A->bool)#(A->real^N)) (f (drop(fstcart z)) (drop(sndcart z)))
                       ((Z:real->real->real^N) (drop(fstcart z)) (drop(sndcart z)))`;
                 `r:real`] CMPC_LINE_T_SMOOTH) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `{lift t | t IN J /\ (f:real->real->A) r t IN FST(c0:(A->bool)#(A->real^N))}` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `t:real` THEN
  ASM_REWRITE_TAC[]);;

let CMPC_LINE_S_FIELD_DIFF = prove
 (`!top atlas (f:real->real->A) (Z:real->real->real^N) S0 J r.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        real_open S0 /\ real_open J /\
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        (!c. c IN atlas
             ==> smooth_map_on
                  {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                  (\z. chart_jac (chart_at atlas (f (drop(fstcart z)) (drop(sndcart z))))
                                 c (f (drop(fstcart z)) (drop(sndcart z)))
                                 (Z (drop(fstcart z)) (drop(sndcart z))))) /\
        r IN J
        ==> mfd_field_diff atlas (\s. f s r) (\s. Z s r) S0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_field_diff; mfd_field_rep] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:real->real->A) s r IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPC_PAIR_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`S0:real->bool`; `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(f:real->real->A) s r`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) s r)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`;
                 `\z. chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                 ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z))))
                       (c0:(A->bool)#(A->real^N)) (f (drop(fstcart z)) (drop(sndcart z)))
                       ((Z:real->real->real^N) (drop(fstcart z)) (drop(sndcart z)))`;
                 `r:real`] CMPC_LINE_S_SMOOTH) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `{lift s | s IN S0 /\ (f:real->real->A) s r IN FST(c0:(A->bool)#(A->real^N))}` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `s:real` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Chart representatives of the covariant derivatives along the coordinate   *)
(* lines.                                                                    *)
(* ========================================================================= *)

let CMPC_COVD_REP_T = prove
 (`!top atlas (g:A->real^N^N) (f:real->real->A) (Z:real->real->real^N) S0 J c r t.
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\
       real_open S0 /\ is_realinterval S0 /\ real_open J /\ is_realinterval J /\
       continuous_map
         (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
         (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
       (!c. c IN atlas
            ==> smooth_map_on
                  {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                  (\z. SND c (f (drop(fstcart z)) (drop(sndcart z))))) /\
       (!c. c IN atlas
            ==> smooth_map_on
                  {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                  (\z. chart_jac (chart_at atlas (f (drop(fstcart z)) (drop(sndcart z))))
                                 c (f (drop(fstcart z)) (drop(sndcart z)))
                                 (Z (drop(fstcart z)) (drop(sndcart z))))) /\
       c IN atlas /\ r IN S0 /\ t IN J /\ f r t IN FST c
       ==> mfd_field_rep atlas (f r) (mfd_covd atlas g (f r) (Z r)) c t =
           frechet_derivative
             (\z. chart_jac (chart_at atlas (f (drop(fstcart z)) (drop(sndcart z)))) c
                    (f (drop(fstcart z)) (drop(sndcart z)))
                    (Z (drop(fstcart z)) (drop(sndcart z))))
             (at (pastecart (lift r) (lift t))) (pastecart (vec 0) (vec 1)) +
           christoffel (metric_local atlas c g) (SND c (f r t))
             (frechet_derivative (\z. SND c (f (drop(fstcart z)) (drop(sndcart z))))
                (at (pastecart (lift r) (lift t))) (pastecart (vec 0) (vec 1)))
             (chart_jac (chart_at atlas (f r t)) c (f r t) (Z r t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(f:real->real->A) r`; `J:real->bool`;
                 `(Z:real->real->real^N) r`; `c:(A->bool)#(A->real^N)`; `t:real`]
    MFD_COVD_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPC_LINE_T_C1 THEN
      MAP_EVERY EXISTS_TAC [`S0:real->bool`; `J:real->bool`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMPC_LINE_T_FIELD_DIFF THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `S0:real->bool`] THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `Fc = \z. SND (c:(A->bool)#(A->real^N))
                         ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z)))` THEN
  ABBREV_TAC `Wc = \z. chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                    ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z))))
                         (c:(A->bool)#(A->real^N)) (f (drop(fstcart z)) (drop(sndcart z)))
                         ((Z:real->real->real^N) (drop(fstcart z)) (drop(sndcart z)))` THEN
  ABBREV_TAC `Oc = {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                    (f:real->real->A) s t IN FST(c:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN `open (Oc:real^(1,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Oc" THEN MATCH_MP_TAC GEOC_PAIR_CHART_OPEN THEN
    EXISTS_TAC `top:A topology` THEN ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift r) (lift t) IN (Oc:real^(1,1)finite_sum->bool)`
  ASSUME_TAC THENL [EXPAND_TAC "Oc" THEN ASM_REWRITE_TAC[GEOC_IN_PAIR_SET]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on Oc (Fc:real^(1,1)finite_sum->real^N) /\
                smooth_map_on Oc (Wc:real^(1,1)finite_sum->real^N)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Oc"; "Fc"; "Wc"] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. mfd_field_rep atlas ((f:real->real->A) r) ((Z:real->real->real^N) r)
           (c:(A->bool)#(A->real^N)) (drop x)) =
    (\x. Wc(pastecart (lift r) x)) /\
    (\x. SND c (f r (drop x))) = (\x. (Fc:real^(1,1)finite_sum->real^N)(pastecart (lift r) x))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["Wc"; "Fc"] THEN
    REWRITE_TAC[FUN_EQ_THM; mfd_field_rep; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_field_rep] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    MP_TAC(ISPECL [`Wc:real^(1,1)finite_sum->real^N`; `lift r`; `lift t`]
      GEOC_COORD_LINES) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `Oc:real^(1,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    MP_TAC(ISPECL [`Fc:real^(1,1)finite_sum->real^N`; `lift r`; `lift t`]
      GEOC_COORD_LINES) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `Oc:real^(1,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]]]);;

let CMPC_COVD_REP_S = prove
 (`!top atlas (g:A->real^N^N) (f:real->real->A) (Z:real->real->real^N) S0 J c s r.
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\
       real_open S0 /\ is_realinterval S0 /\ real_open J /\ is_realinterval J /\
       continuous_map
         (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
         (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
       (!c. c IN atlas
            ==> smooth_map_on
                  {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                  (\z. SND c (f (drop(fstcart z)) (drop(sndcart z))))) /\
       (!c. c IN atlas
            ==> smooth_map_on
                  {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                  (\z. chart_jac (chart_at atlas (f (drop(fstcart z)) (drop(sndcart z))))
                                 c (f (drop(fstcart z)) (drop(sndcart z)))
                                 (Z (drop(fstcart z)) (drop(sndcart z))))) /\
       c IN atlas /\ s IN S0 /\ r IN J /\ f s r IN FST c
       ==> mfd_field_rep atlas (\s. f s r) (mfd_covd atlas g (\s. f s r) (\s. Z s r)) c s =
           frechet_derivative
             (\z. chart_jac (chart_at atlas (f (drop(fstcart z)) (drop(sndcart z)))) c
                    (f (drop(fstcart z)) (drop(sndcart z)))
                    (Z (drop(fstcart z)) (drop(sndcart z))))
             (at (pastecart (lift s) (lift r))) (pastecart (vec 1) (vec 0)) +
           christoffel (metric_local atlas c g) (SND c (f s r))
             (frechet_derivative (\z. SND c (f (drop(fstcart z)) (drop(sndcart z))))
                (at (pastecart (lift s) (lift r))) (pastecart (vec 1) (vec 0)))
             (chart_jac (chart_at atlas (f s r)) c (f s r) (Z s r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\s. (f:real->real->A) s r`; `S0:real->bool`;
                 `\s. (Z:real->real->real^N) s r`; `c:(A->bool)#(A->real^N)`; `s:real`]
    MFD_COVD_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPC_LINE_S_C1 THEN
      MAP_EVERY EXISTS_TAC [`S0:real->bool`; `J:real->bool`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMPC_LINE_S_FIELD_DIFF THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `Fc = \z. SND (c:(A->bool)#(A->real^N))
                         ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z)))` THEN
  ABBREV_TAC `Wc = \z. chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                    ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z))))
                         (c:(A->bool)#(A->real^N)) (f (drop(fstcart z)) (drop(sndcart z)))
                         ((Z:real->real->real^N) (drop(fstcart z)) (drop(sndcart z)))` THEN
  ABBREV_TAC `Oc = {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                    (f:real->real->A) s t IN FST(c:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN `open (Oc:real^(1,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Oc" THEN MATCH_MP_TAC GEOC_PAIR_CHART_OPEN THEN
    EXISTS_TAC `top:A topology` THEN ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift s) (lift r) IN (Oc:real^(1,1)finite_sum->bool)`
  ASSUME_TAC THENL [EXPAND_TAC "Oc" THEN ASM_REWRITE_TAC[GEOC_IN_PAIR_SET]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on Oc (Fc:real^(1,1)finite_sum->real^N) /\
                smooth_map_on Oc (Wc:real^(1,1)finite_sum->real^N)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Oc"; "Fc"; "Wc"] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. mfd_field_rep atlas (\s. (f:real->real->A) s r) (\s. (Z:real->real->real^N) s r)
           (c:(A->bool)#(A->real^N)) (drop x)) =
    (\x. Wc(pastecart x (lift r))) /\
    (\x. SND c ((\s. f s r) (drop x))) =
    (\x. (Fc:real^(1,1)finite_sum->real^N)(pastecart x (lift r)))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["Wc"; "Fc"] THEN
    REWRITE_TAC[FUN_EQ_THM; mfd_field_rep; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_field_rep] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    MP_TAC(ISPECL [`Wc:real^(1,1)finite_sum->real^N`; `lift s`; `lift r`]
      GEOC_COORD_LINES) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `Oc:real^(1,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    MP_TAC(ISPECL [`Fc:real^(1,1)finite_sum->real^N`; `lift s`; `lift r`]
      GEOC_COORD_LINES) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `Oc:real^(1,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]]]);;

(* ========================================================================= *)
(* The curvature commutator MFD_COVD_COMMUTATOR.                             *)
(* ========================================================================= *)

let MFD_COVD_COMMUTATOR = prove
 (`!top atlas (g:A->real^N^N) (f:real->real->A) (Z:real->real->real^N) S0 J s t.
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\
       real_open S0 /\ is_realinterval S0 /\ real_open J /\ is_realinterval J /\
       continuous_map
         (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
         (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
       (!c. c IN atlas
            ==> smooth_map_on
                  {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                  (\z. SND c (f (drop(fstcart z)) (drop(sndcart z))))) /\
       (!c. c IN atlas
            ==> smooth_map_on
                  {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                  (\z. chart_jac (chart_at atlas (f (drop(fstcart z)) (drop(sndcart z))))
                                 c (f (drop(fstcart z)) (drop(sndcart z)))
                                 (Z (drop(fstcart z)) (drop(sndcart z))))) /\
       s IN S0 /\ t IN J
       ==> mfd_covd atlas g (\s'. f s' t) (\s'. mfd_covd atlas g (f s') (Z s') t) s -
           mfd_covd atlas g (f s) (\t'. mfd_covd atlas g (\s'. f s' t') (\s'. Z s' t') s) t =
           mfd_riemann atlas g (f s t) (mfd_vel atlas (\s'. f s' t) s)
                       (mfd_vel atlas (f s) t) (Z s t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real->real->A) s t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPC_PAIR_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`S0:real->bool`; `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(f:real->real->A) s t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) s t)` THEN
  STRIP_TAC THEN
  ABBREV_TAC `O0 = {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                    (f:real->real->A) s t IN FST(c0:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN `open (O0:real^(1,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O0" THEN MATCH_MP_TAC GEOC_PAIR_CHART_OPEN THEN
    EXISTS_TAC `top:A topology` THEN ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift s) (lift t) IN (O0:real^(1,1)finite_sum->bool)`
  ASSUME_TAC THENL [EXPAND_TAC "O0" THEN ASM_REWRITE_TAC[GEOC_IN_PAIR_SET]; ALL_TAC] THEN
  ABBREV_TAC `F0 = \z. SND (c0:(A->bool)#(A->real^N))
                         ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z)))` THEN
  ABBREV_TAC `W0 = \z. chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                    ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z))))
                         (c0:(A->bool)#(A->real^N)) (f (drop(fstcart z)) (drop(sndcart z)))
                         ((Z:real->real->real^N) (drop(fstcart z)) (drop(sndcart z)))` THEN
  SUBGOAL_THEN `smooth_map_on O0 (F0:real^(1,1)finite_sum->real^N) /\
                smooth_map_on O0 (W0:real^(1,1)finite_sum->real^N)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["O0"; "F0"; "W0"] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`O0:real^(1,1)finite_sum->bool`; `s:real`; `t:real`] GEOC_PAIR_NEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ns") (LABEL_TAC "nt")))) THEN
  ABBREV_TAC `e1 = pastecart (vec 1:real^1) (vec 0:real^1)` THEN
  ABBREV_TAC `e2 = pastecart (vec 0:real^1) (vec 1:real^1)` THEN
  ABBREV_TAC `G0 = metric_local (atlas:((A->bool)#(A->real^N))->bool)
                     (c0:(A->bool)#(A->real^N)) (g:A->real^N^N)` THEN
  ABBREV_TAC `U0 = IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` THEN
  SUBGOAL_THEN `metric_field (U0:real^N->bool) (G0:real^N->real^N^N)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U0"; "G0"] THEN
    UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `c0:(A->bool)#(A->real^N)`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN O0 ==> (F0:real^(1,1)finite_sum->real^N) z IN U0`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["O0"; "F0"; "U0"] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* point values in the chart c0 *)
  SUBGOAL_THEN
   `!r q. (F0:real^(1,1)finite_sum->real^N) (pastecart (lift r) (lift q)) =
          SND (c0:(A->bool)#(A->real^N)) ((f:real->real->A) r q) /\
          (W0:real^(1,1)finite_sum->real^N) (pastecart (lift r) (lift q)) =
          chart_jac (chart_at atlas (f r q)) c0 (f r q) ((Z:real->real->real^N) r q)`
  (LABEL_TAC "pv") THENL
   [MAP_EVERY EXPAND_TAC ["F0"; "W0"] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  (* claim A: the c0-representative of D_t Z along the s-line *)
  SUBGOAL_THEN
   `!r. abs(r - s) < e
        ==> chart_jac (chart_at atlas ((f:real->real->A) r t))
              (c0:(A->bool)#(A->real^N)) (f r t)
              (mfd_covd atlas (g:A->real^N^N) (f r) ((Z:real->real->real^N) r) t) =
            frechet_derivative (W0:real^(1,1)finite_sum->real^N)
              (at (pastecart (lift r) (lift t))) e2 +
            christoffel G0 (F0(pastecart (lift r) (lift t)))
              (frechet_derivative (F0:real^(1,1)finite_sum->real^N)
                 (at (pastecart (lift r) (lift t))) e2)
              (W0(pastecart (lift r) (lift t)))`
  (LABEL_TAC "ca") THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    USE_THEN "ns" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(r - s) < e`))) THEN
    EXPAND_TAC "O0" THEN REWRITE_TAC[GEOC_IN_PAIR_SET] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:real->real->A`; `Z:real->real->real^N`;
                   `S0:real->bool`; `J:real->bool`; `c0:(A->bool)#(A->real^N)`;
                   `r:real`; `t:real`] CMPC_COVD_REP_T) THEN
    ASM_REWRITE_TAC[mfd_field_rep] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "pv" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  (* claim B: the c0-representative of D_s Z along the t-line *)
  SUBGOAL_THEN
   `!r. abs(r - t) < e
        ==> chart_jac (chart_at atlas ((f:real->real->A) s r))
              (c0:(A->bool)#(A->real^N)) (f s r)
              (mfd_covd atlas (g:A->real^N^N) (\s'. f s' r)
                 (\s'. (Z:real->real->real^N) s' r) s) =
            frechet_derivative (W0:real^(1,1)finite_sum->real^N)
              (at (pastecart (lift s) (lift r))) e1 +
            christoffel G0 (F0(pastecart (lift s) (lift r)))
              (frechet_derivative (F0:real^(1,1)finite_sum->real^N)
                 (at (pastecart (lift s) (lift r))) e1)
              (W0(pastecart (lift s) (lift r)))`
  (LABEL_TAC "cb") THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    USE_THEN "nt" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(r - t) < e`))) THEN
    EXPAND_TAC "O0" THEN REWRITE_TAC[GEOC_IN_PAIR_SET] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:real->real->A`; `Z:real->real->real^N`;
                   `S0:real->bool`; `J:real->bool`; `c0:(A->bool)#(A->real^N)`;
                   `s:real`; `r:real`] CMPC_COVD_REP_S) THEN
    ASM_REWRITE_TAC[mfd_field_rep] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "pv" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  (* the velocities, Z and the two inner covariant derivatives at (s,t) *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `(f:real->real->A) s t`] CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `mfd_vel atlas (\s'. (f:real->real->A) s' t) s =
    frechet_derivative (F0:real^(1,1)finite_sum->real^N)
      (at (pastecart (lift s) (lift t))) e1 /\
    mfd_vel atlas (f s) t =
    frechet_derivative F0 (at (pastecart (lift s) (lift t))) e2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                   `c0:(A->bool)#(A->real^N)`; `s:real`; `t:real`] GEOC_VEL_CHART2) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "pv" (fun pv ->
    SUBGOAL_THEN
     `(Z:real->real->real^N) s t = W0 (pastecart (lift s) (lift t)) /\
      SND (c0:(A->bool)#(A->real^N)) ((f:real->real->A) s t) =
      F0 (pastecart (lift s) (lift t))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[pv] THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) ((f:real->real->A) s) ((Z:real->real->real^N) s) t =
    frechet_derivative (W0:real^(1,1)finite_sum->real^N)
      (at (pastecart (lift s) (lift t))) e2 +
    christoffel G0 (F0(pastecart (lift s) (lift t)))
      (frechet_derivative (F0:real^(1,1)finite_sum->real^N)
         (at (pastecart (lift s) (lift t))) e2)
      (W0(pastecart (lift s) (lift t)))`
  ASSUME_TAC THENL
   [USE_THEN "ca" (MP_TAC o SPEC `s:real`) THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (\s'. (f:real->real->A) s' t)
      (\s'. (Z:real->real->real^N) s' t) s =
    frechet_derivative (W0:real^(1,1)finite_sum->real^N)
      (at (pastecart (lift s) (lift t))) e1 +
    christoffel G0 (F0(pastecart (lift s) (lift t)))
      (frechet_derivative (F0:real^(1,1)finite_sum->real^N)
         (at (pastecart (lift s) (lift t))) e1)
      (W0(pastecart (lift s) (lift t)))`
  ASSUME_TAC THENL
   [USE_THEN "cb" (MP_TAC o SPEC `t:real`) THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* differentiability of the partial derivative fields at (s,t) *)
  SUBGOAL_THEN
   `!w. (\z. frechet_derivative (F0:real^(1,1)finite_sum->real^N) (at z) w)
        differentiable at (pastecart (lift s) (lift t)) /\
        (\z. frechet_derivative (W0:real^(1,1)finite_sum->real^N) (at z) w)
        differentiable at (pastecart (lift s) (lift t)) /\
        F0 differentiable at (pastecart (lift s) (lift t)) /\
        W0 differentiable at (pastecart (lift s) (lift t))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `O0:real^(1,1)finite_sum->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  (* the outer derivative along the s-line *)
  SUBGOAL_THEN
   `vector_derivative
      (\x. mfd_field_rep atlas (\s'. (f:real->real->A) s' t)
             (\s'. mfd_covd atlas (g:A->real^N^N) (f s') ((Z:real->real->real^N) s') t)
             (c0:(A->bool)#(A->real^N)) (drop x)) (at (lift s)) =
    frechet_derivative (\z. frechet_derivative (W0:real^(1,1)finite_sum->real^N) (at z) e2)
      (at (pastecart (lift s) (lift t))) e1 +
    frechet_derivative
      (\z. christoffel G0 z
             (frechet_derivative (F0:real^(1,1)finite_sum->real^N)
                (at (pastecart (lift s) (lift t))) e2)
             (W0 (pastecart (lift s) (lift t))))
      (at (F0 (pastecart (lift s) (lift t))))
      (frechet_derivative F0 (at (pastecart (lift s) (lift t))) e1) +
    christoffel G0 (F0 (pastecart (lift s) (lift t)))
      (frechet_derivative (\z. frechet_derivative F0 (at z) e2)
         (at (pastecart (lift s) (lift t))) e1)
      (W0 (pastecart (lift s) (lift t))) +
    christoffel G0 (F0 (pastecart (lift s) (lift t)))
      (frechet_derivative F0 (at (pastecart (lift s) (lift t))) e2)
      (frechet_derivative W0 (at (pastecart (lift s) (lift t))) e1)`
  (LABEL_TAC "vd1") THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC
     `\x. frechet_derivative (W0:real^(1,1)finite_sum->real^N)
            (at (pastecart x (lift t))) e2 +
          christoffel G0 (F0 (pastecart x (lift t)))
            (frechet_derivative (F0:real^(1,1)finite_sum->real^N)
               (at (pastecart x (lift t))) e2)
            (W0 (pastecart x (lift t)))` THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN REWRITE_TAC[mfd_field_rep] THEN
      USE_THEN "ca" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(drop x - s) < e`))) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\z. frechet_derivative (W0:real^(1,1)finite_sum->real^N) (at z) e2`;
                     `lift s`; `lift t`] GEOC_COORD_LINES) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`U0:real^N->bool`; `G0:real^N->real^N^N`;
      `\x. (F0:real^(1,1)finite_sum->real^N) (pastecart x (lift t))`;
      `\x. frechet_derivative (F0:real^(1,1)finite_sum->real^N)
              (at (pastecart x (lift t))) e2`;
      `\x. (W0:real^(1,1)finite_sum->real^N) (pastecart x (lift t))`;
      `frechet_derivative (F0:real^(1,1)finite_sum->real^N)
         (at (pastecart (lift s) (lift t))) e1`;
      `frechet_derivative (\z. frechet_derivative (F0:real^(1,1)finite_sum->real^N) (at z) e2)
         (at (pastecart (lift s) (lift t))) e1`;
      `frechet_derivative (W0:real^(1,1)finite_sum->real^N)
         (at (pastecart (lift s) (lift t))) e1`;
      `lift s`] CMPC_CHRISTOFFEL_ALONG) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`F0:real^(1,1)finite_sum->real^N`; `lift s`; `lift t`]
        GEOC_COORD_LINES) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`\z. frechet_derivative (F0:real^(1,1)finite_sum->real^N) (at z) e2`;
                     `lift s`; `lift t`] GEOC_COORD_LINES) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`W0:real^(1,1)finite_sum->real^N`; `lift s`; `lift t`]
        GEOC_COORD_LINES) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  (* the outer derivative along the t-line *)
  SUBGOAL_THEN
   `vector_derivative
      (\x. mfd_field_rep atlas ((f:real->real->A) s)
             (\t'. mfd_covd atlas (g:A->real^N^N) (\s'. f s' t')
                      (\s'. (Z:real->real->real^N) s' t') s)
             (c0:(A->bool)#(A->real^N)) (drop x)) (at (lift t)) =
    frechet_derivative (\z. frechet_derivative (W0:real^(1,1)finite_sum->real^N) (at z) e1)
      (at (pastecart (lift s) (lift t))) e2 +
    frechet_derivative
      (\z. christoffel G0 z
             (frechet_derivative (F0:real^(1,1)finite_sum->real^N)
                (at (pastecart (lift s) (lift t))) e1)
             (W0 (pastecart (lift s) (lift t))))
      (at (F0 (pastecart (lift s) (lift t))))
      (frechet_derivative F0 (at (pastecart (lift s) (lift t))) e2) +
    christoffel G0 (F0 (pastecart (lift s) (lift t)))
      (frechet_derivative (\z. frechet_derivative F0 (at z) e1)
         (at (pastecart (lift s) (lift t))) e2)
      (W0 (pastecart (lift s) (lift t))) +
    christoffel G0 (F0 (pastecart (lift s) (lift t)))
      (frechet_derivative F0 (at (pastecart (lift s) (lift t))) e1)
      (frechet_derivative W0 (at (pastecart (lift s) (lift t))) e2)`
  (LABEL_TAC "vd2") THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC
     `\x. frechet_derivative (W0:real^(1,1)finite_sum->real^N)
            (at (pastecart (lift s) x)) e1 +
          christoffel G0 (F0 (pastecart (lift s) x))
            (frechet_derivative (F0:real^(1,1)finite_sum->real^N)
               (at (pastecart (lift s) x)) e1)
            (W0 (pastecart (lift s) x))` THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN REWRITE_TAC[mfd_field_rep] THEN
      USE_THEN "cb" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(drop x - t) < e`))) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\z. frechet_derivative (W0:real^(1,1)finite_sum->real^N) (at z) e1`;
                     `lift s`; `lift t`] GEOC_COORD_LINES) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`U0:real^N->bool`; `G0:real^N->real^N^N`;
      `\x. (F0:real^(1,1)finite_sum->real^N) (pastecart (lift s) x)`;
      `\x. frechet_derivative (F0:real^(1,1)finite_sum->real^N)
              (at (pastecart (lift s) x)) e1`;
      `\x. (W0:real^(1,1)finite_sum->real^N) (pastecart (lift s) x)`;
      `frechet_derivative (F0:real^(1,1)finite_sum->real^N)
         (at (pastecart (lift s) (lift t))) e2`;
      `frechet_derivative (\z. frechet_derivative (F0:real^(1,1)finite_sum->real^N) (at z) e1)
         (at (pastecart (lift s) (lift t))) e2`;
      `frechet_derivative (W0:real^(1,1)finite_sum->real^N)
         (at (pastecart (lift s) (lift t))) e2`;
      `lift t`] CMPC_CHRISTOFFEL_ALONG) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`F0:real^(1,1)finite_sum->real^N`; `lift s`; `lift t`]
        GEOC_COORD_LINES) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`\z. frechet_derivative (F0:real^(1,1)finite_sum->real^N) (at z) e1`;
                     `lift s`; `lift t`] GEOC_COORD_LINES) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`W0:real^(1,1)finite_sum->real^N`; `lift s`; `lift t`]
        GEOC_COORD_LINES) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  (* unfold the two outer covariant derivatives and the curvature *)
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [mfd_covd] THEN
  REWRITE_TAC[mfd_riemann] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lriemann] THEN
  MP_TAC(ISPECL [`O0:real^(1,1)finite_sum->bool`; `W0:real^(1,1)finite_sum->real^N`;
                 `pastecart (lift s) (lift t)`; `e1:real^(1,1)finite_sum`;
                 `e2:real^(1,1)finite_sum`] LRG_SECOND_DERIVATIVE_SYM) THEN
  MP_TAC(ISPECL [`O0:real^(1,1)finite_sum->bool`; `F0:real^(1,1)finite_sum->real^N`;
                 `pastecart (lift s) (lift t)`; `e1:real^(1,1)finite_sum`;
                 `e2:real^(1,1)finite_sum`] LRG_SECOND_DERIVATIVE_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`U0:real^N->bool`; `G0:real^N->real^N^N`;
                 `(F0:real^(1,1)finite_sum->real^N) (pastecart (lift s) (lift t))`]
    LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD (SPEC_ALL (CONJUNCT1 th))]) THEN
  VECTOR_ARITH_TAC);;


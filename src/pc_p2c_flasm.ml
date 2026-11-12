(* ========================================================================= *)
(* Unit pc_p2c_flasm (Part 2C, flowlim route): the abstract assembly of a   *)
(* limit Ricci flow on a fixed manifold from local limits.  A sequence of   *)
(* time-dependent metrics P k s on a manifold (top,atlas) with an exhaustion *)
(* W, whose chart expressions on the compact intervals of J containing 0    *)
(* are eventually local Ricci flows with the uniform bounds of               *)
(* P2CM_LOCAL_LIMIT, and which are lck close to g0 at time 0, has a         *)
(* subsequence converging in every C^m, uniformly over compact time         *)
(* intervals and compact sets, to a Ricci flow g on J with g 0 = g0.        *)
(* Countable chart pieces, countable admissible intervals and the           *)
(* diagonalization lemma of misc.ml.                                         *)
(* ========================================================================= *)

needs "src/pc_p2c_flconv.ml";;
needs "src/pc_pde_mloc.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Chart independence of lck_dist2 for two manifold metrics,                *)
(* finite covers of compact sets by chart pieces.                            *)
(* ------------------------------------------------------------------------- *)

let P2CA_LCK_CHART_INDEP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) g1 g2 U phi V psi y m.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g1 /\
     riemannian_metric atlas g2 /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
     y IN U /\ y IN V
     ==> lck_dist2 m (metric_local atlas (U,phi) g1) (metric_local atlas (U,phi) g2) (phi y) =
         lck_dist2 m (metric_local atlas (V,psi) g1) (metric_local atlas (V,psi) g2) (psi y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`]
                CHART_TRANS_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`]
                CHART_OVERLAP_IMAGE_OPEN) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`; `U:A->bool`; `phi:A->real^N`]
                CHART_OVERLAP_IMAGE_OPEN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `open (IMAGE (psi:A->real^N) (U INTER V))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN IMAGE (phi:A->real^N) (U INTER V)
        ==> metric_local (atlas:((A->bool)#(A->real^N))->bool) (U,phi) (g1:A->real^N^N) z =
            mpullback (chart_trans (U:A->bool,phi:A->real^N) (V:A->bool,psi:A->real^N)) (metric_local (atlas:((A->bool)#(A->real^N))->bool) (V,psi) g1) z /\
            metric_local (atlas:((A->bool)#(A->real^N))->bool) (U,phi) (g2:A->real^N^N) z =
            mpullback (chart_trans (U:A->bool,phi:A->real^N) (V:A->bool,psi:A->real^N)) (metric_local (atlas:((A->bool)#(A->real^N))->bool) (V,psi) g2) z`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC METRIC_LOCAL_TRANS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `metric_local (atlas:((A->bool)#(A->real^N))->bool) (U,phi) (g1:A->real^N^N)`;
                 `mpullback (chart_trans (U:A->bool,phi:A->real^N) (V:A->bool,psi:A->real^N))
                    (metric_local (atlas:((A->bool)#(A->real^N))->bool) (V,psi) (g1:A->real^N^N))`;
                 `metric_local (atlas:((A->bool)#(A->real^N))->bool) (U,phi) (g2:A->real^N^N)`;
                 `mpullback (chart_trans (U:A->bool,phi:A->real^N) (V:A->bool,psi:A->real^N))
                    (metric_local (atlas:((A->bool)#(A->real^N))->bool) (V,psi) (g2:A->real^N^N))`;
                 `IMAGE (phi:A->real^N) (U INTER V)`; `(phi:A->real^N) y`] LCK_DIST2_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `y:A` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `chart_trans (U:A->bool,phi:A->real^N) (V:A->bool,psi:A->real^N) ((phi:A->real^N) y) = (psi:A->real^N) y`
  (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THENL
   [REWRITE_TAC[chart_trans] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC LCK_DIST2_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (psi:A->real^N) (U INTER V)`;
                        `IMAGE (phi:A->real^N) (U INTER V)`;
                        `chart_trans (V:A->bool,psi:A->real^N) (U:A->bool,phi:A->real^N):real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g1:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g2:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[]]);;

(* Finitely many chart balls (with doubled closed balls inside O) cover a   *)
(* compact subset K of an open set O.                                         *)

let P2CA_PIECES = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) K O.
     smooth_manifold_atlas top atlas /\ compact_in top K /\ open_in top O /\ K SUBSET O
     ==> ?n (c:num->(A->bool)#(A->real^N)) z r.
            (!i. 1 <= i /\ i <= n
                 ==> c i IN atlas /\ &0 < r i /\
                     cball(z i,&2 * r i) SUBSET IMAGE (SND(c i)) (FST(c i) INTER O)) /\
            (!y. y IN K
                 ==> ?i. 1 <= i /\ i <= n /\ y IN FST(c i) /\ SND(c i) y IN ball(z i,r i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[compact_in]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:A. y IN K
          ==> ?e. &0 < e /\
                  cball(SND(chart_at atlas y) y,&2 * e) SUBSET
                  IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) y))
                        (FST(chart_at atlas y) INTER O)`
  MP_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`]
                  CHART_AT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) y`,
             `cy:(A->bool)#(A->real^N)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`; `U INTER (O:A->bool)`]
                  CHART_IMAGE_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN
    DISCH_THEN(MP_TAC o SPEC `(phi:A->real^N) y`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `y:A` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_ARITH `~(&2 = &0)`];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `ee:A->real`) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [compact_in] o
              check (fun th -> can (find_term ((=) `compact_in:(A)topology->(A->bool)->bool`))
                                   (concl th))) THEN
  DISCH_THEN(MP_TAC o SPEC
    `IMAGE (\y:A. {p | p IN FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) y) /\
                       SND(chart_at atlas y) p IN ball(SND(chart_at atlas y) y,ee y)}) K` o
    CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`]
                    CHART_AT) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) y`,
               `cy:(A->bool)#(A->real^N)`) THEN
      REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC GRGD_CHART_PREIMAGE_OPEN THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[OPEN_BALL];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`]
                    CHART_AT) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]] THEN
      DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fc:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`\y:A. {p | p IN FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) y) /\
                SND(chart_at atlas y) p IN ball(SND(chart_at atlas y) y,ee y)}`;
    `K:A->bool`; `Fc:(A->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K':A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `K':A->bool` FINITE_INDEX_NUMSEG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`CARD(K':A->bool)`; `\i. chart_at (atlas:((A->bool)#(A->real^N))->bool) ((f:num->A) i)`;
    `\i. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((f:num->A) i)) (f i)`;
    `\i. (ee:A->real) ((f:num->A) i)`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `((f:num->A) i) IN K` ASSUME_TAC THENL
     [SUBGOAL_THEN `((f:num->A) i) IN K'` MP_TAC THENL
       [UNDISCH_TAC `K' = IMAGE (f:num->A) (1..CARD(K':A->bool))` THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
        REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN
        EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(f:num->A) i`] CHART_AT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN UNIONS Fc` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:A) IN K'` THEN
  UNDISCH_TAC `K' = IMAGE (f:num->A) (1..CARD(K':A->bool))` THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Chart pieces level by level over the exhaustion, compact                 *)
(* sets inside one level, and a countable family of admissible intervals.  *)
(* ------------------------------------------------------------------------- *)

let P2CA_PIECE_LEVELS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W.
     smooth_manifold_atlas top atlas /\
     (!k. open_in top (W k) /\ compact_in top (top closure_of W k) /\
          top closure_of W k SUBSET W (SUC k))
     ==> ?n (c:num->num->(A->bool)#(A->real^N)) z r.
            !m. (!i. 1 <= i /\ i <= n m
                     ==> c m i IN atlas /\ &0 < r m i /\
                         cball(z m i,&2 * r m i) SUBSET
                         IMAGE (SND(c m i)) (FST(c m i) INTER W (SUC m))) /\
                (!y. y IN top closure_of W m
                     ==> ?i. 1 <= i /\ i <= n m /\ y IN FST(c m i) /\
                             SND(c m i) y IN ball(z m i,r m i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `m:num` THEN
  MATCH_MP_TAC P2CA_PIECES THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

let P2CA_COMPACT_IN_W = prove
 (`!top (W:num->A->bool) K.
     (!k. open_in top (W k) /\ top closure_of W k SUBSET W (SUC k)) /\
     UNIONS {W k | k IN (:num)} = topspace top /\ compact_in top K
     ==> ?m. K SUBSET W m`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W") (CONJUNCTS_THEN2 (LABEL_TAC "U") (LABEL_TAC "K"))) THEN
  SUBGOAL_THEN `!k. (W:num->A->bool) k SUBSET W (SUC k)` (LABEL_TAC "step") THENL
   [GEN_TAC THEN USE_THEN "W" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    MP_TAC(ISPECL [`top:A topology`; `(W:num->A->bool) k`] CLOSURE_OF_SUBSET) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k l. k <= l ==> (W:num->A->bool) k SUBSET W l` (LABEL_TAC "mono") THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN REWRITE_TAC[SUBSET_REFL] THEN
    CONJ_TAC THENL [SET_TAC[]; USE_THEN "step" ACCEPT_TAC];
    ALL_TAC] THEN
  USE_THEN "K" (MP_TAC o GEN_REWRITE_RULE I [compact_in]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `{(W:num->A->bool) k | k IN (:num)}`)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_GSPEC] THEN GEN_TAC THEN DISCH_TAC THEN
      USE_THEN "W" (fun th -> REWRITE_TAC[th]);
      USE_THEN "U" SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fc:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`W:num->A->bool`; `(:num)`; `Fc:(A->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  MP_TAC(ISPEC `s:num->bool` num_FINITE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN EXISTS_TAC `m:num` THEN
  UNDISCH_TAC `(K:A->bool) SUBSET UNIONS {(W:num->A->bool) x | x IN s}` THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  USE_THEN "mono" MP_TAC THEN REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]);;

(* Admissible intervals: endpoints rational or extreme points of J. *)

let P2CA_LOWER_POINT = prove
 (`!J a. is_realinterval J /\ a IN J
         ==> ?p. p <= a /\ p IN J /\ (rational p \/ !s. s IN J ==> p <= s)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `!s. s IN J ==> a <= s` THENL
   [EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(s + a) / &2`; `(a - s) / &2`] RATIONAL_APPROXIMATION) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `p:real` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s < p /\ p < a` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `is_realinterval J` THEN REWRITE_TAC[is_realinterval] THEN
  DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`s:real`; `a:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2CA_UPPER_POINT = prove
 (`!J b. is_realinterval J /\ b IN J
         ==> ?q. b <= q /\ q IN J /\ (rational q \/ !s. s IN J ==> s <= q)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `!s. s IN J ==> s <= b` THENL
   [EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(s + b) / &2`; `(s - b) / &2`] RATIONAL_APPROXIMATION) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `q:real` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `b < q /\ q < s` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `is_realinterval J` THEN REWRITE_TAC[is_realinterval] THEN
  DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`b:real`; `s:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2CA_EXTREME_COUNTABLE = prove
 (`!J P. (!x y. x IN J /\ P x /\ y IN J /\ P y ==> x = (y:real))
         ==> COUNTABLE {x | x IN J /\ P x}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{@x:real. x IN J /\ P x}` THEN
  REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\x:real. x IN J /\ P x`; `x:real`] SELECT_AX) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let P2CA_INTERVAL_COVER = prove
 (`!J s a b. is_realinterval J /\ (&0) IN J /\ s IN J /\ ~(s = &0) /\
             a <= b /\ real_interval[a,b] SUBSET J
             ==> ?p q. (rational p \/ (p IN J /\ !x. x IN J ==> p <= x)) /\
                       (rational q \/ (q IN J /\ !x. x IN J ==> x <= q)) /\
                       p <= &0 /\ &0 <= q /\ p < q /\ real_interval[p,q] SUBSET J /\
                       p <= a /\ b <= q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:real) IN J /\ b IN J` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `real_interval[a,b] SUBSET J` THEN REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `a1 = min a (min (&0) s)` THEN ABBREV_TAC `b1 = max b (max (&0) s)` THEN
  SUBGOAL_THEN `(a1:real) IN J /\ b1 IN J /\ a1 < b1 /\ a1 <= &0 /\ &0 <= b1 /\
                a1 <= a /\ b <= b1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a1"; "b1"] THEN
    REWRITE_TAC[real_min; real_max] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`J:real->bool`; `a1:real`] P2CA_LOWER_POINT) THEN
  MP_TAC(ISPECL [`J:real->bool`; `b1:real`] P2CA_UPPER_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`p:real`; `q:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  UNDISCH_TAC `is_realinterval J` THEN REWRITE_TAC[is_realinterval] THEN
  DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`p:real`; `q:real`] THEN
  ASM_REWRITE_TAC[]);;

let P2CA_INTERVALS = prove
 (`!J. is_realinterval J /\ (&0) IN J /\ ~(J = {&0})
       ==> ?(al:num->real) (be:num->real). (!j. al j <= &0 /\ &0 <= be j /\ al j < be j /\
                        real_interval[al j,be j] SUBSET J) /\
                   (!a b. a <= b /\ real_interval[a,b] SUBSET J
                          ==> ?j. al j <= a /\ b <= be j)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?s. s IN J /\ ~(s = &0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(J = {&0})` THEN UNDISCH_TAC `(&0) IN J` THEN SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `D = {pq | (rational(FST pq) \/ (FST pq IN J /\ !s. s IN J ==> FST pq <= s)) /\
              (rational(SND pq) \/ (SND pq IN J /\ !s. s IN J ==> s <= SND pq)) /\
              FST pq <= &0 /\ &0 <= SND pq /\ FST pq < SND pq /\
              real_interval[FST pq,SND pq] SUBSET J}` THEN
  SUBGOAL_THEN
   `!a b. a <= b /\ real_interval[a,b] SUBSET J ==> ?pq. pq IN D /\ FST pq <= a /\ b <= SND pq`
  (LABEL_TAC "cov") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`J:real->bool`; `s:real`; `a:real`; `b:real`] P2CA_INTERVAL_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `(p:real,q:real)` THEN EXPAND_TAC "D" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `COUNTABLE (D:real#real->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC `(rational UNION {x | x IN J /\ !s. s IN J ==> x <= s}) CROSS
                (rational UNION {x | x IN J /\ !s. s IN J ==> s <= x})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_CROSS THEN REWRITE_TAC[COUNTABLE_UNION; COUNTABLE_RATIONAL] THEN
      CONJ_TAC THEN MATCH_MP_TAC P2CA_EXTREME_COUNTABLE THEN REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "D" THEN REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; IN_CROSS;
                                      FST; SND; IN_UNION] THEN
      REWRITE_TAC[IN] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(D:real#real->bool = {})` ASSUME_TAC THENL
   [USE_THEN "cov" (MP_TAC o SPECL [`&0`; `&0`]) THEN
    REWRITE_TAC[REAL_LE_REFL; REAL_INTERVAL_SING; SING_SUBSET] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `D:real#real->bool` COUNTABLE_AS_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real#real` (LABEL_TAC "f")) THEN
  MAP_EVERY EXISTS_TAC [`\j. FST((f:num->real#real) j)`; `\j. SND((f:num->real#real) j)`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN
    SUBGOAL_THEN `((f:num->real#real) j) IN D` MP_TAC THENL
     [USE_THEN "f" SUBST1_TAC THEN REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
      EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    USE_THEN "cov" (MP_TAC o SPECL [`a:real`; `b:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `pq:real#real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(pq:real#real) IN IMAGE (f:num->real#real) (:num)` MP_TAC THENL
     [USE_THEN "f" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THEN EXISTS_TAC `j:num` THEN
    ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The hypotheses and conclusions of the local limit theorem as              *)
(* predicates (p2ca_seqhyp, p2ca_loclim), their stability under             *)
(* subsequences, tails and smaller open sets.                               *)
(* ------------------------------------------------------------------------- *)

let p2ca_seqhyp = new_definition
 `p2ca_seqhyp V a b (Gs:num->real->real^N->real^N^N) <=>
    (!n t. a <= t /\ t <= b ==> metric_field V (Gs n t)) /\
    (!n. lricci_flow V a b (Gs n)) /\
    (!n. ?e (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
           &0 < e /\ smooth_map_on (interval(lift(a - e),lift(b + e)) PCROSS V) FF /\
           (!t y. a <= t /\ t <= b /\ y IN V
                  ==> FF(pastecart (lift t) y) = vectorize(Gs n t y))) /\
    (!K. compact K /\ K SUBSET V
         ==> ?Lm. !n t y v. a <= t /\ t <= b /\ y IN K
                            ==> norm v pow 2 <= Lm * (v dot (Gs n t y ** v))) /\
    (!K l p q. compact K /\ K SUBSET V /\
               ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
               1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
               ==> ?B. !n w. w IN interval(lift a,lift b) PCROSS K
                            ==> norm(iterated_partial l
                                       (\w. lift(Gs n (drop(fstcart w)) (sndcart w)$p$q)) w)
                                <= B)`;;

let p2ca_loclim = new_definition
 `p2ca_loclim V a b (Gs:num->real->real^N->real^N^N) G <=>
    lricci_flow V a b G /\
    (!t. a <= t /\ t <= b ==> metric_field V (G t)) /\
    (!t y p q. a <= t /\ t <= b /\ y IN V /\
               1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
               ==> ((\n. Gs n t y$p$q) ---> G t y$p$q) sequentially) /\
    (!K m e. compact K /\ K SUBSET V /\ &0 < e
             ==> ?N. !n t y. N <= n /\ a <= t /\ t <= b /\ y IN K
                             ==> lck_dist2 m (G t) (Gs n t) y < e)`;;

let P2CA_LOCAL_LIMIT = prove
 (`!V a b (Gs:num->real->real^N->real^N^N).
     open V /\ a < b /\ p2ca_seqhyp V a b Gs
     ==> ?sub G. (!m n. m < n ==> sub m < sub n) /\
                 p2ca_loclim V a b (\n. Gs (sub n)) G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ca_seqhyp; p2ca_loclim] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`]
                P2CM_LOCAL_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]);;

let P2CA_SEQHYP_REINDEX = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) f.
     p2ca_seqhyp V a b Gs ==> p2ca_seqhyp V a b (\n. Gs (f n))`,
  REWRITE_TAC[p2ca_seqhyp] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    X_GEN_TAC `K:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `K:real^N->bool` o check (fun th ->
      can (find_term ((=) `( ** ):real^N^N->real^N->real^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`K:real^N->bool`; `l:num list`; `p:num`; `q:num`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`K:real^N->bool`; `l:num list`; `p:num`; `q:num`] o
      check (fun th -> can (find_term ((=) `iterated_partial:(num)list->(real^(1,N)finite_sum->real^1)->real^(1,N)finite_sum->real^1`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]]);;

let P2CA_SEQHYP_SUBSET = prove
 (`!V V' a b (Gs:num->real->real^N->real^N^N).
     p2ca_seqhyp V a b Gs /\ open V' /\ V' SUBSET V ==> p2ca_seqhyp V' a b Gs`,
  REWRITE_TAC[p2ca_seqhyp] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `V:real^N->bool` THEN ASM_SIMP_TAC[];
    GEN_TAC THEN MATCH_MP_TAC RFA_LRICCI_FLOW_SUBSET THEN
    EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      can (find_term ((=) `pastecart:real^1->real^N->real^(1,N)finite_sum`)) (concl th))) THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(a - e),lift(b + e)) PCROSS (V:real^N->bool)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL];
      ASM_MESON_TAC[SUBSET]];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* Eventual properties pass to eventual subsequences. *)

let P2CA_TAIL_GEN = prove
 (`!(P:num->bool) (f:num->num) (g:num->num) (M:num) (N:num).
     (!n. M <= n ==> P (f n)) /\ (!j. N <= j ==> ?j'. j <= j' /\ g j = f j')
     ==> !j. M + N <= j ==> P (g j)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P") (LABEL_TAC "sub")) THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  USE_THEN "sub" (MP_TAC o SPEC `j:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "P" MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let P2CA_LOCLIM_TAIL = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) G (f:num->num) (g:num->num) (N:num).
     p2ca_loclim V a b (\n. Gs (f n)) G /\ (!j. N <= j ==> ?j'. j <= j' /\ g j = f j')
     ==> p2ca_loclim V a b (\n. Gs (g n)) G`,
  REWRITE_TAC[p2ca_loclim; REALLIM_SEQUENTIALLY] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pt") (LABEL_TAC "lk")))) (LABEL_TAC "sub")) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "pt" (MP_TAC o SPECL [`t:real`; `y:real^N`; `p:num`; `q:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
    EXISTS_TAC `M + N:num` THEN
    MATCH_MP_TAC(BETA_RULE(ISPECL
      [`\k:num. abs((Gs:num->real->real^N->real^N^N) k t y$p$q -
                    (G:real->real^N->real^N^N) t y$p$q) < e`;
       `f:num->num`; `g:num->num`; `M:num`; `N:num`] P2CA_TAIL_GEN)) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    USE_THEN "lk" (MP_TAC o SPECL [`K:real^N->bool`; `m:num`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
    EXISTS_TAC `M + N:num` THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\k:num. !t y. a <= t /\ t <= b /\ y IN K
                      ==> lck_dist2 m ((G:real->real^N->real^N^N) t)
                            ((Gs:num->real->real^N->real^N^N) k t) y < e`;
       `f:num->num`; `g:num->num`; `M:num`; `N:num`] P2CA_TAIL_GEN)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Tools of the assembly.  Local limits only depend on tails                 *)
(* (P2CA_LOCLIM_EVENTUALLY); the diagonal subsequence for a countable family *)
(* of local sequences, each satisfying the hypotheses of the local limit     *)
(* theorem from some index on (P2CA_DIAG, SUBSEQUENCE_DIAGONALIZATION_LEMMA  *)
(* with the MAX trick); smaller time intervals of local flows; a family      *)
(* whose chart representatives are local Ricci flows in every chart is a     *)
(* Ricci flow (the converse of LRG_RICCI_FLOW_ON_CHART); chart independence  *)
(* of lck_dist2 for metrics that are metric fields only near the point.      *)
(* ------------------------------------------------------------------------- *)

let P2CA_LOCLIM_EVENTUALLY = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) Gs' G (N:num).
     p2ca_loclim V a b Gs G /\ (!n. N <= n ==> Gs' n = Gs n)
     ==> p2ca_loclim V a b Gs' G`,
  REWRITE_TAC[p2ca_loclim; REALLIM_SEQUENTIALLY] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pt") (LABEL_TAC "lk")))) (LABEL_TAC "ev")) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "pt" (MP_TAC o SPECL [`t:real`; `y:real^N`; `p:num`; `q:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` (LABEL_TAC "M")) THEN EXISTS_TAC `M + N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Gs':num->real->real^N->real^N^N) n = Gs n` SUBST1_TAC THENL
     [USE_THEN "ev" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "M" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    USE_THEN "lk" (MP_TAC o SPECL [`K:real^N->bool`; `m:num`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` (LABEL_TAC "M")) THEN EXISTS_TAC `M + N:num` THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(Gs':num->real->real^N->real^N^N) n = Gs n` SUBST1_TAC THENL
     [USE_THEN "ev" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "M" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let P2CA_MAX_SHIFT = prove
 (`!x y:num. y + (MAX x y - y) = MAX x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAX] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* The diagonal subsequence. *)

let P2CA_DIAG = prove
 (`!(ok:num->bool) (V:num->real^N->bool) (a:num->real) (b:num->real)
    (H:num->num->real->real^N->real^N^N).
     (!d. ok d ==> open(V d) /\ a d < b d /\
                   ?N. p2ca_seqhyp (V d) (a d) (b d) (\n. H d (N + n)))
     ==> ?sub. (!m n. m < n ==> sub m < sub n) /\
               !d. ok d ==> ?G. p2ca_loclim (V d) (a d) (b d) (\n. H d (sub n)) G`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "hyp") THEN
  SUBGOAL_THEN
   `?NN:num->num. !d. ok d ==> p2ca_seqhyp (V d) (a d) (b d)
                                  (\n. (H:num->num->real->real^N->real^N^N) d (NN d + n))`
  (X_CHOOSE_THEN `NN:num->num` (LABEL_TAC "NN")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `d:num` THEN
    ASM_CASES_TAC `(ok:num->bool) d` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "hyp" (MP_TAC o C MP (ASSUME `(ok:num->bool) d`) o SPEC `d:num`) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC
   `\d (r:num->num). (ok:num->bool) d
                     ==> ?G. p2ca_loclim (V d) (a d) (b d)
                               (\n. (H:num->num->real->real^N->real^N^N) d
                                      (MAX (r n) (NN d))) G`
   SUBSEQUENCE_DIAGONALIZATION_LEMMA) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`d:num`; `r:num->num`] THEN
      ASM_CASES_TAC `(ok:num->bool) d` THEN ASM_REWRITE_TAC[] THENL
       [ALL_TAC; EXISTS_TAC `\n:num. n` THEN ARITH_TAC] THEN
      USE_THEN "hyp" (MP_TAC o C MP (ASSUME `(ok:num->bool) d`) o SPEC `d:num`) THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`(V:num->real^N->bool) d`; `(a:num->real) d`; `(b:num->real) d`;
                     `\n. (H:num->num->real->real^N->real^N^N) d (MAX ((r:num->num) n) (NN d))`]
                    P2CA_LOCAL_LIMIT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`(V:num->real^N->bool) d`; `(a:num->real) d`; `(b:num->real) d`;
                       `\n. (H:num->num->real->real^N->real^N^N) d ((NN:num->num) d + n)`;
                       `\n. MAX ((r:num->num) n) ((NN:num->num) d) - NN d`]
                      P2CA_SEQHYP_REINDEX) THEN
        ANTS_TAC THENL
         [USE_THEN "NN" (MP_TAC o C MP (ASSUME `(ok:num->bool) d`) o SPEC `d:num`) THEN
          REWRITE_TAC[];
          REWRITE_TAC[P2CA_MAX_SHIFT]];
        ALL_TAC] THEN
      REWRITE_TAC[o_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`d:num`; `r:num->num`; `k1:num->num`; `k2:num->num`; `M:num`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    ASM_CASES_TAC `(ok:num->bool) d` THEN ASM_REWRITE_TAC[o_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `G:real->real^N->real^N^N`) THEN
    EXISTS_TAC `G:real->real^N->real^N^N` THEN
    MP_TAC(ISPECL [`(V:num->real^N->bool) d`; `(a:num->real) d`; `(b:num->real) d`;
                   `\x. (H:num->num->real->real^N->real^N^N) d (MAX ((r:num->num) x) (NN d))`;
                   `G:real->real^N->real^N^N`; `k1:num->num`; `k2:num->num`; `M:num`]
                  P2CA_LOCLIM_TAIL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\n:num. n`) THEN REWRITE_TAC[o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dg"))) THEN
  EXISTS_TAC `sub:num->num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  USE_THEN "dg" (MP_TAC o C MP (ASSUME `(ok:num->bool) d`) o SPEC `d:num`) THEN
  DISCH_THEN(X_CHOOSE_TAC `G:real->real^N->real^N^N`) THEN
  EXISTS_TAC `G:real->real^N->real^N^N` THEN
  MATCH_MP_TAC P2CA_LOCLIM_EVENTUALLY THEN
  EXISTS_TAC `\n. (H:num->num->real->real^N->real^N^N) d (MAX ((sub:num->num) n) (NN d))` THEN
  EXISTS_TAC `(NN:num->num) d` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  UNDISCH_TAC `(NN:num->num) d <= n` THEN REWRITE_TAC[MAX] THEN ARITH_TAC);;

(* Smaller time intervals. *)

let P2CA_LRICCI_FLOW_SUBINTERVAL = prove
 (`!U a b a' b' (G:real->real^N->real^N^N).
     lricci_flow U a b G /\ a <= a' /\ a' < b' /\ b' <= b ==> lricci_flow U a' b' G`,
  REWRITE_TAC[lricci_flow] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* Local Ricci flows in every chart give a Ricci flow. *)

let P2CA_RICCI_FLOW_ON_CHARTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N).
     smooth_manifold_atlas top atlas /\ a < b /\
     (!c. c IN atlas
          ==> lricci_flow (IMAGE (SND c) (FST c)) a b (\t. metric_local atlas c (g t)))
     ==> ricci_flow_on (top,atlas) a b g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
  REWRITE_TAC[ricci_flow_on] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[riemannian_metric] THEN
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`) o
      SPEC `c:(A->bool)#(A->real^N)`) THEN
    REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`) o
      SPEC `c:(A->bool)#(A->real^N)`) THEN
    REWRITE_TAC[lricci_flow] THEN MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                  CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME
      `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A) IN atlas`) o
      SPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`) THEN
    REWRITE_TAC[lricci_flow] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real`; `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`;
                               `i:num`; `j:num`] o last o CONJUNCTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[]
     `(f:real->real) = f' /\ (x:real) = x'
      ==> (f has_real_derivative x) net ==> (f' has_real_derivative x') net`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `s:real` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(g:real->A->real^N^N) s`; `x:A`] METRIC_LOCAL_AT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
      ASM_SIMP_TAC[mfd_ricci_matrix; mfd_ricci; LAMBDA_BETA]]]);;

(* Chart independence of lck_dist2 near a point. *)

let P2CA_LCK_CHART_INDEP_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) g1 g2 U phi V psi O y m.
     smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
     open_in top O /\ y IN U /\ y IN V /\ y IN O /\
     metric_field (IMAGE psi (V INTER O)) (metric_local atlas (V,psi) g1) /\
     metric_field (IMAGE psi (V INTER O)) (metric_local atlas (V,psi) g2)
     ==> lck_dist2 m (metric_local atlas (U,phi) g1) (metric_local atlas (U,phi) g2) (phi y) =
         lck_dist2 m (metric_local atlas (V,psi) g1) (metric_local atlas (V,psi) g2) (psi y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = (U:A->bool) INTER V INTER O` THEN
  SUBGOAL_THEN `open_in top (S:A->bool) /\ S SUBSET U /\ S SUBSET V /\
                S SUBSET V INTER O /\ (y:A) IN S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
      SET_TAC[]; SET_TAC[]; SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) S) /\ open(IMAGE (psi:A->real^N) S)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THENL
     [EXISTS_TAC `U:A->bool`; EXISTS_TAC `V:A->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `diffeomorphism_on (IMAGE (phi:A->real^N) S) (IMAGE (psi:A->real^N) S)
      (chart_trans (U:A->bool,phi) (V:A->bool,psi)) (chart_trans (V,psi) (U,phi))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (psi:A->real^N) S =
      IMAGE (chart_trans (U:A->bool,phi:A->real^N) (V:A->bool,psi)) (IMAGE phi S)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[o_THM; chart_trans] THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CMPH_DIFFEO_RESTRICT THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) (U INTER V)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN IMAGE (phi:A->real^N) S
        ==> metric_local (atlas:((A->bool)#(A->real^N))->bool) (U,phi) (g1:A->real^N^N) z =
            mpullback (chart_trans (U:A->bool,phi:A->real^N) (V:A->bool,psi:A->real^N))
                      (metric_local atlas (V,psi) g1) z /\
            metric_local (atlas:((A->bool)#(A->real^N))->bool) (U,phi) (g2:A->real^N^N) z =
            mpullback (chart_trans (U:A->bool,phi:A->real^N) (V:A->bool,psi:A->real^N))
                      (metric_local atlas (V,psi) g2) z`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC METRIC_LOCAL_TRANS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `metric_local (atlas:((A->bool)#(A->real^N))->bool) (U,phi) (g1:A->real^N^N)`;
                 `mpullback (chart_trans (U:A->bool,phi:A->real^N) (V:A->bool,psi:A->real^N))
                    (metric_local (atlas:((A->bool)#(A->real^N))->bool) (V,psi) (g1:A->real^N^N))`;
                 `metric_local (atlas:((A->bool)#(A->real^N))->bool) (U,phi) (g2:A->real^N^N)`;
                 `mpullback (chart_trans (U:A->bool,phi:A->real^N) (V:A->bool,psi:A->real^N))
                    (metric_local (atlas:((A->bool)#(A->real^N))->bool) (V,psi) (g2:A->real^N^N))`;
                 `IMAGE (phi:A->real^N) S`; `(phi:A->real^N) y`] LCK_DIST2_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:A` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `chart_trans (U:A->bool,phi:A->real^N) (V:A->bool,psi:A->real^N) ((phi:A->real^N) y) =
                (psi:A->real^N) y`
  (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THENL
   [REWRITE_TAC[chart_trans] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC LCK_DIST2_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (psi:A->real^N) S`; `IMAGE (phi:A->real^N) S`;
                        `chart_trans (V:A->bool,psi:A->real^N) (U:A->bool,phi:A->real^N):real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) (V INTER O)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) (V INTER O)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The setting of the assembly (p2ca_set: manifold, exhaustion,              *)
(* time interval J, a sequence P of time-dependent metrics whose chart       *)
(* representatives over W m are eventually local flows with the bounds of    *)
(* p2ca_seqhyp on every compact interval of J around 0, lck close to g0 at   *)
(* time 0), the context after the choice of chart pieces, intervals, the     *)
(* diagonal subsequence and the local limits (p2ca_actx), the limit family   *)
(* (p2ca_glim), chart transfer near a point, and first consequences.        *)
(* ------------------------------------------------------------------------- *)

let p2ca_set = new_definition
 `p2ca_set (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (W:num->A->bool)
           (J:real->bool) (P:num->real->A->real^N^N) (g0:A->real^N^N) <=>
    smooth_manifold_atlas top atlas /\
    (!k. open_in top (W k) /\ compact_in top (top closure_of W k) /\
         top closure_of W k SUBSET W (SUC k)) /\
    UNIONS {W k | k IN (:num)} = topspace top /\
    is_realinterval J /\ (&0) IN J /\ riemannian_metric atlas g0 /\
    (!m a b. a <= &0 /\ &0 <= b /\ a < b /\ real_interval[a,b] SUBSET J
             ==> ?N. !c. c IN atlas
                         ==> p2ca_seqhyp (IMAGE (SND c) (FST c INTER W m)) a b
                                         (\n s. metric_local atlas c (P (N + n) s))) /\
    (!K m e. compact_in top K /\ &0 < e
             ==> ?N. !n y. N <= n /\ y IN K
                           ==> lck_dist2 m (metric_local atlas (chart_at atlas y) g0)
                                           (metric_local atlas (chart_at atlas y) (P n (&0)))
                                           (SND(chart_at atlas y) y) < e)`;;

let p2ca_actx = new_definition
 `p2ca_actx (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (W:num->A->bool)
            (J:real->bool) (P:num->real->A->real^N^N) (g0:A->real^N^N)
            (nl:num->num) (cs:num->num->(A->bool)#(A->real^N)) (zs:num->num->real^N)
            (rs:num->num->real) (al:num->real) (be:num->real) (sub:num->num)
            (GG:num->num->num->real->real^N->real^N^N) <=>
    p2ca_set top atlas W J P g0 /\
    (!m. (!i. 1 <= i /\ i <= nl m
              ==> cs m i IN atlas /\ &0 < rs m i /\
                  cball(zs m i,&2 * rs m i) SUBSET
                  IMAGE (SND(cs m i)) (FST(cs m i) INTER W (SUC m))) /\
         (!y. y IN top closure_of W m
              ==> ?i. 1 <= i /\ i <= nl m /\ y IN FST(cs m i) /\
                      SND(cs m i) y IN ball(zs m i,rs m i))) /\
    (!j. al j <= &0 /\ &0 <= be j /\ al j < be j /\ real_interval[al j,be j] SUBSET J) /\
    (!a b. a <= b /\ real_interval[a,b] SUBSET J ==> ?j. al j <= a /\ b <= be j) /\
    (!m n. m < n ==> sub m < sub n) /\
    (!m i j. 1 <= i /\ i <= nl m
             ==> p2ca_loclim (ball(zs m i,&2 * rs m i)) (al j) (be j)
                   (\n s. metric_local atlas (cs m i) (P (sub n) s)) (GG m i j))`;;

(* The limit family: g0 at time 0, otherwise the pointwise limit. *)

let p2ca_glim = new_definition
 `p2ca_glim (P:num->real->A->real^N^N) (sub:num->num) (g0:A->real^N^N) =
    \s x. if s = &0 then g0 x
          else (matrify:real^(N,N)finite_prod->real^N^N)
                 (lim sequentially
                    (\n. (vectorize:real^N^N->real^(N,N)finite_prod) (P (sub n) s x)))`;;

(* A chart c near y and a chart c' around chart_inv c y: an open set O     *)
(* around y on which the transition is a diffeomorphism into a given open  *)
(* set B and the representatives of every metric are related by pullback. *)

let P2CA_CHART_TRANSFER = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c c' B y.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\ open B /\
     y IN IMAGE (SND c) (FST c) /\ chart_inv c y IN FST c' /\ SND c' (chart_inv c y) IN B
     ==> ?O. open O /\ y IN O /\ O SUBSET IMAGE (SND c) (FST c) /\
             IMAGE (chart_trans c c') O SUBSET B /\
             diffeomorphism_on O (IMAGE (chart_trans c c') O) (chart_trans c c')
                               (chart_trans c' c) /\
             (!v z. z IN O ==> metric_local atlas c v z =
                               mpullback (chart_trans c c') (metric_local atlas c' v) z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`]
                CHART_TRANS_DIFFEO) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN(LABEL_TAC "df") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `{w | w IN IMAGE (SND(c:(A->bool)#(A->real^N)))
                             (FST c INTER FST(c':(A->bool)#(A->real^N))) /\
                   chart_trans c c' w IN B}` THEN
  SUBGOAL_THEN
   `open {w | w IN IMAGE (SND(c:(A->bool)#(A->real^N)))
                         (FST c INTER FST(c':(A->bool)#(A->real^N))) /\
              chart_trans c c' w IN B}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "df" (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_INTER] THEN CONJ_TAC THENL
     [EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) y` THEN ASM_SIMP_TAC[];
      REWRITE_TAC[chart_trans] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC CMPH_DIFFEO_RESTRICT THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N)))
                      (FST c INTER FST(c':(A->bool)#(A->real^N)))` THEN
    EXISTS_TAC `IMAGE (SND(c':(A->bool)#(A->real^N)))
                      (FST(c:(A->bool)#(A->real^N)) INTER FST c')` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC PDM_METRIC_LOCAL_TRANS_C THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[]]);;

(* Chart independence of lck_dist2 near a point, for charts as pairs. *)

let P2CA_LCK_CHART_INDEP_C = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) g1 g2 c c' O y m.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
     open_in top O /\ y IN FST c /\ y IN FST c' /\ y IN O /\
     metric_field (IMAGE (SND c') (FST c' INTER O)) (metric_local atlas c' g1) /\
     metric_field (IMAGE (SND c') (FST c' INTER O)) (metric_local atlas c' g2)
     ==> lck_dist2 m (metric_local atlas c g1) (metric_local atlas c g2) (SND c y) =
         lck_dist2 m (metric_local atlas c' g1) (metric_local atlas c' g2) (SND c' y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g1:A->real^N^N`; `g2:A->real^N^N`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                 `O:A->bool`; `y:A`; `m:num`] P2CA_LCK_CHART_INDEP_LOCAL) THEN
  REWRITE_TAC[PAIR]);;

(* First consequences of the context. *)

let P2CA_ACTX_SEQHYP = prove
 (`!top atlas W J (P:num->real->A->real^N^N) g0 nl cs zs rs al be sub GG.
     p2ca_actx top atlas W J P g0 nl cs zs rs al be sub GG
     ==> !m j. ?N. !c. c IN atlas
                       ==> p2ca_seqhyp (IMAGE (SND c) (FST c INTER W m)) (al j) (be j)
                                       (\n s. metric_local atlas c (P (N + n) s))`,
  REWRITE_TAC[p2ca_actx; p2ca_set] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let P2CA_ACTX_MF = prove
 (`!top atlas W J (P:num->real->A->real^N^N) g0 nl cs zs rs al be sub GG.
     p2ca_actx top atlas W J P g0 nl cs zs rs al be sub GG
     ==> !m j. ?N. !n c s. N <= n /\ c IN atlas /\ al j <= s /\ s <= be j
                           ==> metric_field (IMAGE (SND c) (FST c INTER W m))
                                            (metric_local atlas c (P n s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "sh" o MATCH_MP P2CA_ACTX_SEQHYP) THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `j:num`] THEN
  USE_THEN "sh" (X_CHOOSE_THEN `N:num` (LABEL_TAC "N") o SPECL [`m:num`; `j:num`]) THEN
  EXISTS_TAC `N:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `c:(A->bool)#(A->real^N)`; `s:real`] THEN STRIP_TAC THEN
  USE_THEN "N" (MP_TAC o C MP (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`) o
    SPEC `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[p2ca_seqhyp] THEN
  DISCH_THEN(MP_TAC o SPECL [`n - N:num`; `s:real`] o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `N + n - N:num = n` SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]);;

(* The pieces: charts, chart images, centres in the chart images. *)

let P2CA_ACTX_PIECE = prove
 (`!top atlas W J (P:num->real->A->real^N^N) g0 nl cs zs rs al be sub GG m i j.
     p2ca_actx top atlas W J P g0 nl cs zs rs al be sub GG /\ 1 <= i /\ i <= nl m
     ==> cs m i IN atlas /\ &0 < rs m i /\
         ball(zs m i,&2 * rs m i) SUBSET IMAGE (SND(cs m i)) (FST(cs m i) INTER W (SUC m)) /\
         ball(zs m i,&2 * rs m i) SUBSET IMAGE (SND(cs m i)) (FST(cs m i)) /\
         (!y. y IN ball(zs m i,&2 * rs m i)
              ==> chart_inv (cs m i) y IN FST(cs m i) /\
                  chart_inv (cs m i) y IN W (SUC m) /\
                  SND(cs m i) (chart_inv (cs m i) y) = y) /\
         p2ca_loclim (ball(zs m i,&2 * rs m i)) (al j) (be j)
           (\n s. metric_local atlas (cs m i) (P (sub n) s)) (GG m i j)`,
  REWRITE_TAC[p2ca_actx; p2ca_set] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(cs:num->num->(A->bool)#(A->real^N)) m i IN atlas /\ &0 < rs m i /\
    cball(zs m i,&2 * rs m i) SUBSET
    IMAGE (SND(cs m i)) (FST(cs m i) INTER (W:num->A->bool) (SUC m))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ball(zs m i,&2 * rs m i) SUBSET
    IMAGE (SND((cs:num->num->(A->bool)#(A->real^N)) m i))
          (FST(cs m i) INTER (W:num->A->bool) (SUC m))`
  ASSUME_TAC THENL [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->num->(A->bool)#(A->real^N)) m i`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(y:real^N) IN IMAGE (SND((cs:num->num->(A->bool)#(A->real^N)) m i))
                        (FST(cs m i) INTER (W:num->A->bool) (SUC m))`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Identification of the limit.  In a piece chart the chart                  *)
(* representative of p2ca_glim is the local limit GG; at time 0 this uses    *)
(* the lck closeness to g0 (LCK_DIST_C0, chart independence, CMPH_SYM_QUAD_EQ *)
(* for the symmetric limit matrices).  Pointwise convergence of the          *)
(* sequence to p2ca_glim at every point and time of J.                       *)
(* ------------------------------------------------------------------------- *)

let p2ca_avars = [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
  `W:num->A->bool`; `J:real->bool`; `P:num->real->A->real^N^N`; `g0:A->real^N^N`;
  `nl:num->num`; `cs:num->num->(A->bool)#(A->real^N)`; `zs:num->num->real^N`;
  `rs:num->num->real`; `al:num->real`; `be:num->real`; `sub:num->num`;
  `GG:num->num->num->real->real^N->real^N^N`];;

let P2CA_ACTX_BASIC = prove
 (`!top atlas W J (P:num->real->A->real^N^N) g0 nl cs zs rs al be sub GG.
     p2ca_actx top atlas W J P g0 nl cs zs rs al be sub GG
     ==> smooth_manifold_atlas top atlas /\
         (!k. open_in top (W k) /\ compact_in top (top closure_of W k) /\
              top closure_of W k SUBSET W (SUC k)) /\
         UNIONS {W k | k IN (:num)} = topspace top /\
         is_realinterval J /\ (&0) IN J /\ riemannian_metric atlas g0 /\
         (!j. al j <= &0 /\ &0 <= be j /\ al j < be j /\ real_interval[al j,be j] SUBSET J) /\
         (!a b. a <= b /\ real_interval[a,b] SUBSET J ==> ?j. al j <= a /\ b <= be j) /\
         (!m n. m < n ==> sub m < sub n) /\
         (!K m e. compact_in top K /\ &0 < e
                  ==> ?N. !n y. N <= n /\ y IN K
                                ==> lck_dist2 m (metric_local atlas (chart_at atlas y) g0)
                                                (metric_local atlas (chart_at atlas y) (P n (&0)))
                                                (SND(chart_at atlas y) y) < e) /\
         (!m y. y IN top closure_of W m
                ==> ?i. 1 <= i /\ i <= nl m /\ y IN FST(cs m i) /\
                        SND(cs m i) y IN ball(zs m i,rs m i))`,
  REWRITE_TAC[p2ca_actx; p2ca_set] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let P2CA_CHART_IMAGE_OPEN_C = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c O.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ open_in top O
     ==> open(IMAGE (SND c) (FST c INTER O))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c:(A->bool)#(A->real^N)) INTER O`] CHART_IMAGE_OPEN) THEN
  ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PDM_CHART_OPEN_C]);;

let P2CA_LCK_DIST2_POS = prove
 (`!k s (G0:real^N->real^N^N) G y.
     metric_field s G0 /\ metric_field s G /\ y IN s ==> &0 <= lck_dist2 k G0 G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lck_dist2] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* A real sequence controlled by sqrt of a null sequence. *)

let P2CA_C0_LIM = prove
 (`!(f:num->real) l (d:num->real) Q (N0:num).
     (!n. N0 <= n ==> &0 <= d n /\ abs(f n - l) <= sqrt(d n) * Q) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> d n < e) /\ &0 <= Q
     ==> (f ---> l) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "b") (CONJUNCTS_THEN2 (LABEL_TAC "d") ASSUME_TAC)) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < e / (Q + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "d" (MP_TAC o SPEC `(e / (Q + &1)) pow 2`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N + N0:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "b" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "N" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `sqrt((d:num->real) n) < e / (Q + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt((e / (Q + &1)) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt((d:num->real) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `e / (Q + &1) * (Q + &1) = e` (LABEL_TAC "e") THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt((d:num->real) n) * Q` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt((d:num->real) n) * (Q + &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    USE_THEN "e" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC]);;

(* Entrywise convergence of a local limit as convergence of vectorize. *)

let P2CA_LOCLIM_VCONV = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) G t y.
     p2ca_loclim V a b Gs G /\ a <= t /\ t <= b /\ y IN V
     ==> ((\n. (vectorize:real^N^N->real^(N,N)finite_prod) (Gs n t y)) -->
          vectorize(G t y)) sequentially`,
  REWRITE_TAC[p2ca_loclim] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIM_VECTORIZE_COMPONENTWISE] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:real^N`; `p:num`; `q:num`]) THEN
  ASM_REWRITE_TAC[TENDSTO_REAL; o_DEF] THEN DISCH_THEN ACCEPT_TAC);;

let P2CA_GLIM_0 = prove
 (`!(P:num->real->A->real^N^N) sub g0. p2ca_glim P sub g0 (&0) = g0`,
  REWRITE_TAC[p2ca_glim; FUN_EQ_THM]);;

(* Away from time 0. *)

let P2CA_ACTX_IDENT_NZ = prove
 (`!top atlas W J (P:num->real->A->real^N^N) g0 nl cs zs rs al be sub GG m i j s y.
     p2ca_actx top atlas W J P g0 nl cs zs rs al be sub GG /\
     1 <= i /\ i <= nl m /\ al j <= s /\ s <= be j /\ ~(s = &0) /\
     y IN ball(zs m i,&2 * rs m i)
     ==> metric_local atlas (cs m i) (p2ca_glim P sub g0 s) y = GG m i j s y /\
         ((\n. (vectorize:real^N^N->real^(N,N)finite_prod)
                 (P (sub n) s (chart_inv (cs m i) y))) -->
          vectorize(p2ca_glim P sub g0 s (chart_inv (cs m i) y))) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CA_ACTX_BASIC) THEN
  MP_TAC(ISPECL (p2ca_avars @ [`m:num`; `i:num`; `j:num`]) P2CA_ACTX_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `x = chart_inv ((cs:num->num->(A->bool)#(A->real^N)) m i) y` THEN
  SUBGOAL_THEN `(x:A) IN FST((cs:num->num->(A->bool)#(A->real^N)) m i) /\
                SND(cs m i) x = (y:real^N)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. (vectorize:real^N^N->real^(N,N)finite_prod)
            (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                         ((P:num->real->A->real^N^N) ((sub:num->num) n) s) y)) -->
     vectorize((GG:num->num->num->real->real^N->real^N^N) m i j s y)) sequentially`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball((zs:num->num->real^N) m i,&2 * (rs:num->num->real) m i)`;
                   `(al:num->real) j`; `(be:num->real) j`;
                   `\n s. metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                       ((P:num->real->A->real^N^N) ((sub:num->num) n) s)`;
                   `(GG:num->num->num->real->real^N->real^N^N) m i j`; `s:real`; `y:real^N`]
                  P2CA_LOCLIM_VCONV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->num->(A->bool)#(A->real^N)) m i`;
                 `\n. (P:num->real->A->real^N^N) ((sub:num->num) n) s`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((GG:num->num->num->real->real^N->real^N^N) m i j s z)`;
                 `x:A`; `sequentially:(num)net`] PDM_CHART_FIELD_LIM) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `A0 = pdm_chart_field atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                     ((matrify:real^(N,N)finite_prod->real^N^N) o
                      (\z. vectorize((GG:num->num->num->real->real^N->real^N^N) m i j s z)))
                     (x:A)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `p2ca_glim (P:num->real->A->real^N^N) sub g0 s (x:A) = A0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2ca_glim] THEN
    MP_TAC(ISPECL [`sequentially:(num)net`;
                   `\n. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((P:num->real->A->real^N^N) ((sub:num->num) n) s (x:A))`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod) A0`] TENDSTO_LIM) THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->num->(A->bool)#(A->real^N)) m i`;
                 `\n. (P:num->real->A->real^N^N) ((sub:num->num) n) s`;
                 `p2ca_glim (P:num->real->A->real^N^N) sub g0 s`;
                 `y:real^N`; `sequentially:(num)net`] PDM_METRIC_LOCAL_LIM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM VECTORIZE_EQ] THEN
  MATCH_MP_TAC(ISPEC `sequentially:(num)net` LIM_UNIQUE) THEN
  EXISTS_TAC `\n. (vectorize:real^N^N->real^(N,N)finite_prod)
                    (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                 ((P:num->real->A->real^N^N) ((sub:num->num) n) s) y)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY]);;

(* At time 0: the local limit is the representative of g0. *)

let P2CA_ACTX_IDENT_Z = prove
 (`!top atlas W J (P:num->real->A->real^N^N) g0 nl cs zs rs al be sub GG m i j y.
     p2ca_actx top atlas W J P g0 nl cs zs rs al be sub GG /\
     1 <= i /\ i <= nl m /\ y IN ball(zs m i,&2 * rs m i)
     ==> metric_local atlas (cs m i) g0 y = GG m i j (&0) y /\
         ((\n. (vectorize:real^N^N->real^(N,N)finite_prod)
                 (P (sub n) (&0) (chart_inv (cs m i) y))) -->
          vectorize(g0 (chart_inv (cs m i) y))) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CA_ACTX_BASIC) THEN
  MP_TAC(ISPECL (p2ca_avars @ [`m:num`; `i:num`; `j:num`]) P2CA_ACTX_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(al:num->real) j <= &0 /\ &0 <= (be:num->real) j` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `x = chart_inv ((cs:num->num->(A->bool)#(A->real^N)) m i) y` THEN
  SUBGOAL_THEN `(x:A) IN FST((cs:num->num->(A->bool)#(A->real^N)) m i) /\
                x IN (W:num->A->bool) (SUC m) /\ SND(cs m i) x = (y:real^N)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->num->(A->bool)#(A->real^N)) m i`] PDM_CHART_OPEN_C) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. (vectorize:real^N^N->real^(N,N)finite_prod)
            (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                         ((P:num->real->A->real^N^N) ((sub:num->num) n) (&0)) y)) -->
     vectorize((GG:num->num->num->real->real^N->real^N^N) m i j (&0) y)) sequentially`
  (LABEL_TAC "vc") THENL
   [MP_TAC(ISPECL [`ball((zs:num->num->real^N) m i,&2 * (rs:num->num->real) m i)`;
                   `(al:num->real) j`; `(be:num->real) j`;
                   `\n s. metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                       ((P:num->real->A->real^N^N) ((sub:num->num) n) s)`;
                   `(GG:num->num->num->real->real^N->real^N^N) m i j`; `&0`; `y:real^N`]
                  P2CA_LOCLIM_VCONV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `S = IMAGE (SND((cs:num->num->(A->bool)#(A->real^N)) m i))
                        (FST(cs m i) INTER (W:num->A->bool) (SUC m))` THEN
  SUBGOAL_THEN `(y:real^N) IN S /\ open S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field S (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                 (g0:A->real^N^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND((cs:num->num->(A->bool)#(A->real^N)) m i)) (FST(cs m i))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; EXPAND_TAC "S" THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`SUC m`; `j:num`] o MATCH_MP P2CA_ACTX_MF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "mf")) THEN
  SUBGOAL_THEN
   `!n. N1 <= n
        ==> metric_field S (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                         ((P:num->real->A->real^N^N) n (&0)))`
  (LABEL_TAC "mfS") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN EXPAND_TAC "S" THEN
    USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. N1 <= n
        ==> lck_dist2 0 (metric_local atlas (chart_at atlas (x:A)) (g0:A->real^N^N))
                        (metric_local atlas (chart_at atlas x) ((P:num->real->A->real^N^N) n (&0)))
                        (SND(chart_at atlas x) x) =
            lck_dist2 0 (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i) g0)
                        (metric_local atlas (cs m i) (P n (&0))) y`
  (LABEL_TAC "ci") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g0:A->real^N^N`; `(P:num->real->A->real^N^N) n (&0)`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`;
                   `(cs:num->num->(A->bool)#(A->real^N)) m i`;
                   `(W:num->A->bool) (SUC m)`; `x:A`; `0`] P2CA_LCK_CHART_INDEP_C) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "mfS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* quadratic forms converge to those of g0 *)
  SUBGOAL_THEN
   `!w. ((\n. w dot (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                  ((P:num->real->A->real^N^N) ((sub:num->num) n) (&0)) y ** w))
         ---> w dot (metric_local atlas (cs m i) (g0:A->real^N^N) y ** w)) sequentially`
  (LABEL_TAC "q0") THENL
   [X_GEN_TAC `w:real^N` THEN MATCH_MP_TAC P2CA_C0_LIM THEN
    EXISTS_TAC `\n. lck_dist2 0 (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                              (g0:A->real^N^N))
                                (metric_local atlas (cs m i)
                                   ((P:num->real->A->real^N^N) ((sub:num->num) n) (&0))) y` THEN
    EXISTS_TAC `w dot (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                     (g0:A->real^N^N) y ** w)` THEN
    EXISTS_TAC `N1:num` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(LABEL_TAC "big") THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `N1 <= (sub:num->num) n` ASSUME_TAC THENL
       [USE_THEN "big" (MP_TAC o SPEC `n:num`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "mfS" (MP_TAC o C MP (ASSUME `N1 <= (sub:num->num) n`) o
        SPEC `(sub:num->num) n`) THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2CA_LCK_DIST2_POS THEN EXISTS_TAC `S:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC LCK_DIST_C0 THEN EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`{x:A}`; `0`; `e:real`] o check (fun th ->
        can (find_term ((=) `compact_in:(A)topology->(A->bool)->bool`)) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[COMPACT_IN_SING; IN_SING] THEN
      DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
      EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `N1 <= (sub:num->num) n /\ N2 <= sub n` STRIP_ASSUME_TAC THENL
       [USE_THEN "big" (MP_TAC o SPEC `n:num`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "ci" (SUBST1_TAC o SYM o C MP (ASSUME `N1 <= (sub:num->num) n`) o
        SPEC `(sub:num->num) n`) THEN
      USE_THEN "N2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_CASES_TAC `w:real^N = vec 0` THENL
       [ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      UNDISCH_TAC `metric_field S (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                                (g0:A->real^N^N))` THEN
      REWRITE_TAC[metric_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N` o last o CONJUNCTS) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* and to those of the local limit *)
  SUBGOAL_THEN
   `!w. ((\n. w dot (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                  ((P:num->real->A->real^N^N) ((sub:num->num) n) (&0)) y ** w))
         ---> w dot ((GG:num->num->num->real->real^N->real^N^N) m i j (&0) y ** w)) sequentially`
  (LABEL_TAC "q1") THENL
   [X_GEN_TAC `w:real^N` THEN REWRITE_TAC[TENDSTO_REAL; o_DEF] THEN
    MP_TAC(ISPECL [`sequentially:(num)net`; `\v:real^N. lift(w dot v)`;
                   `\n. metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                          ((P:num->real->A->real^N^N) ((sub:num->num) n) (&0)) y ** w`;
                   `(GG:num->num->num->real->real^N->real^N^N) m i j (&0) y ** w`] LIM_LINEAR) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [USE_THEN "vc" (MP_TAC o REWRITE_RULE[GSYM LIM_MATRIX_VECTORIZE]) THEN
      DISCH_THEN(ACCEPT_TAC o SPEC `w:real^N`);
      REWRITE_TAC[linear; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i) (g0:A->real^N^N) y =
    (GG:num->num->num->real->real^N->real^N^N) m i j (&0) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPH_SYM_QUAD_EQ THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `metric_field S (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                                  (g0:A->real^N^N))` THEN
      REWRITE_TAC[metric_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N` o last o CONJUNCTS) THEN
      ASM_MESON_TAC[];
      UNDISCH_TAC `p2ca_loclim (ball((zs:num->num->real^N) m i,&2 * (rs:num->num->real) m i))
                     ((al:num->real) j) ((be:num->real) j)
                     (\n s. metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                         ((P:num->real->A->real^N^N) ((sub:num->num) n) s))
                     ((GG:num->num->num->real->real^N->real^N^N) m i j)` THEN
      REWRITE_TAC[p2ca_loclim] THEN
      DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[metric_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N` o last o CONJUNCTS) THEN
      ASM_MESON_TAC[];
      X_GEN_TAC `w:real^N` THEN MATCH_MP_TAC(ISPEC `sequentially:(num)net` REALLIM_UNIQUE) THEN
      EXISTS_TAC `\n. w dot (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                              ((P:num->real->A->real^N^N) ((sub:num->num) n) (&0)) y ** w)` THEN
      ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->num->(A->bool)#(A->real^N)) m i`;
                 `\n. (P:num->real->A->real^N^N) ((sub:num->num) n) (&0)`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                     (g0:A->real^N^N) z)`;
                 `x:A`; `sequentially:(num)net`] PDM_CHART_FIELD_LIM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(matrify:real^(N,N)finite_prod->real^N^N) o
    (\z. vectorize(metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                (g0:A->real^N^N) z)) =
    metric_local atlas (cs m i) g0`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->num->(A->bool)#(A->real^N)) m i`; `g0:A->real^N^N`; `x:A`]
                PDM_CHART_FIELD_METRIC_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* Both cases, and pointwise convergence everywhere on the manifold. *)

let P2CA_ACTX_IDENT = prove
 (`!top atlas W J (P:num->real->A->real^N^N) g0 nl cs zs rs al be sub GG m i j s y.
     p2ca_actx top atlas W J P g0 nl cs zs rs al be sub GG /\
     1 <= i /\ i <= nl m /\ al j <= s /\ s <= be j /\ y IN ball(zs m i,&2 * rs m i)
     ==> metric_local atlas (cs m i) (p2ca_glim P sub g0 s) y = GG m i j s y /\
         ((\n. (vectorize:real^N^N->real^(N,N)finite_prod)
                 (P (sub n) s (chart_inv (cs m i) y))) -->
          vectorize(p2ca_glim P sub g0 s (chart_inv (cs m i) y))) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `s = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[P2CA_GLIM_0] THEN
    MP_TAC(ISPECL (p2ca_avars @ [`m:num`; `i:num`; `j:num`; `y:real^N`]) P2CA_ACTX_IDENT_Z) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL (p2ca_avars @ [`m:num`; `i:num`; `j:num`; `s:real`; `y:real^N`])
                  P2CA_ACTX_IDENT_NZ) THEN
    ASM_REWRITE_TAC[]]);;

let P2CA_ACTX_CONV = prove
 (`!top atlas W J (P:num->real->A->real^N^N) g0 nl cs zs rs al be sub GG s x.
     p2ca_actx top atlas W J P g0 nl cs zs rs al be sub GG /\ s IN J /\ x IN topspace top
     ==> ((\n. (vectorize:real^N^N->real^(N,N)finite_prod) (P (sub n) s x)) -->
          vectorize(p2ca_glim P sub g0 s x)) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CA_ACTX_BASIC) THEN
  SUBGOAL_THEN `?m. (x:A) IN top closure_of (W:num->A->bool) m` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:A) IN UNIONS {(W:num->A->bool) k | k IN (:num)}` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN EXISTS_TAC `m:num` THEN
    MP_TAC(ISPECL [`top:A topology`; `(W:num->A->bool) m`] CLOSURE_OF_SUBSET) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `x:A`] o check (fun th ->
    can (find_term ((=) `(closure_of):(A)topology->(A->bool)->(A->bool)`)) (concl th) &&
    is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `s:real`] o check (fun th ->
    can (find_term ((=) `real_interval`)) (concl th) && is_forall (concl th) &&
    can (SPECL [`s:real`; `s:real`]) th)) THEN
  REWRITE_TAC[REAL_LE_REFL; REAL_INTERVAL_SING; SING_SUBSET] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL (p2ca_avars @ [`m:num`; `i:num`; `j:num`]) P2CA_ACTX_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2ca_avars @ [`m:num`; `i:num`; `j:num`; `s:real`;
                 `SND((cs:num->num->(A->bool)#(A->real^N)) m i) (x:A)`]) P2CA_ACTX_IDENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(zs:num->num->real^N) m i`; `(rs:num->num->real) m i`;
                   `&2 * (rs:num->num->real) m i`] SUBSET_BALL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->num->(A->bool)#(A->real^N)) m i`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The limit family is a Riemannian metric at every time of J,               *)
(* a Ricci flow on every compact interval of J with interior, and the        *)
(* sequence converges to it in every C^k, uniformly on compact sets and     *)
(* compact time intervals of J, read in the preferred charts.  Every chart  *)
(* point is near a piece (P2CA_ACTX_LOCAL), where the representative is the  *)
(* pullback of the local limit by the chart transition.                      *)
(* ------------------------------------------------------------------------- *)

let P2CA_ACTX_LOCAL = prove
 (`!top atlas W J (P:num->real->A->real^N^N) g0 nl cs zs rs al be sub GG c y a b.
     p2ca_actx top atlas W J P g0 nl cs zs rs al be sub GG /\ c IN atlas /\
     y IN IMAGE (SND c) (FST c) /\ a <= b /\ real_interval[a,b] SUBSET J
     ==> ?m i j O. 1 <= i /\ i <= nl m /\ al j <= a /\ b <= be j /\
                   open O /\ y IN O /\ O SUBSET IMAGE (SND c) (FST c) /\
                   IMAGE (chart_trans c (cs m i)) O SUBSET ball(zs m i,&2 * rs m i) /\
                   diffeomorphism_on O (IMAGE (chart_trans c (cs m i)) O)
                                     (chart_trans c (cs m i)) (chart_trans (cs m i) c) /\
                   (!v z. z IN O
                          ==> metric_local atlas c v z =
                              mpullback (chart_trans c (cs m i)) (metric_local atlas (cs m i) v) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CA_ACTX_BASIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^N)) y` THEN
  SUBGOAL_THEN `(x:A) IN FST(c:(A->bool)#(A->real^N)) /\ SND c x = y` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?m. (x:A) IN top closure_of (W:num->A->bool) m` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:A) IN UNIONS {(W:num->A->bool) k | k IN (:num)}` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN EXISTS_TAC `m:num` THEN
    MP_TAC(ISPECL [`top:A topology`; `(W:num->A->bool) m`] CLOSURE_OF_SUBSET) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `x:A`] o check (fun th ->
    can (find_term ((=) `(closure_of):(A)topology->(A->bool)->(A->bool)`)) (concl th) &&
    is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `b:real`] o check (fun th ->
    can (find_term ((=) `real_interval`)) (concl th) && is_forall (concl th) &&
    can (SPECL [`a:real`; `b:real`]) th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL (p2ca_avars @ [`m:num`; `i:num`; `j:num`]) P2CA_ACTX_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `(cs:num->num->(A->bool)#(A->real^N)) m i`;
                 `ball((zs:num->num->real^N) m i,&2 * (rs:num->num->real) m i)`; `y:real^N`]
                P2CA_CHART_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN
    MP_TAC(ISPECL [`(zs:num->num->real^N) m i`; `(rs:num->num->real) m i`;
                   `&2 * (rs:num->num->real) m i`] SUBSET_BALL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `i:num`; `j:num`; `O:real^N->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* Riemannian metrics. *)

let P2CA_ACTX_RIEM = prove
 (`!top atlas W J (P:num->real->A->real^N^N) g0 nl cs zs rs al be sub GG s.
     p2ca_actx top atlas W J P g0 nl cs zs rs al be sub GG /\ s IN J
     ==> riemannian_metric atlas (p2ca_glim P sub g0 s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CA_ACTX_BASIC) THEN
  REWRITE_TAC[riemannian_metric] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_LOCAL THEN
  CONJ_TAC THENL [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2ca_avars @ [`c:(A->bool)#(A->real^N)`; `y:real^N`; `s:real`; `s:real`])
                P2CA_ACTX_LOCAL) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_INTERVAL_SING; SING_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num`
    (X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `O:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL (p2ca_avars @ [`m:num`; `i:num`; `j:num`]) P2CA_ACTX_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `mpullback (chart_trans c ((cs:num->num->(A->bool)#(A->real^N)) m i))
                        ((GG:num->num->num->real->real^N->real^N^N) m i j s)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (chart_trans c ((cs:num->num->(A->bool)#(A->real^N)) m i)) O`;
      `chart_trans ((cs:num->num->(A->bool)#(A->real^N)) m i) c`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `ball((zs:num->num->real^N) m i,&2 * (rs:num->num->real) m i)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `p2ca_loclim (ball((zs:num->num->real^N) m i,&2 * (rs:num->num->real) m i))
                     ((al:num->real) j) ((be:num->real) j)
                     (\n s. metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                         ((P:num->real->A->real^N^N) ((sub:num->num) n) s))
                     ((GG:num->num->num->real->real^N->real^N^N) m i j)` THEN
      REWRITE_TAC[p2ca_loclim] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `diffeomorphism_on (O:real^N->bool)
                     (IMAGE (chart_trans c ((cs:num->num->(A->bool)#(A->real^N)) m i)) O)
                     (chart_trans c (cs m i)) (chart_trans (cs m i) c)` THEN
      SIMP_TAC[diffeomorphism_on]];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[mpullback] THEN
    SUBGOAL_THEN
     `metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
        (p2ca_glim (P:num->real->A->real^N^N) sub g0 s)
        (chart_trans c (cs m i) z) =
      (GG:num->num->num->real->real^N->real^N^N) m i j s (chart_trans c (cs m i) z)`
    (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL (p2ca_avars @ [`m:num`; `i:num`; `j:num`; `s:real`;
                   `chart_trans c ((cs:num->num->(A->bool)#(A->real^N)) m i) z`])
                  P2CA_ACTX_IDENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; SIMP_TAC[]]]);;

(* Ricci flows. *)

let P2CA_ACTX_RF = prove
 (`!top atlas W J (P:num->real->A->real^N^N) g0 nl cs zs rs al be sub GG a b.
     p2ca_actx top atlas W J P g0 nl cs zs rs al be sub GG /\
     a < b /\ real_interval[a,b] SUBSET J
     ==> ricci_flow_on (top,atlas) a b (p2ca_glim P sub g0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CA_ACTX_BASIC) THEN
  MATCH_MP_TAC P2CA_RICCI_FLOW_ON_CHARTS THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MATCH_MP_TAC RFA_LRICCI_FLOW_UNION THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2ca_avars @ [`c:(A->bool)#(A->real^N)`; `y:real^N`; `a:real`; `b:real`])
                P2CA_ACTX_LOCAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num`
    (X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `O:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z. z IN O ==> chart_trans c ((cs:num->num->(A->bool)#(A->real^N)) m i) z IN
                   ball((zs:num->num->real^N) m i,&2 * (rs:num->num->real) m i)`
  (LABEL_TAC "tb") THENL
   [UNDISCH_TAC `IMAGE (chart_trans c ((cs:num->num->(A->bool)#(A->real^N)) m i)) O SUBSET
                 ball((zs:num->num->real^N) m i,&2 * (rs:num->num->real) m i)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2ca_avars @ [`m:num`; `i:num`; `j:num`]) P2CA_ACTX_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_LRICCI_FLOW_EQ THEN
  EXISTS_TAC `\t. mpullback (chart_trans c ((cs:num->num->(A->bool)#(A->real^N)) m i))
                            ((GG:num->num->num->real->real^N->real^N^N) m i j t)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRICCI_FLOW_PULLBACK THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (chart_trans c ((cs:num->num->(A->bool)#(A->real^N)) m i)) O`;
      `chart_trans ((cs:num->num->(A->bool)#(A->real^N)) m i) c`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_LRICCI_FLOW_SUBSET THEN
    EXISTS_TAC `ball((zs:num->num->real^N) m i,&2 * (rs:num->num->real) m i)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CA_LRICCI_FLOW_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`(al:num->real) j`; `(be:num->real) j`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2ca_loclim (ball((zs:num->num->real^N) m i,&2 * (rs:num->num->real) m i))
                     ((al:num->real) j) ((be:num->real) j)
                     (\n s. metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                         ((P:num->real->A->real^N^N) ((sub:num->num) n) s))
                     ((GG:num->num->num->real->real^N->real^N^N) m i j)` THEN
      SIMP_TAC[p2ca_loclim; ETA_AX];
      UNDISCH_TAC `diffeomorphism_on (O:real^N->bool)
                     (IMAGE (chart_trans c ((cs:num->num->(A->bool)#(A->real^N)) m i)) O)
                     (chart_trans c (cs m i)) (chart_trans (cs m i) c)` THEN
      SIMP_TAC[diffeomorphism_on]];
    MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[mpullback] THEN
    SUBGOAL_THEN
     `metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
        (p2ca_glim (P:num->real->A->real^N^N) sub g0 t)
        (chart_trans c (cs m i) z) =
      (GG:num->num->num->real->real^N->real^N^N) m i j t (chart_trans c (cs m i) z)`
    (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL (p2ca_avars @ [`m:num`; `i:num`; `j:num`; `t:real`;
                   `chart_trans c ((cs:num->num->(A->bool)#(A->real^N)) m i) z`])
                  P2CA_ACTX_IDENT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]]]);;

(* Finitely many eventual properties hold together. *)

let P2CA_FINITE_EVENTUALLY = prove
 (`!(Pr:num->num->bool) n0.
     (!i. 1 <= i /\ i <= n0 ==> ?N. !n. N <= n ==> Pr i n)
     ==> ?N. !i n. 1 <= i /\ i <= n0 /\ N <= n ==> Pr i n`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `0` THEN MESON_TAC[ARITH_RULE `~(1 <= i /\ i <= 0)`];
    DISCH_THEN(LABEL_TAC "h") THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "h" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
    USE_THEN "h" (MP_TAC o SPEC `SUC n0`) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
    EXISTS_TAC `N1 + N2:num` THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `i = SUC n0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN USE_THEN "N2" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "N1" MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

(* Uniform C^k convergence on compact sets and compact time intervals. *)

let P2CA_ACTX_LCK = prove
 (`!top atlas W J (P:num->real->A->real^N^N) g0 nl cs zs rs al be sub GG a b K k e.
     p2ca_actx top atlas W J P g0 nl cs zs rs al be sub GG /\
     real_interval[a,b] SUBSET J /\ compact_in top K /\ &0 < e
     ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN K
                     ==> lck_dist2 k (metric_local atlas (chart_at atlas y) (p2ca_glim P sub g0 s))
                                     (metric_local atlas (chart_at atlas y) (P (sub n) s))
                                     (SND(chart_at atlas y) y) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CA_ACTX_BASIC) THEN
  ASM_CASES_TAC `a <= b` THENL
   [ALL_TAC; EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `b:real`] o check (fun th ->
    can (find_term ((=) `real_interval`)) (concl th) && is_forall (concl th) &&
    can (SPECL [`a:real`; `b:real`]) th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `W:num->A->bool`; `K:A->bool`] P2CA_COMPACT_IN_W) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(X_CHOOSE_TAC `m:num`)] THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET top closure_of (W:num->A->bool) m /\
                top closure_of W m SUBSET W (SUC m)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(W:num->A->bool) m` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  (* uniform bounds on the pieces of level m *)
  MP_TAC(ISPECL
   [`\i n. !t z. al (j:num) <= t /\ t <= be j /\
                 z IN cball((zs:num->num->real^N) m i,(rs:num->num->real) m i)
                 ==> lck_dist2 k ((GG:num->num->num->real->real^N->real^N^N) m i j t)
                       (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                          ((P:num->real->A->real^N^N) ((sub:num->num) n) t)) z < e`;
    `(nl:num->num) m`] P2CA_FINITE_EVENTUALLY) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL (p2ca_avars @ [`m:num`; `i:num`; `j:num`]) P2CA_ACTX_PIECE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `p2ca_loclim (ball((zs:num->num->real^N) m i,&2 * (rs:num->num->real) m i))
                   ((al:num->real) j) ((be:num->real) j)
                   (\n s. metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                       ((P:num->real->A->real^N^N) ((sub:num->num) n) s))
                   ((GG:num->num->num->real->real^N->real^N^N) m i j)` THEN
    REWRITE_TAC[p2ca_loclim] THEN
    DISCH_THEN(MP_TAC o SPECL [`cball((zs:num->num->real^N) m i,(rs:num->num->real) m i)`;
                               `k:num`; `e:real`] o last o CONJUNCTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[COMPACT_CBALL] THEN REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN
      ASM_REAL_ARITH_TAC;
      MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`SUC m`; `j:num`] o MATCH_MP P2CA_ACTX_MF) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  EXISTS_TAC `N1 + N2:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `N1 <= (sub:num->num) n /\ N2 <= sub n /\ N1 <= n` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(al:num->real) j <= s /\ s <= (be:num->real) j /\ s IN J` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    UNDISCH_TAC `real_interval[a,b] SUBSET J` THEN REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN top closure_of (W:num->A->bool) m /\ y IN W (SUC m) /\
                y IN topspace top`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; OPEN_IN_SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `y:A`] o check (fun th ->
    can (find_term ((=) `(closure_of):(A)topology->(A->bool)->(A->bool)`)) (concl th) &&
    is_forall (concl th) && can (SPECL [`m:num`; `y:A`]) th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL (p2ca_avars @ [`m:num`; `i:num`; `j:num`]) P2CA_ACTX_PIECE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `p2ca_glim (P:num->real->A->real^N^N) sub g0 s`;
                 `(P:num->real->A->real^N^N) ((sub:num->num) n) s`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)`;
                 `(cs:num->num->(A->bool)#(A->real^N)) m i`;
                 `(W:num->A->bool) (SUC m)`; `y:A`; `k:num`] P2CA_LCK_CHART_INDEP_C) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND((cs:num->num->(A->bool)#(A->real^N)) m i)) (FST(cs m i))` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL (p2ca_avars @ [`s:real`]) P2CA_ACTX_RIEM) THEN
        ASM_REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        CONJ_TAC THENL
         [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
          MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
          ASM_REWRITE_TAC[];
          SET_TAC[]]];
      USE_THEN "N2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`k:num`;
                 `metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                    (p2ca_glim (P:num->real->A->real^N^N) sub g0 s)`;
                 `(GG:num->num->num->real->real^N->real^N^N) m i j s`;
                 `metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                    ((P:num->real->A->real^N^N) ((sub:num->num) n) s)`;
                 `metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                    ((P:num->real->A->real^N^N) ((sub:num->num) n) s)`;
                 `ball((zs:num->num->real^N) m i,&2 * (rs:num->num->real) m i)`;
                 `SND((cs:num->num->(A->bool)#(A->real^N)) m i) (y:A)`] LCK_DIST2_LOCAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(zs:num->num->real^N) m i`; `(rs:num->num->real) m i`;
                     `&2 * (rs:num->num->real) m i`] SUBSET_BALL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL (p2ca_avars @ [`m:num`; `i:num`; `j:num`; `s:real`; `z:real^N`])
                    P2CA_ACTX_IDENT) THEN
      ASM_SIMP_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!t z. (al:num->real) j <= t /\ t <= (be:num->real) j /\
          z IN cball((zs:num->num->real^N) m i,(rs:num->num->real) m i)
          ==> lck_dist2 k ((GG:num->num->num->real->real^N->real^N^N) m i j t)
                (metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                   ((P:num->real->A->real^N^N) ((sub:num->num) n) t)) z < e`
  MP_TAC THENL [USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The assembly theorem.  In the setting p2ca_set a subsequence              *)
(* of P converges, in every C^k uniformly on compact sets and compact time   *)
(* intervals of J (read in the preferred charts), to a family g with         *)
(* g 0 = g0 which is a Riemannian metric at every time of J and a Ricci flow *)
(* on every compact interval of J with interior.  For J = {0} the sequence  *)
(* itself and g = g0 do; otherwise chart pieces level by level, countably    *)
(* many admissible intervals and the diagonal subsequence give the context  *)
(* p2ca_actx, and g is p2ca_glim.                                            *)
(* ------------------------------------------------------------------------- *)

let P2CA_ASSEMBLY = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W J (P:num->real->A->real^N^N) g0.
     p2ca_set top atlas W J P g0
     ==> ?(sub:num->num) g. (!m n. m < n ==> sub m < sub n) /\ g (&0) = g0 /\
                 (!s. s IN J ==> riemannian_metric atlas (g s)) /\
                 (!a b. a < b /\ real_interval[a,b] SUBSET J
                        ==> ricci_flow_on (top,atlas) a b g) /\
                 (!a b K k e. real_interval[a,b] SUBSET J /\ compact_in top K /\ &0 < e
                              ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN K
                                              ==> lck_dist2 k
                                                    (metric_local atlas (chart_at atlas y) (g s))
                                                    (metric_local atlas (chart_at atlas y)
                                                                  (P (sub n) s))
                                                    (SND(chart_at atlas y) y) < e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2ca_set]) THEN
  ASM_CASES_TAC `J = {&0}` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `!a b. ~(a < b /\ real_interval[a,b] SUBSET {&0})` (LABEL_TAC "nrf") THENL
     [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_SING] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `a:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!a b K k e. real_interval[a,b] SUBSET {&0} /\ compact_in top K /\ &0 < e
                  ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN K
                                  ==> lck_dist2 k
                                        (metric_local atlas (chart_at atlas y) (g0:A->real^N^N))
                                        (metric_local atlas (chart_at atlas y)
                                                      ((P:num->real->A->real^N^N) n s))
                                        (SND(chart_at atlas y) y) < e`
    (LABEL_TAC "lk") THENL
     [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_SING] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`K:A->bool`; `k:num`; `e:real`] o check (fun th ->
        can (find_term ((=) `compact_in:(A)topology->(A->bool)->bool`)) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `y:A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `s = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `\n:num. n` THEN EXISTS_TAC `\s:real. (g0:A->real^N^N)` THEN
    REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `J:real->bool` P2CA_INTERVALS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `al:num->real` (X_CHOOSE_THEN `be:num->real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:num->A->bool`]
                P2CA_PIECE_LEVELS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `nl:num->num` (X_CHOOSE_THEN `cs:num->num->(A->bool)#(A->real^N)`
    (X_CHOOSE_THEN `zs:num->num->real^N` (X_CHOOSE_THEN `rs:num->num->real`
    (LABEL_TAC "pc"))))) THEN
  MP_TAC(ISPECL
   [`\d. 1 <= NUMFST(NUMSND d) /\ NUMFST(NUMSND d) <= (nl:num->num) (NUMFST d)`;
    `\d. ball((zs:num->num->real^N) (NUMFST d) (NUMFST(NUMSND d)),
              &2 * (rs:num->num->real) (NUMFST d) (NUMFST(NUMSND d)))`;
    `\d. (al:num->real) (NUMSND(NUMSND d))`; `\d. (be:num->real) (NUMSND(NUMSND d))`;
    `\d n s. metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) (NUMFST d)
                                   (NUMFST(NUMSND d)))
                          ((P:num->real->A->real^N^N) n s)`] P2CA_DIAG) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `d:num` THEN
    MAP_EVERY ABBREV_TAC [`m = NUMFST d`; `i = NUMFST(NUMSND d)`; `j = NUMSND(NUMSND d)`] THEN
    STRIP_TAC THEN REWRITE_TAC[OPEN_BALL] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(cs:num->num->(A->bool)#(A->real^N)) m i IN atlas /\ &0 < (rs:num->num->real) m i /\
      cball((zs:num->num->real^N) m i,&2 * rs m i) SUBSET
      IMAGE (SND(cs m i)) (FST(cs m i) INTER (W:num->A->bool) (SUC m))`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "pc" (MP_TAC o SPEC `m:num`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`SUC m`; `(al:num->real) j`; `(be:num->real) j`] o
      check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "p2ca_seqhyp"
                                                 with Failure _ -> false)) (concl th) &&
                       is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num`
      (MP_TAC o SPEC `(cs:num->num->(A->bool)#(A->real^N)) m i`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `N:num` THEN
    MATCH_MP_TAC P2CA_SEQHYP_SUBSET THEN
    EXISTS_TAC `IMAGE (SND((cs:num->num->(A->bool)#(A->real^N)) m i))
                      (FST(cs m i) INTER (W:num->A->bool) (SUC m))` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dg"))) THEN
  SUBGOAL_THEN
   `?GG:num->num->num->real->real^N->real^N^N.
      !m i j. 1 <= i /\ i <= (nl:num->num) m
              ==> p2ca_loclim (ball((zs:num->num->real^N) m i,&2 * (rs:num->num->real) m i))
                    ((al:num->real) j) ((be:num->real) j)
                    (\n s. metric_local atlas ((cs:num->num->(A->bool)#(A->real^N)) m i)
                                        ((P:num->real->A->real^N^N) ((sub:num->num) n) s))
                    (GG m i j)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN MAP_EVERY X_GEN_TAC [`m:num`; `i:num`; `j:num`] THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN STRIP_TAC THEN
    USE_THEN "dg" (MP_TAC o SPEC `NUMPAIR m (NUMPAIR i j)`) THEN
    REWRITE_TAC[NUMPAIR_DEST] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2ca_actx top atlas W J (P:num->real->A->real^N^N) g0 nl cs zs rs al be sub GG`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2ca_actx] THEN ASM_REWRITE_TAC[] THEN USE_THEN "pc" ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL p2ca_avars P2CA_ACTX_RIEM) THEN
  MP_TAC(ISPECL p2ca_avars P2CA_ACTX_RF) THEN
  MP_TAC(ISPECL p2ca_avars P2CA_ACTX_LCK) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `p2ca_glim (P:num->real->A->real^N^N) sub g0`] THEN
  ASM_REWRITE_TAC[P2CA_GLIM_0]);;


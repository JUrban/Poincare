(* ========================================================================= *)
(* pc_p2a_seg: segments of curves (for L2, L4, L12, L7).  Chart curves of a  *)
(* region give curve pieces satisfying the conditions of p2a_adm on a time   *)
(* interval; an admissible curve can be continued by such a piece, and a     *)
(* piece of an admissible curve can be replaced by one.                      *)
(*                                                                           *)
(* First: C^1 from pointwise derivatives, the chain rule with a smooth chart *)
(* transition, and the corner-free p2a_pc1 of region chart curves.           *)
(* ========================================================================= *)

needs "src/pc_p2a_lconv.ml";;
needs "src/pc_p2a_minr.ml";;

prioritize_real();;
type_invention_error := true;;

let P2A_CD1_FROM_AT = prove
 (`!(f:real^1->real^N) f' S.
     (!x. x IN S ==> (f has_vector_derivative f' x) (at x) /\ f' continuous (at x))
     ==> continuously_differentiable 1 S f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[num_CONV `1`; continuously_differentiable] THEN
  EXISTS_TAC `\x:real^1 h:real^1. drop h % (f':real^1->real^N) x` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    ASM_REWRITE_TAC[GSYM has_vector_derivative];
    X_GEN_TAC `h:real^1` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC CONTINUOUS_CMUL THEN ASM_MESON_TAC[]]);;

(* The derivative of T o Z, T smooth on an open set, is continuous where Z  *)
(* and its derivative are.                                                   *)

let P2A_FRECHET_COMPOSE_CONT = prove
 (`!(Tm:real^N->real^M) O (Z:real^1->real^N) Z' x.
     open O /\ smooth_map_on O Tm /\ Z x IN O /\ Z continuous (at x) /\ Z' continuous (at x)
     ==> (\x. frechet_derivative Tm (at (Z x)) (Z' x)) continuous (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!h. (\y. frechet_derivative (Tm:real^N->real^M) (at y) h) continuous_on O`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`0`; `O:real^N->bool`; `Tm:real^N->real^M`]
                  CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
    REWRITE_TAC[continuously_differentiable] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\ !x'. dist(x',x) < d ==> (Z:real^1->real^N) x' IN O`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(O:real^N->bool)` THEN REWRITE_TAC[open_def] THEN
    DISCH_THEN(MP_TAC o SPEC `(Z:real^1->real^N) x`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(Z:real^1->real^N) continuous (at x)` THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
  EXISTS_TAC `\x':real^1. vsum(1..dimindex(:N))
               (\i. ((Z':real^1->real^N) x')$i %
                    frechet_derivative (Tm:real^N->real^M) (at (Z x')) (basis i))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x':real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `linear(frechet_derivative (Tm:real^N->real^M) (at ((Z:real^1->real^N) x')))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^N->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_LIFT_COMPONENT_COMPOSE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x':real^1. frechet_derivative (Tm:real^N->real^M) (at ((Z:real^1->real^N) x')) (basis i)) =
    (\y. frechet_derivative Tm (at y) (basis i)) o Z`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `basis i:real^N` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "continuous_on")) (concl th))) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]);;

(* p2a_pc1 for curves given by a region chart curve Zs (a function of tau)  *)
(* that is differentiable with continuous derivative at each time.          *)

let P2A_CHART_CURVE_PC1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt W a' b'' U (phi:A->real^N) (Zs:real^1->real^N) Zs' b1 b2.
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\ b1 < b2 /\
     (!tau. b1 <= tau /\ tau <= b2 ==> a' < tt - tau /\ tt - tau <= b'') /\
     (!tau. b1 <= tau /\ tau <= b2
            ==> Zs(lift tau) IN IMAGE phi (U INTER W) /\
                (Zs has_vector_derivative Zs'(lift tau)) (at (lift tau)) /\
                Zs' continuous (at (lift tau)))
     ==> !S c. S SUBSET {s | b1 <= drop s /\ drop s <= b2 /\
                             c IN p2a_vatlas V (tt - drop s) /\
                             chart_inv (U INTER W,phi) (Zs s) IN FST c}
               ==> continuously_differentiable 1 S
                     (\s. SND c (chart_inv (U INTER W,phi) (Zs s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC P2A_CD1_FROM_AT THEN
  EXISTS_TAC `\s:real^1. frechet_derivative (chart_trans (U INTER W:A->bool,phi:A->real^N) c)
                                            (at ((Zs:real^1->real^N) s)) (Zs' s)` THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `b1 <= drop x /\ drop x <= b2 /\
                (c:(A->bool)#(A->real^N)) IN p2a_vatlas V (tt - drop x) /\
                chart_inv (U INTER W,phi:A->real^N) ((Zs:real^1->real^N) x) IN FST c`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `drop x` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `Zs':real^1->real^N`)) (concl th))) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `drop x` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `b'':real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - drop x`; `c:(A->bool)#(A->real^N)`]
                P2A_REGION_SLICE_CHART) THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ABBREV_TAC `O = IMAGE (phi:A->real^N) ((U INTER W) INTER FST(c:(A->bool)#(A->real^N)))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(Zs:real^1->real^N) x IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN
    UNDISCH_TAC `(Zs:real^1->real^N) x IN IMAGE (phi:A->real^N) (U INTER W)` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `q:A` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    SUBGOAL_THEN `chart_inv (U INTER W,phi:A->real^N) ((Zs:real^1->real^N) x) = q`
    (fun th -> ASM_MESON_TAC[th; IN_INTER]) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b''`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b''`;
                   `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `q:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `b'':real`]
                  P2A_REGION_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(\s. SND (c:(A->bool)#(A->real^N)) (chart_inv (U INTER W,phi:A->real^N)
                                                     ((Zs:real^1->real^N) s))) =
                  chart_trans (U INTER W,phi) c o Zs`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; chart_trans]; ALL_TAC] THEN
    REWRITE_TAC[has_vector_derivative] THEN
    SUBGOAL_THEN
     `(\h. drop h % frechet_derivative (chart_trans (U INTER W:A->bool,phi:A->real^N) c)
                       (at ((Zs:real^1->real^N) x)) (Zs' x)) =
      frechet_derivative (chart_trans (U INTER W,phi) c) (at (Zs x)) o (\h. drop h % Zs' x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC LINEAR_CMUL THEN
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_REWRITE_TAC[GSYM has_vector_derivative] THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2A_FRECHET_COMPOSE_CONT THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Segments (curve pieces on [b1,b2] satisfying the conditions of p2a_adm    *)
(* there), continuation of an admissible curve by a segment (P2A_SEG_GLUE,   *)
(* after the gluing lemmas of pc_p2a_minr), and the replacement of a piece   *)
(* of an admissible curve (P2A_REPLACE).                                     *)
(* ========================================================================= *)

let p2a_lseg = new_definition
 `p2a_lseg (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
              (real->A->real^N^N)) (tt:real) (b1:real) (b2:real) (sig:real->A) <=>
    &0 < b1 /\ b1 < b2 /\
    (!tau. b1 <= tau /\ tau <= b2 ==> sig tau IN topspace(p2a_vtop V (tt - tau))) /\
    (!tau0 O. b1 <= tau0 /\ tau0 <= b2 /\ open_in (p2a_vtop V (tt - tau0)) O /\
              sig tau0 IN O
              ==> ?d. &0 < d /\
                      !tau. b1 <= tau /\ tau <= b2 /\ abs(tau - tau0) < d ==> sig tau IN O) /\
    (?P. p2a_pc1 V tt sig b1 b2 P) /\
    (!c. c IN p2a_vatlas V (tt - b1) /\ sig b1 IN FST c
         ==> ?d. &0 < d /\
                 continuously_differentiable 1
                   {s | b1 <= drop s /\ drop s <= b1 + d /\ drop s <= b2 /\
                        p2a_vatlas V (tt - drop s) = p2a_vatlas V (tt - b1) /\
                        sig(drop s) IN FST c}
                   (\s. SND c (sig(drop s)))) /\
    (!tau. b1 <= tau /\ tau <= b2 ==> p2a_smooth V (sig tau) (tt - tau)) /\
    p2a_L_integrand V tt sig b2 real_integrable_on real_interval[b1,b2]`;;

let P2A_SEG_GLUE_CONT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt (gamma:real->A) gamma' gg b b'.
        (!tau0 O. b' <= tau0 /\ tau0 <= b /\ open_in (p2a_vtop V (tt - tau0)) O /\
                  gamma tau0 IN O
                  ==> ?d. &0 < d /\
                          !tau. b' <= tau /\ tau <= b /\ abs(tau - tau0) < d
                                ==> gamma tau IN O) /\
        (!tau0 O. &0 <= tau0 /\ tau0 <= b' /\ open_in (p2a_vtop V (tt - tau0)) O /\
                  gamma' tau0 IN O
                  ==> ?d. &0 < d /\
                          !tau. &0 <= tau /\ tau <= b' /\ abs(tau - tau0) < d
                                ==> gamma' tau IN O) /\
        b' < b /\
        (!tau. tau <= b' ==> gg tau = gamma' tau) /\
        (!tau. b' <= tau ==> gg tau = gamma tau)
        ==> !tau0 O. &0 <= tau0 /\ tau0 <= b /\
                     open_in (p2a_vtop V (tt - tau0)) O /\ gg tau0 IN O
                     ==> ?d. &0 < d /\
                             !tau. &0 <= tau /\ tau <= b /\ abs(tau - tau0) < d
                                   ==> gg tau IN O`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C") (CONJUNCTS_THEN2 (LABEL_TAC "C'")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "E1")
     (LABEL_TAC "E2"))))) THEN
  MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `tau0 < b'` THENL
   [SUBGOAL_THEN `(gamma':real->A) tau0 IN O` ASSUME_TAC THENL
     [SUBGOAL_THEN `(gg:real->A) tau0 = gamma' tau0`
        (fun th -> ASM_MESON_TAC[th]) THEN
      USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "C'" (MP_TAC o SPECL [`tau0:real`; `O:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "D1"))) THEN
    MP_TAC(SPECL [`d1:real`; `b' - tau0`] REAL_DOWN2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gg:real->A) tau = gamma' tau` SUBST1_TAC THENL
     [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "D1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `tau0:real = b'` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(gamma':real->A) b' IN O /\ (gamma:real->A) b' IN O`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(gg:real->A) b' = gamma' b' /\ (gg:real->A) b' = gamma b'`
        (fun th -> ASM_MESON_TAC[th]) THEN
      CONJ_TAC THENL [USE_THEN "E1" MATCH_MP_TAC; USE_THEN "E2" MATCH_MP_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "C'" (MP_TAC o SPECL [`b':real`; `O:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "D1"))) THEN
    USE_THEN "C" (MP_TAC o SPECL [`b':real`; `O:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "D2"))) THEN
    MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `tau <= b'` THENL
     [SUBGOAL_THEN `(gg:real->A) tau = gamma' tau` SUBST1_TAC THENL
       [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "D1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(gg:real->A) tau = gamma tau` SUBST1_TAC THENL
       [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "D2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `b' < tau0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) tau0 IN O` ASSUME_TAC THENL
   [SUBGOAL_THEN `(gg:real->A) tau0 = gamma tau0`
      (fun th -> ASM_MESON_TAC[th]) THEN
    USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "C" (MP_TAC o SPECL [`tau0:real`; `O:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "D1"))) THEN
  MP_TAC(SPECL [`d1:real`; `tau0 - b'`] REAL_DOWN2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gg:real->A) tau = gamma tau` SUBST1_TAC THENL
   [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "D1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2A_SEG_GLUE_PC1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt (gamma:real->A) gamma' gg b b' P P'.
        p2a_pc1 V tt gamma b' b P /\
        (!c. c IN p2a_vatlas V (tt - b') /\ gamma b' IN FST c
             ==> ?d. &0 < d /\
                     continuously_differentiable 1
                       {s | b' <= drop s /\ drop s <= b' + d /\ drop s <= b /\
                            p2a_vatlas V (tt - drop s) = p2a_vatlas V (tt - b') /\
                            gamma(drop s) IN FST c}
                       (\s. SND c (gamma(drop s)))) /\
        p2a_pc1 V tt gamma' (&0) b' P' /\
        &0 < b' /\ b' < b /\
        (!tau. tau <= b' ==> gg tau = gamma' tau) /\
        (!tau. b' <= tau ==> gg tau = gamma tau)
        ==> p2a_pc1 V tt gg (&0) b (b' INSERT (P UNION P'))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_pc1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G"))
   (CONJUNCTS_THEN2 (LABEL_TAC "RB")
   (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G'"))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "E1") (LABEL_TAC "E2"))))))) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_UNION] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INSERT; IN_UNION; DE_MORGAN_THM] THEN
  ASM_CASES_TAC `s0 < b'` THENL
   [SUBGOAL_THEN `(gamma':real->A) s0 IN FST(c:(A->bool)#(A->real^N))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(gg:real->A) s0 = gamma' s0` (fun th -> ASM_MESON_TAC[th]) THEN
      USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "G'" (MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "L1") (CONJUNCTS_THEN2 (LABEL_TAC "R1")
      (LABEL_TAC "T1"))))) THEN
    MP_TAC(SPECL [`d1:real`; `(b' - s0) / &2`] REAL_DOWN2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "L1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER);
      USE_THEN "R1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER);
      STRIP_TAC THEN
      USE_THEN "T1" (MP_TAC o C MP (ASSUME `~((s0:real) IN P')`)) THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER)] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `(gg:real->A)(drop s) = gamma'(drop s)` SUBST_ALL_TAC THENL
      [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s0:real = b'` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(gamma':real->A) b' IN FST(c:(A->bool)#(A->real^N)) /\
                  (gamma:real->A) b' IN FST c` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(gg:real->A) b' = gamma' b' /\ (gg:real->A) b' = gamma b'`
        (fun th -> ASM_MESON_TAC[th]) THEN
      CONJ_TAC THENL [USE_THEN "E1" MATCH_MP_TAC; USE_THEN "E2" MATCH_MP_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "G'" (MP_TAC o SPECL [`b':real`; `c:(A->bool)#(A->real^N)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "L1") (K ALL_TAC)))) THEN
    USE_THEN "RB" (MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R2"))) THEN
    MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "L1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(gg:real->A)(drop s) = gamma'(drop s)` SUBST_ALL_TAC THENL
       [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "R2" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(gg:real->A)(drop s) = gamma(drop s)` SUBST_ALL_TAC THENL
       [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `b' < s0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) s0 IN FST(c:(A->bool)#(A->real^N))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(gg:real->A) s0 = gamma s0` (fun th -> ASM_MESON_TAC[th]) THEN
    USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "G" (MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "L1") (CONJUNCTS_THEN2 (LABEL_TAC "R1")
    (LABEL_TAC "T1"))))) THEN
  MP_TAC(SPECL [`d1:real`; `(s0 - b') / &2`] REAL_DOWN2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "L1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER);
    USE_THEN "R1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER);
    STRIP_TAC THEN
    USE_THEN "T1" (MP_TAC o C MP (ASSUME `~((s0:real) IN P)`)) THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER)] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
  (SUBGOAL_THEN `(gg:real->A)(drop s) = gamma(drop s)` SUBST_ALL_TAC THENL
    [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2A_SEG_GLUE_LINT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt (gamma:real->A) gamma' gg b b'.
        p2a_L_integrand V tt gamma b real_integrable_on real_interval[b',b] /\
        p2a_L_integrand V tt gamma' b' real_integrable_on real_interval[&0,b'] /\
        &0 < b' /\ b' < b /\
        (!tau. tau <= b' ==> gg tau = gamma' tau) /\
        (!tau. b' <= tau ==> gg tau = gamma tau)
        ==> p2a_L_integrand V tt gg b real_integrable_on real_interval[&0,b] /\
            p2a_L_length V tt gg b =
            p2a_L_length V tt gamma' b' +
            real_integral (real_interval[b',b]) (p2a_L_integrand V tt gamma b)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "E1") (LABEL_TAC "E2")))))) THEN
  SUBGOAL_THEN `&0 <= b' /\ b' <= b` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gg:real->A) b`;
    `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma':real->A) b'`;
    `&0`; `b':real`] P2A_REAL_INTEGRAL_OPEN_EQ) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b':real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN USE_THEN "E1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "I1") (LABEL_TAC "J1")) THEN
  MP_TAC(ISPECL
   [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gg:real->A) b`;
    `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma:real->A) b`;
    `b':real`; `b:real`] P2A_REAL_INTEGRAL_OPEN_EQ) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`b':real`; `b:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN USE_THEN "E2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "I2") (LABEL_TAC "J2")) THEN
  SUBGOAL_THEN
   `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                       (real->A->real^N^N)) tt (gg:real->A) b
      real_integrable_on real_interval[&0,b]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `b':real` THEN
    REMOVE_THEN "I1" (fun th -> REWRITE_TAC[th]) THEN
    REMOVE_THEN "I2" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2a_L_length] THEN
  MP_TAC(ISPECL
   [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gg:real->A) b`;
    `&0`; `b:real`; `b':real`] REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REMOVE_THEN "J1" SUBST1_TAC THEN REMOVE_THEN "J2" SUBST1_TAC THEN REFL_TAC);;


let P2A_SEG_GLUE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt x (gamma:real->A) gamma' gg b b'.
        p2a_adm V tt x b' gamma' /\ p2a_lseg V tt b' b gamma /\ gamma' b' = gamma b' /\
        (!tau. tau <= b' ==> gg tau = gamma' tau) /\
        (!tau. b' <= tau ==> gg tau = gamma tau)
        ==> p2a_adm V tt x b gg /\
            p2a_L_length V tt gg b =
            p2a_L_length V tt gamma' b' +
            real_integral (real_interval[b',b]) (p2a_L_integrand V tt gamma b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_adm; p2a_lseg] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "E1")
    (LABEL_TAC "E2"))))) THEN
  SUBGOAL_THEN
   `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                       (real->A->real^N^N)) tt (gg:real->A) b
      real_integrable_on real_interval[&0,b] /\
    p2a_L_length V tt gg b =
    p2a_L_length V tt gamma' b' +
    real_integral (real_interval[b',b]) (p2a_L_integrand V tt gamma b)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_SEG_GLUE_LINT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    TRANS_TAC EQ_TRANS `(gamma':real->A)(&0)` THEN CONJ_TAC THENL
     [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN ASM_CASES_TAC `tau <= b'` THENL
     [SUBGOAL_THEN `(gg:real->A) tau = gamma' tau` SUBST1_TAC THENL
       [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(gg:real->A) tau = gamma tau` SUBST1_TAC THENL
       [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC P2A_SEG_GLUE_CONT THEN
    MAP_EVERY EXISTS_TAC [`gamma:real->A`; `gamma':real->A`; `b':real`] THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `b' INSERT ((P':real->bool) UNION P)` THEN
    MATCH_MP_TAC P2A_SEG_GLUE_PC1 THEN
    MAP_EVERY EXISTS_TAC [`gamma:real->A`; `gamma':real->A`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN ASM_CASES_TAC `tau <= b'` THENL
     [SUBGOAL_THEN `(gg:real->A) tau = gamma' tau` SUBST1_TAC THENL
       [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(gg:real->A) tau = gamma tau` SUBST1_TAC THENL
       [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

(* Replacing a piece [b1,b2] of an admissible curve (b2 < b) by a segment   *)
(* with the same end points.                                                 *)

let P2A_REPLACE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt x (gamma:real->A) sig b b1 b2.
        p2a_adm V tt x b gamma /\ p2a_lseg V tt b1 b2 sig /\ b2 < b /\
        sig b1 = gamma b1 /\ sig b2 = gamma b2
        ==> p2a_adm V tt x b
              (\tau. if tau <= b1 then gamma tau else if tau <= b2 then sig tau
                     else gamma tau) /\
            p2a_L_length V tt
              (\tau. if tau <= b1 then gamma tau else if tau <= b2 then sig tau
                     else gamma tau) b =
            p2a_L_length V tt gamma b -
            real_integral (real_interval[b1,b2]) (p2a_L_integrand V tt gamma b) +
            real_integral (real_interval[b1,b2]) (p2a_L_integrand V tt sig b2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b1 /\ b1 < b2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_lseg]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `sig:real->A`; `gamma:real->A`;
                 `\tau. if tau <= b1 then (gamma:real->A) tau else sig tau`;
                 `b2:real`; `b1:real`] P2A_SEG_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2A_ADM_RESTRICT THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau:real = b1` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`;
                 `\tau. if tau <= b1 then (gamma:real->A) tau else sig tau`;
                 `\tau. if tau <= b1 then (gamma:real->A) tau else if tau <= b2 then sig tau
                        else gamma tau`; `b:real`; `b2:real`] P2A_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `tau:real` THEN DISCH_TAC THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(tau <= b1)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      (SUBGOAL_THEN `tau:real = b2` SUBST1_TAC THENL
        [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]])];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`; `b:real`;
                 `b1:real`] P2A_LENGTH_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                       (real->A->real^N^N)) tt (gamma:real->A) b
      real_integrable_on real_interval[b1,b]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[p2a_adm]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt (gamma:real->A) b`;
                 `b1:real`; `b:real`; `b2:real`] REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Chart pieces.  For a curve sol in the image of a                          *)
(* region chart, C^1 on [s1,s2] (s1 > 0), the curve                          *)
(*    tau |-> chart_inv (U INTER W,phi) (sol(sqrt tau))                      *)
(* is a segment on [s1^2,s2^2] whose L-length is the chart L-functional of  *)
(* sol; a minimizer is no longer on [s1^2,s2^2] than such a piece with the  *)
(* same end points (P2A_MIN_CHART_PIECE).                                    *)
(* ========================================================================= *)

(* Inverses of region charts.                                                *)

let P2A_REGION_CHART_INV = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' b'' U (phi:A->real^N) z.
     p2a_region V W a' b'' /\ a' < b'' /\ (U,phi) IN p2a_vatlas V b'' /\ z IN U INTER W
     ==> chart_inv (U INTER W,phi) (phi z) = z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `b'':real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b''`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b''`;
                 `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `z:A`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_SIMP_TAC[]);;

let P2A_CHART_PIECE_FACTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' b'' U (phi:A->real^N) (y:real^N).
     p2a_region V W a' b'' /\ a' < b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     y IN IMAGE phi (U INTER W)
     ==> chart_inv (U INTER W,phi) y IN U INTER W /\ phi(chart_inv (U INTER W,phi) y) = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `q:A`] P2A_REGION_CHART_INV) THEN
  ASM_SIMP_TAC[]);;

(* The set of chart points whose chart inverse lies in a slice-open set O   *)
(* is open.                                                                   *)

let P2A_CHART_INV_NBHD = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' b'' U (phi:A->real^N) t O y0.
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\ a' < t /\ t <= b'' /\
     open_in (p2a_vtop V t) O /\ y0 IN IMAGE phi (U INTER W) /\
     chart_inv (U INTER W,phi) y0 IN O
     ==> ?r. &0 < r /\
             !y. dist(y,y0) < r
                 ==> y IN IMAGE phi (U INTER W) /\ chart_inv (U INTER W,phi) y IN O`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `b'':real`]
                P2A_REGION_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) b'') (W INTER O)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_OPEN_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`a':real`; `t:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b''`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b''`;
                 `U:A->bool`; `phi:A->real^N`; `W INTER O:A->bool`] MFDR_RESTRICT_IMAGE_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!z:A. z IN U INTER W ==> chart_inv (U INTER W,phi:A->real^N) (phi z) = z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(y0:real^N) IN IMAGE (phi:A->real^N) (U INTER W)` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(q:A) IN O` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (phi:A->real^N) (U INTER W INTER O)` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `(phi:A->real^N) q`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN IMAGE (phi:A->real^N) (U INTER W INTER O)` MP_TAC THENL
   [UNDISCH_TAC `ball((phi:A->real^N) q,r) SUBSET IMAGE phi (U INTER W INTER O)` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:A) IN U INTER W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[] THEN ASM SET_TAC[]]);;

(* tau |-> sol(sqrt tau): derivative and continuous derivative.             *)

let P2A_SQRT_CURVE_DERIV = prove
 (`!(sol:real^1->real^N) tau.
     &0 < tau /\
     (sol has_vector_derivative vector_derivative sol (at (lift(sqrt tau))))
       (at (lift(sqrt tau))) /\
     (\v. vector_derivative sol (at v)) continuous (at (lift(sqrt tau)))
     ==> ((\t. sol(lift(sqrt(drop t)))) has_vector_derivative
          inv(&2 * sqrt tau) % vector_derivative sol (at (lift(sqrt tau)))) (at (lift tau)) /\
         (\t. inv(&2 * sqrt(drop t)) % vector_derivative sol (at (lift(sqrt(drop t)))))
           continuous (at (lift tau))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((lift o sqrt o drop) has_vector_derivative lift(inv(&2 * sqrt tau)))
                (at (lift tau))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SQRT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(lift o sqrt o drop) continuous (at (lift tau))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL; REAL_CONTINUOUS_AT_SQRT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`lift o sqrt o drop`; `sol:real^1->real^N`; `lift(inv(&2 * sqrt tau))`;
                   `vector_derivative (sol:real^1->real^N) (at (lift(sqrt tau)))`; `lift tau`]
                  VECTOR_DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[o_THM; LIFT_DROP] THEN REWRITE_TAC[o_DEF; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN `lift o (\t:real^1. inv(&2 * sqrt(drop t))) =
                  lift o (\x. inv(&2 * sqrt x)) o drop`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_INV_ATREAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN REWRITE_TAC[REAL_CONTINUOUS_AT_SQRT];
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[SQRT_POS_LT] THEN REAL_ARITH_TAC];
    SUBGOAL_THEN `(\t:real^1. vector_derivative (sol:real^1->real^N) (at (lift(sqrt(drop t))))) =
                  (\v. vector_derivative sol (at v)) o (lift o sqrt o drop)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN ASM_REWRITE_TAC[o_THM; LIFT_DROP]]);;

(* Agreement on an open interval transfers derivatives.                      *)

let P2A_VDERIV_AGREE = prove
 (`!(f:real^1->real^N) g s1 s2 s.
     (!v. s1 < drop v /\ drop v < s2 ==> f v = g v) /\ s1 < s /\ s < s2 /\
     g differentiable (at (lift s))
     ==> (f has_vector_derivative vector_derivative g (at (lift s))) (at (lift s)) /\
         vector_derivative f (at (lift s)) = vector_derivative g (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`g:real^1->real^N`; `min (s - s1) (s2 - s)`] THEN
    ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(MATCH_ACCEPT_TAC o MATCH_MP VECTOR_DERIVATIVE_AT)]);;

let P2A_VDERIV_AGREE_CONT = prove
 (`!(f:real^1->real^N) g s1 s2 s.
     (!v. s1 < drop v /\ drop v < s2 ==> f v = g v /\ g differentiable (at v)) /\
     s1 < s /\ s < s2 /\
     (\v. vector_derivative g (at v)) continuous (at (lift s))
     ==> (\v. vector_derivative f (at v)) continuous (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\v. vector_derivative (g:real^1->real^N) (at v)`;
                        `min (s - s1) (s2 - s)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN DISCH_TAC THEN
  SUBGOAL_THEN `s1 < drop(v:real^1) /\ drop v < s2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `g:real^1->real^N`; `s1:real`; `s2:real`; `drop(v:real^1)`]
                P2A_VDERIV_AGREE) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]));;

(* The L-length of a chart piece.                                            *)

let P2A_CHART_SEG_LINT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt W a' b'' U (phi:A->real^N) (sol:real^1->real^N) s1 s2 sa sb.
     p2a_svs V /\ p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s1 /\ s1 < s2 /\ sa < s1 /\ s2 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b'') /\
     (!s. s1 <= s /\ s <= s2
          ==> sol(lift s) IN IMAGE phi (U INTER W) /\
              sol differentiable (at (lift s)) /\
              (\v. vector_derivative sol (at v)) continuous (at (lift s)))
     ==> (p2a_L_integrand V tt (\tau. chart_inv (U INTER W,phi) (sol(lift(sqrt tau))))
                          (s2 pow 2)
          has_real_integral p2a_cL (p2a_rlocal V W b'' (U INTER W,phi)) tt sol s1 s2)
         (real_interval[s1 pow 2,s2 pow 2])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `sig = \tau. chart_inv (U INTER W,phi:A->real^N)
                                    ((sol:real^1->real^N)(lift(sqrt tau)))` THEN
  SUBGOAL_THEN `a' < b''` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= s2
                    ==> (sig:real->A)(s pow 2) IN U INTER W /\
                        (phi:A->real^N)(sig(s pow 2)) = (sol:real^1->real^N)(lift s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "sig" THEN
    SUBGOAL_THEN `sqrt(s pow 2) = s` SUBST1_TAC THENL
     [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2A_CHART_PIECE_FACTS THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. s1 <= drop v /\ drop v <= s2
                    ==> (phi:A->real^N)((sig:real->A)(drop v pow 2)) = (sol:real^1->real^N) v`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop(v:real^1)` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sig:real->A`)) (concl th))) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\v. vector_derivative (sol:real^1->real^N) (at v)) continuous_on
                interval[lift s1,lift s2]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC o BETA_RULE o
              MATCH_MP P2A_CONT_BOUNDED) THEN
  (* hypotheses of P2A_LINT_PIECE *)
  SUBGOAL_THEN
   `!s O. s1 < s /\ s < s2 /\
          open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) (tt - s pow 2)) O /\
          (sig:real->A)(s pow 2) IN O
          ==> ?e. &0 < e /\
                  !r. &0 <= r /\ r pow 2 <= s2 pow 2 /\ abs(r - s) < e ==> sig(r pow 2) IN O`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `O:A->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a' < tt - s pow 2 /\ tt - s pow 2 <= b''` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sb:real`)) (concl th))) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(sol:real^1->real^N)(lift s) IN IMAGE (phi:A->real^N) (U INTER W) /\
                  sol differentiable (at (lift s))` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sol:real^1->real^N`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (U INTER W,phi:A->real^N) ((sol:real^1->real^N)(lift s)) IN O`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(sig:real->A)(s pow 2) IN O` THEN EXPAND_TAC "sig" THEN
      SUBGOAL_THEN `sqrt(s pow 2) = s` SUBST1_TAC THENL
       [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                   `phi:A->real^N`; `tt - s pow 2`; `O:A->bool`;
                   `(sol:real^1->real^N)(lift s)`] P2A_CHART_INV_NBHD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R0"))) THEN
    SUBGOAL_THEN `(sol:real^1->real^N) continuous (at (lift s))` MP_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `r0:real`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
    EXISTS_TAC `min d (min (s - s1) (s2 - s))` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s1 < r /\ r < s2` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "sig" THEN
    SUBGOAL_THEN `sqrt(r pow 2) = r` SUBST1_TAC THENL
     [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "R0" (MP_TAC o SPEC `(sol:real^1->real^N)(lift r)`) THEN
    ANTS_TAC THENL
     [USE_THEN "D" MATCH_MP_TAC THEN REWRITE_TAC[DIST_LIFT] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\v. (phi:A->real^N)((sig:real->A)(drop v pow 2))) continuous_on
                interval[lift s1,lift s2]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `sol:real^1->real^N` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sig:real->A`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "drop")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 < s /\ s < s2
        ==> (\v. (phi:A->real^N)((sig:real->A)(drop v pow 2))) differentiable (at (lift s)) /\
            (\v. vector_derivative (\v. phi(sig(drop v pow 2))) (at v))
              continuous (at (lift s)) /\
            norm(vector_derivative (\v. phi(sig(drop v pow 2))) (at (lift s))) <= M /\
            vector_derivative (\v. phi(sig(drop v pow 2))) (at (lift s)) =
            vector_derivative (sol:real^1->real^N) (at (lift s))`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `!v. s1 < drop v /\ drop v < s2
                      ==> (phi:A->real^N)((sig:real->A)(drop v pow 2)) =
                          (sol:real^1->real^N) v /\ sol differentiable (at v)`
    ASSUME_TAC THENL
     [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `sig:real->A`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "drop")) (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o SPEC `drop(v:real^1)` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `sol:real^1->real^N`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous")) (concl th))) THEN
        REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(sol:real^1->real^N) differentiable (at (lift s)) /\
                  (\v. vector_derivative sol (at v)) continuous (at (lift s))`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sol:real^1->real^N`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\v. (phi:A->real^N)((sig:real->A)(drop v pow 2))`; `sol:real^1->real^N`;
                   `s1:real`; `s2:real`; `s:real`] P2A_VDERIV_AGREE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC P2A_VDERIV_AGREE_CONT THEN
      MAP_EVERY EXISTS_TAC [`sol:real^1->real^N`; `s1:real`; `s2:real`] THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `sig:real->A`; `s2 pow 2`;
                 `s1:real`; `s2:real`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `{}:real->bool`; `sa:real`; `sb:real`; `M:real`]
                P2A_LINT_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; FINITE_EMPTY; NOT_IN_EMPTY] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[p2a_cL] THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
  EXISTS_TAC `{s1:real,s2}` THEN
  SIMP_TAC[REAL_NEGLIGIBLE_FINITE; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `s1 < s /\ s < s2` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(phi:A->real^N)((sig:real->A)(drop(lift s) pow 2)) = (sol:real^1->real^N)(lift s)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sig:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "drop")) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable"))
             (concl th)))) THEN
    REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th) &&
    can (find_term ((=) `M:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* Chart pieces are segments (P2A_CHART_CURVE_SEG), and minimizers are no    *)
(* longer than chart pieces (P2A_MIN_CHART_PIECE).                           *)
(* ========================================================================= *)

let P2A_CHART_CURVE_SEG = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt W a' b'' U (phi:A->real^N) (sol:real^1->real^N) s1 s2 sa sb.
     p2a_svs V /\ p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s1 /\ s1 < s2 /\ sa < s1 /\ s2 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'') /\
     (!s. s1 <= s /\ s <= s2
          ==> sol(lift s) IN IMAGE phi (U INTER W) /\
              sol differentiable (at (lift s)) /\
              (\v. vector_derivative sol (at v)) continuous (at (lift s)))
     ==> p2a_lseg V tt (s1 pow 2) (s2 pow 2)
           (\tau. chart_inv (U INTER W,phi) (sol(lift(sqrt tau)))) /\
         (p2a_L_integrand V tt (\tau. chart_inv (U INTER W,phi) (sol(lift(sqrt tau))))
                          (s2 pow 2)
          has_real_integral p2a_cL (p2a_rlocal V W b'' (U INTER W,phi)) tt sol s1 s2)
         (real_interval[s1 pow 2,s2 pow 2])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b''`
  ASSUME_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2A_CHART_SEG_LINT THEN
    MAP_EVERY EXISTS_TAC [`a':real`; `sa:real`; `sb:real`] THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `a' < b''` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `sig = \tau. chart_inv (U INTER W,phi:A->real^N)
                                    ((sol:real^1->real^N)(lift(sqrt tau)))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `!t. chart_inv (U INTER W,phi:A->real^N) ((sol:real^1->real^N)(lift(sqrt t))) =
                    (sig:real->A) t` ASSUME_TAC THENL
   [EXPAND_TAC "sig" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s1 pow 2 /\ s1 pow 2 < s2 pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* facts on [s1^2,s2^2] *)
  SUBGOAL_THEN
   `!tau. s1 pow 2 <= tau /\ tau <= s2 pow 2
          ==> &0 < tau /\ s1 <= sqrt tau /\ sqrt tau <= s2 /\
              a' < tt - tau /\ tt - tau < b'' /\
              (sol:real^1->real^N)(lift(sqrt tau)) IN IMAGE (phi:A->real^N) (U INTER W) /\
              (sig:real->A) tau IN U INTER W /\
              (sol has_vector_derivative vector_derivative sol (at (lift(sqrt tau))))
                (at (lift(sqrt tau))) /\
              (\v. vector_derivative sol (at v)) continuous (at (lift(sqrt tau)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `s1 <= sqrt tau /\ sqrt tau <= s2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt tau pow 2 = tau` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `sqrt tau` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "real_le"))
                (rand(concl(SPEC_ALL th)))))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `sqrt tau` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sol:real^1->real^N`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
    EXPAND_TAC "sig" THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                   `phi:A->real^N`; `(sol:real^1->real^N)(lift(sqrt tau))`]
                  P2A_CHART_PIECE_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* C^1 of the chart curves in slice charts *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`;
                 `\t:real^1. (sol:real^1->real^N)(lift(sqrt(drop t)))`;
                 `\t:real^1. inv(&2 * sqrt(drop t)) %
                             vector_derivative (sol:real^1->real^N) (at (lift(sqrt(drop t))))`;
                 `s1 pow 2`; `s2 pow 2`] P2A_CHART_CURVE_PC1) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sig:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2A_SQRT_CURVE_DERIV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "CD") THEN
  REWRITE_TAC[p2a_lseg] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* topspace *)
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sig:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `tt - tau`]
                  P2A_REGION_SLICE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      concl th = `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                       (real->A->real^N^N)) (tt - tau)) W`)) THEN
    ASM SET_TAC[];
    (* continuity *)
    MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `tau0:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sig:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                   `phi:A->real^N`; `tt - tau0`; `O:A->bool`;
                   `(sol:real^1->real^N)(lift(sqrt tau0))`] P2A_CHART_INV_NBHD) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R0"))) THEN
    SUBGOAL_THEN `(sol:real^1->real^N) continuous (at (lift(sqrt tau0)))` MP_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `r0:real`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
    MP_TAC(SPEC `tau0:real` REAL_CONTINUOUS_AT_SQRT) THEN
    REWRITE_TAC[real_continuous_atreal] THEN DISCH_THEN(MP_TAC o SPEC `d1:real`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D2"))) THEN
    EXISTS_TAC `d2:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
      is_eq(snd(dest_forall(concl th))))) THEN
    REMOVE_THEN "R0" (MP_TAC o SPEC `(sol:real^1->real^N)(lift(sqrt tau))`) THEN
    ANTS_TAC THENL
     [USE_THEN "D1" MATCH_MP_TAC THEN REWRITE_TAC[DIST_LIFT] THEN
      USE_THEN "D2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    (* pc1 *)
    EXISTS_TAC `{}:real->bool` THEN REWRITE_TAC[p2a_pc1; FINITE_EMPTY; NOT_IN_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`t0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN REPEAT CONJ_TAC THEN
    USE_THEN "CD" MATCH_MP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    (* first point *)
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN STRIP_TAC THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    USE_THEN "CD" MATCH_MP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    (* smooth points *)
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN REWRITE_TAC[p2a_smooth] THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b'':real`] THEN
    FIRST_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sig:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    (* integrability *)
    REWRITE_TAC[real_integrable_on] THEN ASM_MESON_TAC[]]);;

(* A minimizer is no longer on [s1^2,s2^2] than a chart piece with the same *)
(* end points.                                                               *)

let P2A_MIN_CHART_PIECE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' U (phi:A->real^N) (sol:real^1->real^N) s1 s2 sa sb.
     p2a_svs V /\ p2a_min V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s1 /\ s1 < s2 /\ s2 pow 2 < b /\ sa < s1 /\ s2 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'') /\
     (!s. s1 <= s /\ s <= s2
          ==> sol(lift s) IN IMAGE phi (U INTER W) /\
              sol differentiable (at (lift s)) /\
              (\v. vector_derivative sol (at v)) continuous (at (lift s))) /\
     gamma(s1 pow 2) IN U INTER W /\ gamma(s2 pow 2) IN U INTER W /\
     sol(lift s1) = phi(gamma(s1 pow 2)) /\ sol(lift s2) = phi(gamma(s2 pow 2))
     ==> real_integral (real_interval[s1 pow 2,s2 pow 2]) (p2a_L_integrand V tt gamma b)
         <= p2a_cL (p2a_rlocal V W b'' (U INTER W,phi)) tt sol s1 s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`; `sol:real^1->real^N`; `s1:real`; `s2:real`;
                 `sa:real`; `sb:real`] P2A_CHART_CURVE_SEG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a' < b''` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sb:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `sig = \tau. chart_inv (U INTER W,phi:A->real^N)
                                    ((sol:real^1->real^N)(lift(sqrt tau)))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `s1 pow 2 < s2 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(sig:real->A)(s1 pow 2) = gamma(s1 pow 2) /\ sig(s2 pow 2) = gamma(s2 pow 2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sig" THEN
    SUBGOAL_THEN `sqrt(s1 pow 2) = s1 /\ sqrt(s2 pow 2) = s2` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[p2a_min] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_min")) (concl th))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`; `sig:real->A`;
                 `b:real`; `s1 pow 2`; `s2 pow 2`] P2A_REPLACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\tau. if tau <= s1 pow 2 then (gamma:real->A) tau
                                   else if tau <= s2 pow 2 then (sig:real->A) tau
                                   else gamma tau` o CONJUNCT2 o REWRITE_RULE[p2a_min] o
              check (fun th -> can (find_term (fun t -> is_const t &&
                fst(dest_const t) = "p2a_min")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(b <= s1 pow 2) /\ ~(b <= s2 pow 2)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "has_real_integral")) (concl th))) THEN
  REAL_ARITH_TAC);;


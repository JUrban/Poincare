(* ========================================================================= *)
(* pc_moi_s34_rchart: local charts and local gluing for the Sec 34 residual   *)
(* balls (Moise GTM 47, pp.244-245), shared by pc_moi_s34_residb and          *)
(* pc_moi_s34_resida.  Half-space charts of PL cells and balls at every       *)
(* point, ambient charts of PL spheres, invariance of domain through charts,  *)
(* and the gluing lemma: two cells with agreeing boundaries near a boundary   *)
(* point and disjoint cell interiors cover a neighbourhood of the point.      *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_cglue.ml";;
needs "src/pc_moi_s34_tinf.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Chart predicates, invariance of domain through an ambient                 *)
(* chart, open cell interiors and the local gluing lemma (any dimension).    *)
(* moi_s4yc_mchart m x u c c': an ambient chart of m at x onto an open set  *)
(* of real^N; moi_s4yc_hchart x1 b1 x w h h' oo: a half-space chart of x1   *)
(* at x whose boundary part b1 corresponds to the last coordinate zero.     *)
(* ------------------------------------------------------------------------- *)

let moi_s4yc_mchart = new_definition
 `moi_s4yc_mchart (m:real^M->bool) (x:real^M) (u:real^M->bool) (c:real^M->real^N)
                  (c':real^N->real^M) <=>
    open_in (subtopology euclidean m) u /\ x IN u /\ open (IMAGE c u) /\
    homeomorphism (u,IMAGE c u) (c,c')`;;

let moi_s4yc_hchart = new_definition
 `moi_s4yc_hchart (x1:real^M->bool) (b1:real^M->bool) (x:real^M) (w:real^M->bool)
                  (h:real^M->real^N) (h':real^N->real^M) (oo:real^N->bool) <=>
    open_in (subtopology euclidean x1) w /\ x IN w /\ homeomorphism (w,IMAGE h w) (h,h') /\
    open oo /\ IMAGE h w = oo INTER {y | &0 <= y$(dimindex(:N))} /\
    (!y. y IN w ==> (y IN b1 <=> (h y)$(dimindex(:N)) = &0))`;;

(* Invariance of domain through an ambient chart. *)

let MOI_S4YC_IOD = prove
 (`!(m:real^M->bool) x u (c:real^M->real^N) c' oo (f:real^N->real^M).
     moi_s4yc_mchart m x u c c' /\
     open oo /\ f continuous_on oo /\
     (!y z. y IN oo /\ z IN oo /\ f y = f z ==> y = z) /\
     IMAGE f oo SUBSET u /\ x IN IMAGE f oo
     ==> ?v. open v /\ x IN v /\ m INTER v SUBSET IMAGE f oo`,
  REWRITE_TAC[moi_s4yc_mchart] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `open (IMAGE ((c:real^M->real^N) o (f:real^N->real^M)) oo)` ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^M->bool` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`y:real^N`; `z:real^N`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(f:real^N->real^M) y = f z` (fun th -> ASM_MESON_TAC[th]) THEN
      ASM_MESON_TAC[SUBSET; FUN_IN_IMAGE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean u) (IMAGE (f:real^N->real^M) oo)` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (f:real^N->real^M) oo =
                  IMAGE (c':real^N->real^M) (IMAGE ((c:real^M->real^N) o f) oo)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      MATCH_MP_TAC(SET_RULE `(!x:real^N. x IN s ==> (f:real^N->real^M) x = g x)
                             ==> IMAGE f s = IMAGE g s`) THEN
      ASM_MESON_TAC[SUBSET; FUN_IN_IMAGE];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`c:real^M->real^N`; `IMAGE (c:real^M->real^N) u`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[HOMEOMORPHISM_SYM]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean m) (IMAGE (f:real^N->real^M) oo)` MP_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real^M->bool` THEN ASM SET_TAC[]);;

(* A point of a half chart off the boundary part has a neighbourhood in the  *)
(* ambient set inside x1 DIFF b1.                                            *)

let MOI_S4YC_HALF_OPEN = prove
 (`!(m:real^M->bool) x1 b1 x u (c:real^M->real^N) c' w (h:real^M->real^N) h' oo.
     moi_s4yc_mchart m x u c c' /\ x1 SUBSET m /\ moi_s4yc_hchart x1 b1 x w h h' oo /\
     ~(x IN b1)
     ==> ?v. open v /\ x IN v /\ m INTER v SUBSET x1 DIFF b1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4yc_hchart] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s4yc_mchart]) THEN STRIP_TAC THEN
  UNDISCH_TAC `open_in (subtopology euclidean m) (u:real^M->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN DISCH_THEN(X_CHOOSE_THEN `v0:real^M->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `open_in (subtopology euclidean x1) (w:real^M->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN DISCH_THEN(X_CHOOSE_THEN `v1:real^M->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `n = dimindex(:N)` THEN
  SUBGOAL_THEN `&0 < ((h:real^M->real^N) x)$n` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^M->real^N) x IN oo INTER {y | &0 <= y$n}` MP_TAC THENL
     [ASM_MESON_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LT_LE];
    ALL_TAC] THEN
  ABBREV_TAC `o3 = {y | y IN oo INTER {y:real^N | &0 < y$n} /\ (h':real^N->real^M) y IN v0}` THEN
  SUBGOAL_THEN `oo INTER {y:real^N | &0 < y$n} SUBSET IMAGE (h:real^M->real^N) w` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `open (o3:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "o3" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (h:real^M->real^N) w` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:real^M->bool`; `x:real^M`; `u:real^M->bool`; `c:real^M->real^N`;
                 `c':real^N->real^M`; `o3:real^N->bool`; `h':real^N->real^M`] MOI_S4YC_IOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (h:real^M->real^N) w` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "o3" THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`y:real^N`; `z:real^N`] THEN EXPAND_TAC "o3" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_MESON_TAC[SUBSET];
      EXPAND_TAC "o3" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(h':real^N->real^M) y IN w` MP_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h:real^M->real^N) x` THEN
      EXPAND_TAC "o3" THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM_SIMP_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FUN_IN_IMAGE; IN_INTER]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^M->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (h':real^N->real^M) o3 SUBSET x1 DIFF b1` MP_TAC THENL
   [EXPAND_TAC "o3" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_DIFF; IN_INTER] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(h':real^N->real^M) y IN w /\ (h:real^M->real^N) (h' y) = y`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `((h:real^M->real^N) ((h':real^N->real^M) y))$n = &0` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The local gluing lemma.  Two subsets x1, x2 of m with half                *)
(* charts at a common boundary point x, whose boundary parts agree near x    *)
(* and whose parts off the boundary are disjoint, cover a neighbourhood of x *)
(* in m.  The glued map is h1' on the upper half and h2' after the boundary  *)
(* transition and the reflection on the lower half; it is continuous and     *)
(* injective, so invariance of domain applies (MOI_S4YC_IOD).                *)
(* ------------------------------------------------------------------------- *)

let MOI_S4YC_FLAT_NORM = prove
 (`!(z:real^N) n. 1 <= n /\ n <= dimindex(:N)
     ==> (z - (z$n) % basis n)$n = &0 /\ norm(z - (z$n) % basis n) <= norm z /\
         z = (z - (z$n) % basis n) + (z$n) % basis n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    REWRITE_TAC[NORM_LE; DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
    ASM_SIMP_TAC[DOT_BASIS; BASIS_COMPONENT] THEN
    MP_TAC(SPEC `(z:real^N)$n` REAL_LE_SQUARE) THEN REAL_ARITH_TAC;
    VECTOR_ARITH_TAC]);;

let MOI_S4YC_GLUE = prove
 (`!(m:real^M->bool) x1 b1 x2 b2 x u (c:real^M->real^N) c' w1 (h1:real^M->real^N) h1' o1
    w2 (h2:real^M->real^N) h2' o2.
     moi_s4yc_mchart m x u c c' /\ x1 SUBSET m /\ x2 SUBSET m /\
     b1 SUBSET x1 /\ b2 SUBSET x2 /\
     moi_s4yc_hchart x1 b1 x w1 h1 h1' o1 /\ moi_s4yc_hchart x2 b2 x w2 h2 h2' o2 /\
     x IN b1 /\ (?v. open v /\ x IN v /\ v INTER b1 = v INTER b2) /\
     DISJOINT (x1 DIFF b1) (x2 DIFF b2)
     ==> ?v. open v /\ x IN v /\ m INTER v SUBSET x1 UNION x2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4yc_hchart] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `homeomorphism (w1,IMAGE (h1:real^M->real^N) w1) (h1,h1')`) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `homeomorphism (w2,IMAGE (h2:real^M->real^N) w2) (h2,h2')`) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `moi_s4yc_mchart (m:real^M->bool) x u (c:real^M->real^N) c'`) THEN
  REWRITE_TAC[moi_s4yc_mchart; OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v3:real^M->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `open_in (subtopology euclidean x1) (w1:real^M->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN DISCH_THEN(X_CHOOSE_THEN `v1:real^M->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  UNDISCH_TAC `open_in (subtopology euclidean x2) (w2:real^M->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN DISCH_THEN(X_CHOOSE_THEN `v2:real^M->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  ABBREV_TAC `n = dimindex(:N)` THEN
  SUBGOAL_THEN `1 <= n /\ n <= dimindex(:N)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[DIMINDEX_GE_1; LE_REFL]; ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (h1:real^M->real^N) w1 = o1 INTER {y | &0 <= y$n}` THEN
  DISCH_THEN(LABEL_TAC "im1" o GSYM) THEN
  UNDISCH_TAC `IMAGE (h2:real^M->real^N) w2 = o2 INTER {y | &0 <= y$n}` THEN
  DISCH_THEN(LABEL_TAC "im2" o GSYM) THEN
  (* the points and their coordinates *)
  SUBGOAL_THEN `(x:real^M) IN b2 /\ x IN v1 /\ x IN v2 /\ x IN v3` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `y0 = (h1:real^M->real^N) x` THEN
  SUBGOAL_THEN `(y0:real^N)$n = &0 /\ ((h2:real^M->real^N) x)$n = &0 /\
                y0 IN IMAGE (h1:real^M->real^N) w1 /\ h2 x IN IMAGE h2 w2 /\
                (h1':real^N->real^M) y0 = x /\ (h2':real^N->real^M) (h2 x) = x`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN REPEAT CONJ_TAC THEN TRY(ASM_MESON_TAC[FUN_IN_IMAGE]);
    ALL_TAC] THEN
  (* continuity data *)
  ABBREV_TAC `g = v INTER v2 INTER (v3:real^M->bool)` THEN
  SUBGOAL_THEN `open (g:real^M->bool) /\ (x:real^M) IN g` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN ASM_SIMP_TAC[OPEN_INTER; IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?d1. &0 < d1 /\ ball(y0:real^N,d1) SUBSET o1 /\
         !y. y IN IMAGE (h1:real^M->real^N) w1 /\ dist(y,y0) < d1 ==> (h1':real^N->real^M) y IN g`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^M->bool`] OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ASSUME `(h1':real^N->real^M) continuous_on IMAGE (h1:real^M->real^N) w1`) THEN
    REWRITE_TAC[continuous_on] THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `(y0:real^N) IN IMAGE (h1:real^M->real^N) w1`) o
               SPEC `y0:real^N`) THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `&0 < r`) o SPEC `r:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cd"))) THEN
    MP_TAC(ISPECL [`o1:real^N->bool`] OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `y0:real^N`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `(y0:real^N) IN IMAGE (h1:real^M->real^N) w1` THEN
      USE_THEN "im1" (fun th -> REWRITE_TAC[GSYM th]) THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d r1` THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y0:real^N,r1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL];
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
      USE_THEN "cd" (MP_TAC o C MP (CONJ (ASSUME `(y:real^N) IN IMAGE (h1:real^M->real^N) w1`)
                                      (ASSUME `dist(y:real^N,y0) < d`)) o SPEC `y:real^N`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `ball(x:real^M,r) SUBSET g` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d2. &0 < d2 /\ ball((h2:real^M->real^N) x,d2) SUBSET o2 /\
         !z. z IN IMAGE h2 w2 /\ dist(z,h2 x) < d2 ==> (h2':real^N->real^M) z IN v3`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`v3:real^M->bool`] OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ASSUME `(h2':real^N->real^M) continuous_on IMAGE (h2:real^M->real^N) w2`) THEN
    REWRITE_TAC[continuous_on] THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `(h2:real^M->real^N) x IN IMAGE h2 w2`) o
               SPEC `(h2:real^M->real^N) x`) THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `&0 < r`) o SPEC `r:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cd"))) THEN
    MP_TAC(ISPECL [`o2:real^N->bool`] OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `(h2:real^M->real^N) x`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `(h2:real^M->real^N) x IN IMAGE h2 w2` THEN
      USE_THEN "im2" (fun th -> REWRITE_TAC[GSYM th]) THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d r1` THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball((h2:real^M->real^N) x,r1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL];
      X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
      USE_THEN "cd" (MP_TAC o C MP (CONJ (ASSUME `(z:real^N) IN IMAGE (h2:real^M->real^N) w2`)
                                      (ASSUME `dist(z:real^N,(h2:real^M->real^N) x) < d`)) o SPEC `z:real^N`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `ball(x:real^M,r) SUBSET v3` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d4. &0 < d4 /\
         !p. p IN w2 /\ dist(p,x) < d4
             ==> dist((h2:real^M->real^N) p,h2 x) < d2 / &2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(h2:real^M->real^N) continuous_on w2` THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `d2 / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:real^M` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d3. &0 < d3 /\
         !q. q IN IMAGE (h1:real^M->real^N) w1 /\ dist(q,y0) < d3
             ==> dist((h1':real^N->real^M) q,x) < d4`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(h1':real^N->real^M) continuous_on IMAGE (h1:real^M->real^N) w1` THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `y0:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `d4:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(h1':real^N->real^M) y0 = x` (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THENL
     [ASM_REWRITE_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `eps = min d1 (min d3 (d2 / &2))` THEN
  SUBGOAL_THEN `&0 < eps /\ eps <= d1 /\ eps <= d3 /\ eps <= d2 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the upper half *)
  SUBGOAL_THEN
   `!y:real^N. y IN ball(y0,eps) /\ &0 <= y$n
               ==> y IN IMAGE (h1:real^M->real^N) w1 /\ (h1':real^N->real^M) y IN w1 /\
                   h1' y IN g /\ h1 (h1' y) = y`
  (LABEL_TAC "up") THENL
   [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN IMAGE (h1:real^M->real^N) w1` ASSUME_TAC THENL
     [USE_THEN "im1" (fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ball(y0:real^N,d1) SUBSET o1` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `d1:real`)) (concl th))) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the lower half *)
  SUBGOAL_THEN
   `!y:real^N. y IN ball(y0,eps) /\ y$n <= &0
     ==> (y - (y$n) % basis n) IN IMAGE (h1:real^M->real^N) w1 /\
         (h1':real^N->real^M) (y - (y$n) % basis n) IN w2 /\
         h1' (y - (y$n) % basis n) IN b1 /\ h1' (y - (y$n) % basis n) IN b2 /\
         h1 (h1' (y - (y$n) % basis n)) = y - (y$n) % basis n /\
         ((h2:real^M->real^N) (h1' (y - (y$n) % basis n)) - (y$n) % basis n) IN IMAGE h2 w2 /\
         (h2 (h1' (y - (y$n) % basis n)) - (y$n) % basis n)$n = --(y$n) /\
         (h2':real^N->real^M) (h2 (h1' (y - (y$n) % basis n)) - (y$n) % basis n) IN w2 /\
         h2' (h2 (h1' (y - (y$n) % basis n)) - (y$n) % basis n) IN v3 /\
         h2 (h2' (h2 (h1' (y - (y$n) % basis n)) - (y$n) % basis n)) =
         h2 (h1' (y - (y$n) % basis n)) - (y$n) % basis n`
  (LABEL_TAC "low") THENL
   [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `((y:real^N) - (y$n) % basis n)$n = &0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm((y:real^N) - (y$n) % basis n - y0) <= norm(y - y0)` ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^N) - (y$n) % basis n - y0 = (y - y0) - ((y - y0)$n) % basis n`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT; REAL_SUB_RZERO] THEN VECTOR_ARITH_TAC;
        MP_TAC(ISPECL [`y - y0:real^N`; `n:num`] MOI_S4YC_FLAT_NORM) THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    ABBREV_TAC `q = (y:real^N) - (y$n) % basis n` THEN
    SUBGOAL_THEN `dist(q:real^N,y0) < eps` ASSUME_TAC THENL
     [REWRITE_TAC[dist] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `norm(y - y0:real^N)` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist];
      ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^N) IN IMAGE (h1:real^M->real^N) w1` ASSUME_TAC THENL
     [USE_THEN "im1" (fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      UNDISCH_TAC `ball(y0:real^N,d1) SUBSET o1` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(h1':real^N->real^M) q IN w1 /\ h1 (h1' q) = q /\ h1' q IN g`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `d1:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(h1':real^N->real^M) q IN b1` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h1':real^N->real^M) q IN b2 /\ h1' q IN w2` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(h1':real^N->real^M) q IN g` THEN EXPAND_TAC "g" THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(h1':real^N->real^M) q IN b2` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `((h2:real^M->real^N) ((h1':real^N->real^M) q))$n = &0` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `dist((h2:real^M->real^N) ((h1':real^N->real^M) q),h2 x) < d2 / &2`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `d4:real`)) (concl th) &&
        not (can (find_term ((=) `d3:real`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `d3:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `z = (h2:real^M->real^N) ((h1':real^N->real^M) q) - ((y:real^N)$n) % basis n` THEN
    SUBGOAL_THEN `(z:real^N)$n = --((y:real^N)$n)` ASSUME_TAC THENL
     [EXPAND_TAC "z" THEN
      ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `dist(z:real^N,(h2:real^M->real^N) x) < d2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `dist((h2:real^M->real^N) ((h1':real^N->real^M) q),h2 x) + abs((y:real^N)$n)` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "z" THEN REWRITE_TAC[dist] THEN
        SUBGOAL_THEN `abs((y:real^N)$n) = norm((y$n) % basis n:real^N)` SUBST1_TAC THENL
         [ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; REAL_MUL_RID]; ALL_TAC] THEN
        REWRITE_TAC[NORM_ARITH `norm((p:real^N) - r - q) <= norm(p - q) + norm r`];
        MATCH_MP_TAC(REAL_ARITH `a < d / &2 /\ b < d / &2 ==> a + b < d`) THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(y - y0:real^N)` THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`y - y0:real^N`; `n:num`] COMPONENT_LE_NORM) THEN
          ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT; REAL_SUB_RZERO];
          MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[] THEN
          ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN IMAGE (h2:real^M->real^N) w2` ASSUME_TAC THENL
     [USE_THEN "im2" (fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `ball((h2:real^M->real^N) x,d2) SUBSET o2` THEN
        REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h2':real^N->real^M) z IN w2 /\ (h2:real^M->real^N) (h2' z) = z`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h2':real^N->real^M) z IN v3` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `d2:real`)) (concl th) &&
        can (find_term ((=) `v3:real^M->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the glued map *)
  ABBREV_TAC `psi = \y:real^N. if &0 <= y$n then (h1':real^N->real^M) y
                               else h2'((h2:real^M->real^N) (h1' (y - (y$n) % basis n)) - (y$n) % basis n)` THEN
  SUBGOAL_THEN `!y:real^N. y IN ball(y0,eps)
                           ==> (psi:real^N->real^M) y IN (x1 UNION x2) INTER v3`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXPAND_TAC "psi" THEN
    COND_CASES_TAC THENL
     [USE_THEN "up" (MP_TAC o C MP (CONJ (ASSUME `(y:real^N) IN ball(y0,eps)`)
        (ASSUME `&0 <= (y:real^N)$n`)) o SPEC `y:real^N`) THEN
      EXPAND_TAC "g" THEN ASM SET_TAC[];
      SUBGOAL_THEN `(y:real^N)$n <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "low" (MP_TAC o C MP (CONJ (ASSUME `(y:real^N) IN ball(y0,eps)`)
        (ASSUME `(y:real^N)$n <= &0`)) o SPEC `y:real^N`) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  (* continuity *)
  SUBGOAL_THEN `(psi:real^N->real^M) continuous_on ball(y0,eps)` ASSUME_TAC THENL
   [SUBGOAL_THEN `ball(y0:real^N,eps) =
                  (ball(y0,eps) INTER {y | y$n >= &0}) UNION (ball(y0,eps) INTER {y | y$n <= &0})`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN
      ASM_CASES_TAC `(z:real^N) IN ball(y0,eps)` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "psi" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `{y:real^N | y$n >= &0}` THEN
      REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE] THEN SET_TAC[];
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `{y:real^N | y$n <= &0}` THEN
      REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE] THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (h1:real^M->real^N) w1` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; real_ge] THEN
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
      USE_THEN "up" (MP_TAC o SPEC `y:real^N`) THEN ASM_SIMP_TAC[];
      ALL_TAC;
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_ge] THEN X_GEN_TAC `y:real^N` THEN
      DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^N)$n = &0 /\ (y:real^N)$n <= &0` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "low" (MP_TAC o C MP (CONJ (ASSUME `(y:real^N) IN ball(y0,eps)`)
        (ASSUME `(y:real^N)$n <= &0`)) o SPEC `y:real^N`) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN STRIP_TAC THEN ASM_SIMP_TAC[]] THEN
    SUBGOAL_THEN
     `(\y. (h2':real^N->real^M) ((h2:real^M->real^N) ((h1':real^N->real^M) (y - (y$n) % basis n)) -
                                 (y$n) % basis n)) =
      h2' o (\y. h2 (h1' (y - (y$n) % basis n)) - (y$n) % basis n)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `(\y:real^N. (h2:real^M->real^N) ((h1':real^N->real^M) (y - (y$n) % basis n))) =
          h2 o h1' o (\y. y - (y$n) % basis n)`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
           [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
            MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF] THEN
            ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT];
            MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (h1:real^M->real^N) w1` THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
            X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
            USE_THEN "low" (MP_TAC o SPEC `y:real^N`) THEN ASM_SIMP_TAC[]];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w2:real^M->bool` THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM; o_THM] THEN
          X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
          USE_THEN "low" (MP_TAC o SPEC `y:real^N`) THEN ASM_SIMP_TAC[]];
        MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF] THEN
        ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (h2:real^M->real^N) w2` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
      USE_THEN "low" (MP_TAC o SPEC `y:real^N`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* injectivity *)
  SUBGOAL_THEN `!y y':real^N. y IN ball(y0,eps) /\ y' IN ball(y0,eps) /\
                              &0 <= y$n /\ y'$n < &0 ==> ~((psi:real^N->real^M) y = psi y')`
  (LABEL_TAC "mix") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "psi" THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_ARITH `a < &0 ==> ~(&0 <= a)`] THEN
    USE_THEN "up" (MP_TAC o C MP (CONJ (ASSUME `(y:real^N) IN ball(y0,eps)`)
      (ASSUME `&0 <= (y:real^N)$n`)) o SPEC `y:real^N`) THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y':real^N)$n <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "low" (MP_TAC o C MP (CONJ (ASSUME `(y':real^N) IN ball(y0,eps)`)
      (ASSUME `(y':real^N)$n <= &0`)) o SPEC `y':real^N`) THEN STRIP_TAC THEN
    ABBREV_TAC `z' = (h2:real^M->real^N) ((h1':real^N->real^M) (y' - (y'$n) % basis n)) - (y'$n) % basis n` THEN
    SUBGOAL_THEN `~((h2':real^N->real^M) z' IN b2)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `((h2:real^M->real^N) ((h2':real^N->real^M) z'))$n = &0` MP_TAC THENL
       [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y':real^N)$n < &0` THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_TAC THEN ASM_CASES_TAC `(y:real^N)$n = &0` THENL
     [SUBGOAL_THEN `(h1':real^N->real^M) y IN b1` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(h1':real^N->real^M) y IN b2` MP_TAC THENL
       [UNDISCH_TAC `(h1':real^N->real^M) y IN g` THEN EXPAND_TAC "g" THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `~((h1':real^N->real^M) y IN b1)` ASSUME_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `((h1:real^M->real^N) ((h1':real^N->real^M) y))$n = &0` MP_TAC THENL
         [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `DISJOINT (x1 DIFF b1) (x2 DIFF (b2:real^M->bool))` THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_DIFF; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `(h1':real^N->real^M) y`) THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y y':real^N. y IN ball(y0,eps) /\ y' IN ball(y0,eps) /\
                              (psi:real^N->real^M) y = psi y' ==> y = y'`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_CASES_TAC `&0 <= (y:real^N)$n` THEN ASM_CASES_TAC `&0 <= (y':real^N)$n` THENL
     [UNDISCH_TAC `(psi:real^N->real^M) y = psi y'` THEN EXPAND_TAC "psi" THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      USE_THEN "up" (MP_TAC o C MP (CONJ (ASSUME `(y:real^N) IN ball(y0,eps)`)
        (ASSUME `&0 <= (y:real^N)$n`)) o SPEC `y:real^N`) THEN
      USE_THEN "up" (MP_TAC o C MP (CONJ (ASSUME `(y':real^N) IN ball(y0,eps)`)
        (ASSUME `&0 <= (y':real^N)$n`)) o SPEC `y':real^N`) THEN
      ASM_MESON_TAC[];
      USE_THEN "mix" (MP_TAC o SPECL [`y:real^N`; `y':real^N`]) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      USE_THEN "mix" (MP_TAC o SPECL [`y':real^N`; `y:real^N`]) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N)$n <= &0 /\ (y':real^N)$n <= &0` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "low" (MP_TAC o C MP (CONJ (ASSUME `(y:real^N) IN ball(y0,eps)`)
      (ASSUME `(y:real^N)$n <= &0`)) o SPEC `y:real^N`) THEN STRIP_TAC THEN
    USE_THEN "low" (MP_TAC o C MP (CONJ (ASSUME `(y':real^N) IN ball(y0,eps)`)
      (ASSUME `(y':real^N)$n <= &0`)) o SPEC `y':real^N`) THEN STRIP_TAC THEN
    UNDISCH_TAC `(psi:real^N->real^M) y = psi y'` THEN EXPAND_TAC "psi" THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(h2:real^M->real^N) ((h1':real^N->real^M) (y - (y$n) % basis n)) - (y$n) % basis n =
      h2 (h1' (y' - (y'$n) % basis n)) - (y'$n) % basis n`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N)$n = (y':real^N)$n` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `--a = --b ==> a = b`) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(y:real^N)$n = (y':real^N)$n`)) THEN
    SUBGOAL_THEN `(h2:real^M->real^N) ((h1':real^N->real^M) (y - (y'$n) % basis n)) =
                  h2 (h1' (y' - (y'$n) % basis n))` ASSUME_TAC THENL
     [MATCH_MP_TAC(VECTOR_ARITH `!a c b:real^N. a - c = b - c ==> a = b`) THEN
      EXISTS_TAC `((y':real^N)$n) % basis n:real^N` THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) - (y'$n) % basis n = y' - (y'$n) % basis n` MP_TAC THENL
     [ASM_MESON_TAC[]; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  (* invariance of domain *)
  MP_TAC(ISPECL [`m:real^M->bool`; `x:real^M`; `u:real^M->bool`; `c:real^M->real^N`;
                 `c':real^N->real^M`; `ball(y0:real^N,eps)`; `psi:real^N->real^M`]
                MOI_S4YC_IOD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `v3:real^M->bool`)) (concl th) &&
        can (find_term ((=) `psi:real^N->real^M`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y0:real^N` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN EXPAND_TAC "psi" THEN
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `vv:real^M->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (psi:real^N->real^M) (ball(y0,eps))` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Transport of charts along homeomorphisms; half-space charts               *)
(* of 3-simplices (MOI_FMB_CHART on the face complex), of PL 3-cells and of  *)
(* PL 3-balls in real^3 at every point.                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_S4YC_HCHART_TRANSPORT = prove
 (`!(k:real^M->bool) (c:real^P->bool) (f:real^M->real^P) g bk z w (h:real^M->real^N) h' oo.
     homeomorphism (k,c) (f,g) /\ bk SUBSET k /\ moi_s4yc_hchart k bk z w h h' oo
     ==> moi_s4yc_hchart c (IMAGE f bk) (f z) (IMAGE f w) (h o g) (f o h') oo`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4yc_hchart] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^M->bool) SUBSET k` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
    check (fun th -> can (find_term ((=) `k:real^M->bool`)) (concl th) &&
                     can (find_term ((=) `c:real^P->bool`)) (concl th))) THEN
  SUBGOAL_THEN `IMAGE ((h:real^M->real^N) o (g:real^P->real^M)) (IMAGE f w) = IMAGE h w`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^M. x IN s ==> (f:real^M->real^N) x = g x)
                             ==> IMAGE f s = IMAGE g s`) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g:real^P->real^M`; `k:real^M->bool`] THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    SUBST1_TAC(ASSUME `IMAGE ((h:real^M->real^N) o (g:real^P->real^M)) (IMAGE f w) = IMAGE h w`) THEN
    MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `w:real^M->bool` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`c:real^P->bool`; `k:real^M->bool`] THEN
    ASM_SIMP_TAC[HOMEOMORPHISM_SYM] THEN ASM SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^P->real^M) (f y) = y` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^M->real^P) y IN IMAGE f bk <=> y IN bk` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]]]);;

let MOI_S4YC_MCHART_TRANSPORT = prove
 (`!(k:real^M->bool) (c:real^P->bool) (f:real^M->real^P) g z u (h:real^M->real^N) h'.
     homeomorphism (k,c) (f,g) /\ moi_s4yc_mchart k z u h h'
     ==> moi_s4yc_mchart c (f z) (IMAGE f u) (h o g) (f o h')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4yc_mchart] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^M->bool) SUBSET k` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
    check (fun th -> can (find_term ((=) `k:real^M->bool`)) (concl th) &&
                     can (find_term ((=) `c:real^P->bool`)) (concl th))) THEN
  SUBGOAL_THEN `IMAGE ((h:real^M->real^N) o (g:real^P->real^M)) (IMAGE f u) = IMAGE h u`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^M. x IN s ==> (f:real^M->real^N) x = g x)
                             ==> IMAGE f s = IMAGE g s`) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g:real^P->real^M`; `k:real^M->bool`] THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `u:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`c:real^P->bool`; `k:real^M->bool`] THEN
    ASM_SIMP_TAC[HOMEOMORPHISM_SYM] THEN ASM SET_TAC[]]);;

(* Half-space charts of a 3-simplex at every point. *)

let MOI_S4YC_SIMPLEX3_CHART = prove
 (`!(k:real^N->bool) z.
     &3 simplex k /\ z IN k
     ==> ?w (h:real^N->real^3) h' oo. moi_s4yc_hchart k (relative_frontier k) z w h h' oo`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{f:real^N->bool | f face_of k}`; `z:real^N`] MOI_FMB_CHART) THEN
  ASM_SIMP_TAC[MOI_FMB_FACE_COMPLEX_CMWB; MOI_FMB_FACE_COMPLEX_CB] THEN
  SUBGOAL_THEN `UNIONS {f:real^N->bool | f face_of k} = k` SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN MESON_TAC[FACE_OF_IMP_SUBSET];
      MATCH_MP_TAC(SET_RULE `(k:real^N->bool) IN s ==> k SUBSET UNIONS s`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC FACE_OF_REFL THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (X_CHOOSE_THEN `p:real^N->real^3`
    (X_CHOOSE_THEN `p':real^3->real^N` (X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`w:real^N->bool`; `p:real^N->real^3`; `p':real^3->real^N`;
                        `oo:real^3->bool`] THEN
  ASM_REWRITE_TAC[moi_s4yc_hchart; DIMINDEX_3]);;

let MOI_S4YC_CELL3_CHART = prove
 (`!(c:real^N->bool) bd x.
     pl_cell_with_boundary 3 c bd /\ x IN c
     ==> ?w (h:real^N->real^3) h' oo. moi_s4yc_hchart c bd x w h h' oo`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(g:real^N->real^N) x IN k /\ f (g x) = x` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(g:real^N->real^N) x`] MOI_S4YC_SIMPLEX3_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
    (X_CHOOSE_THEN `h':real^3->real^N` (X_CHOOSE_THEN `oo:real^3->bool` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `c:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`;
                 `relative_frontier k:real^N->bool`; `(g:real^N->real^N) x`; `w:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `oo:real^3->bool`]
                MOI_S4YC_HCHART_TRANSPORT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (f:real^N->real^N) w`; `(h:real^N->real^3) o (g:real^N->real^N)`;
                        `(f:real^N->real^N) o (h':real^3->real^N)`; `oo:real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* PL 3-balls in real^3: the boundary part is the frontier. *)

let MOI_S4YC_BALL_CELL = prove
 (`!b:real^3->bool. pl_ball 3 b ==> pl_cell_with_boundary 3 b (frontier b)`,
  REWRITE_TAC[pl_ball; pl_cell_with_boundary] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCD_BALL_FRONTIER THEN
  EXISTS_TAC `g:real^3->real^3` THEN ASM_REWRITE_TAC[]);;

let MOI_S4YC_BALL_CHART = prove
 (`!(b:real^3->bool) x.
     pl_ball 3 b /\ x IN b
     ==> ?w (h:real^3->real^3) h' oo. moi_s4yc_hchart b (frontier b) x w h h' oo`,
  MESON_TAC[MOI_S4YC_BALL_CELL; MOI_S4YC_CELL3_CHART]);;

(* ------------------------------------------------------------------------- *)
(* Half-plane charts of the standard triangle T0 = conv{0,e1,e2}              *)
(* of real^2 at its vertex 0, at the points of the open edge (0,e1) and at   *)
(* interior points; boundary part = relative frontier <-> y$2 = 0.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4YC_STD2_RF = prove
 (`!x:real^2.
     x IN relative_frontier (convex hull {vec 0,basis 1,basis 2}) <=>
     &0 <= x$1 /\ &0 <= x$2 /\ x$1 + x$2 <= &1 /\
     (x$1 = &0 \/ x$2 = &0 \/ x$1 + x$2 = &1)`,
  GEN_TAC THEN
  MP_TAC MOI_PL2_STD_TRIANGLES THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE; IN_UNION; MOI_PL2_IN_SEGMENT_BASE] THEN
  REWRITE_TAC[IN_SEGMENT; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_LID; REAL_ADD_RID] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `&1 - (x:real^2)$2` THEN ASM_REAL_ARITH_TAC;
    DISJ1_TAC THEN ASM_REAL_ARITH_TAC;
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `(x:real^2)$2` THEN ASM_REAL_ARITH_TAC]);;

(* Continuity of real-valued expressions built from coordinates, +, -,     *)
(* scalar multiples and abs (lifted).                                         *)

let MOI_S4YC_CONT_TAC =
  REPEAT(MATCH_MP_TAC CONTINUOUS_ON_ADD ORELSE MATCH_MP_TAC CONTINUOUS_ON_SUB ORELSE
         MATCH_MP_TAC CONTINUOUS_ON_CMUL ORELSE MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS ORELSE
         CONJ_TAC ORELSE CHANGED_TAC(REWRITE_TAC[LIFT_ADD; LIFT_SUB; LIFT_CMUL])) THEN
  SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; CONTINUOUS_ON_CONST; DIMINDEX_2; DIMINDEX_1; ARITH];;

(* The vertex chart: (x1,x2) |-> (x1 - x2, min x1 x2) near 0. *)

let MOI_S4YC_STD2_VERTEX_CHART = prove
 (`?w (h:real^2->real^2) h' oo.
     moi_s4yc_hchart (convex hull {vec 0,basis 1,basis 2})
                     (relative_frontier (convex hull {vec 0,basis 1,basis 2}))
                     (vec 0) w h h' oo`,
  ABBREV_TAC `t0 = convex hull {vec 0:real^2,basis 1,basis 2}` THEN
  ABBREV_TAC `w = {x:real^2 | x IN t0 /\ x$1 + x$2 < &1 / &2}` THEN
  ABBREV_TAC `h = \x:real^2. (x$1 - x$2) % basis 1 +
                              (inv(&2) * (x$1 + x$2 - abs(x$1 - x$2))) % basis 2:real^2` THEN
  ABBREV_TAC `h' = \y:real^2. (y$2 + inv(&2) * (y$1 + abs(y$1))) % basis 1 +
                               (y$2 + inv(&2) * (abs(y$1) - y$1)) % basis 2:real^2` THEN
  ABBREV_TAC `oo = {y:real^2 | abs(y$1) + &2 * abs(y$2) < &1 / &2}` THEN
  MAP_EVERY EXISTS_TAC [`w:real^2->bool`; `h:real^2->real^2`; `h':real^2->real^2`;
                        `oo:real^2->bool`] THEN
  SUBGOAL_THEN `!x:real^2. ((h:real^2->real^2) x)$1 = x$1 - x$2 /\
                          (h x)$2 = (x$1 + x$2 - abs(x$1 - x$2)) / &2`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. ((h':real^2->real^2) y)$1 = y$2 + (y$1 + abs(y$1)) / &2 /\
                           (h' y)$2 = y$2 + (abs(y$1) - y$1) / &2`
  ASSUME_TAC THENL
   [EXPAND_TAC "h'" THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN w <=> &0 <= x$1 /\ &0 <= x$2 /\ x$1 + x$2 < &1 / &2`
  ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN EXPAND_TAC "t0" THEN
    REWRITE_TAC[IN_ELIM_THM; MOI_PL2_IN_TRIANGLE_UP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2 y. x = y <=> x$1 = y$1 /\ x$2 = y$2` ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2]; ALL_TAC] THEN
  SUBGOAL_THEN `(!x:real^2. x IN w ==> h'((h:real^2->real^2) x) = x) /\
                (!y:real^2. y IN oo INTER {y | &0 <= y$2} ==> h (h' y) = y) /\
                IMAGE (h:real^2->real^2) w = oo INTER {y | &0 <= y$2}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      X_GEN_TAC `y:real^2` THEN EXPAND_TAC "oo" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `y:real^2` THEN
      EXPAND_TAC "oo" THEN REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC `(x:real^2) IN w` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        STRIP_TAC THEN EXISTS_TAC `(h':real^2->real^2) y` THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^2->real^2) continuous_on w /\
                (h':real^2->real^2) continuous_on (oo INTER {y | &0 <= y$2})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "h"; EXPAND_TAC "h'"] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF] THEN MOI_S4YC_CONT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_s4yc_hchart; DIMINDEX_2] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN
    EXISTS_TAC `{x:real^2 | (basis 1 + basis 2) dot x < &1 / &2}` THEN
    REWRITE_TAC[OPEN_HALFSPACE_LT] THEN EXPAND_TAC "w" THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; DOT_LADD] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_2; ARITH] THEN MESON_TAC[];
    ASM_REWRITE_TAC[VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
    SUBGOAL_THEN
     `oo = {y:real^2 | (basis 1 + &2 % basis 2) dot y < &1 / &2} INTER
           {y | (basis 1 - &2 % basis 2) dot y < &1 / &2} INTER
           {y | (--basis 1 + &2 % basis 2) dot y < &1 / &2} INTER
           {y | (--basis 1 - &2 % basis 2) dot y < &1 / &2}`
    SUBST1_TAC THENL
     [EXPAND_TAC "oo" THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; DOT_LADD; DOT_LSUB; DOT_LNEG; DOT_LMUL] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
      SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_LT]];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EXPAND_TAC "t0" THEN
    REWRITE_TAC[MOI_S4YC_STD2_RF] THEN
    UNDISCH_TAC `(x:real^2) IN w` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Identity charts (the edge and interior charts of T0), the                 *)
(* affine parametrization of a triangle by T0, and half-plane charts of      *)
(* 2-simplices and of PL 2-cells at every point.                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S4YC_ID_CHART = prove
 (`!(t:real^N->bool) bt x0 oo.
     open oo /\ x0 IN oo /\ x0 IN t /\
     t INTER oo = oo INTER {x | &0 <= x$(dimindex(:N))} /\
     (!x. x IN t INTER oo ==> (x IN bt <=> x$(dimindex(:N)) = &0))
     ==> moi_s4yc_hchart t bt x0 (t INTER oo) (\x. x) (\x. x) oo`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s4yc_hchart; IMAGE_ID] THEN
  ASM_REWRITE_TAC[IN_INTER; HOMEOMORPHISM_ID] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `oo:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* Edge chart of T0 at s0 e1, 0 < s0 < 1. *)

let MOI_S4YC_STD2_EDGE_CHART = prove
 (`!s0. &0 < s0 /\ s0 < &1
        ==> ?w (h:real^2->real^2) h' oo.
              moi_s4yc_hchart (convex hull {vec 0,basis 1,basis 2})
                              (relative_frontier (convex hull {vec 0,basis 1,basis 2}))
                              (s0 % basis 1) w h h' oo`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = min (s0 / &2) ((&1 - s0) / &2)` THEN
  SUBGOAL_THEN `&0 < d /\ d <= s0 / &2 /\ d <= (&1 - s0) / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `oo = {x:real^2 | abs(x$1 - s0) < d /\ abs(x$2) < d}` THEN
  MAP_EVERY EXISTS_TAC [`convex hull {vec 0:real^2,basis 1,basis 2} INTER oo`;
                        `\x:real^2. x`; `\x:real^2. x`; `oo:real^2->bool`] THEN
  MATCH_MP_TAC MOI_S4YC_ID_CHART THEN REWRITE_TAC[DIMINDEX_2] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `oo = {x:real^2 | basis 1 dot x < s0 + d} INTER {x | (--basis 1) dot x < d - s0} INTER
           {x | basis 2 dot x < d} INTER {x | (--basis 2) dot x < d}`
    SUBST1_TAC THENL
     [EXPAND_TAC "oo" THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; DOT_LNEG] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
      SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_LT]];
    EXPAND_TAC "oo" THEN
    SIMP_TAC[IN_ELIM_THM; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[MOI_PL2_IN_TRIANGLE_UP] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
    EXPAND_TAC "oo" THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; MOI_PL2_IN_TRIANGLE_UP] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^2` THEN EXPAND_TAC "oo" THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; MOI_PL2_IN_TRIANGLE_UP; MOI_S4YC_STD2_RF] THEN
    ASM_REAL_ARITH_TAC]);;

(* Interior chart of T0. *)

let MOI_S4YC_STD2_INT_CHART = prove
 (`!x0:real^2. &0 < x0$1 /\ &0 < x0$2 /\ x0$1 + x0$2 < &1
        ==> ?w (h:real^2->real^2) h' oo.
              moi_s4yc_hchart (convex hull {vec 0,basis 1,basis 2})
                              (relative_frontier (convex hull {vec 0,basis 1,basis 2}))
                              x0 w h h' oo`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = min ((x0:real^2)$1 / &3) (min (x0$2 / &3) ((&1 - x0$1 - x0$2) / &3))` THEN
  SUBGOAL_THEN `&0 < d /\ d <= (x0:real^2)$1 / &3 /\ d <= x0$2 / &3 /\
                d <= (&1 - x0$1 - x0$2) / &3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `oo = {x:real^2 | abs(x$1 - (x0:real^2)$1) < d /\ abs(x$2 - x0$2) < d}` THEN
  MAP_EVERY EXISTS_TAC [`convex hull {vec 0:real^2,basis 1,basis 2} INTER oo`;
                        `\x:real^2. x`; `\x:real^2. x`; `oo:real^2->bool`] THEN
  MATCH_MP_TAC MOI_S4YC_ID_CHART THEN REWRITE_TAC[DIMINDEX_2] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `oo = {x:real^2 | basis 1 dot x < (x0:real^2)$1 + d} INTER {x | (--basis 1) dot x < d - x0$1} INTER
           {x | basis 2 dot x < x0$2 + d} INTER {x | (--basis 2) dot x < d - x0$2}`
    SUBST1_TAC THENL
     [EXPAND_TAC "oo" THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; DOT_LNEG] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
      SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_LT]];
    EXPAND_TAC "oo" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[MOI_PL2_IN_TRIANGLE_UP] THEN ASM_REAL_ARITH_TAC;
    EXPAND_TAC "oo" THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; MOI_PL2_IN_TRIANGLE_UP] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^2` THEN EXPAND_TAC "oo" THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; MOI_PL2_IN_TRIANGLE_UP; MOI_S4YC_STD2_RF] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The affine parametrization of a triangle by T0 and the                    *)
(* half-plane charts of 2-simplices and PL 2-cells at every point.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4YC_AFFINE_HULL_IMAGE = prove
 (`!(l:real^M->real^N) a s.
     linear l
     ==> IMAGE (\x. a + l x) (convex hull s) = convex hull (IMAGE (\x. a + l x) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^M. a + (l:real^M->real^N) x) = (\x. a + x) o l` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  ASM_SIMP_TAC[IMAGE_o; CONVEX_HULL_LINEAR_IMAGE; CONVEX_HULL_TRANSLATION]);;

let MOI_S4YC_NONCOLLINEAR_INDEP = prove
 (`!a b c:real^N u v.
     ~collinear {a,b,c} /\ u % (b - a) + v % (c - a) = vec 0 ==> u = &0 /\ v = &0`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{a:real^N,b,c} = {b,a,c}` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[COLLINEAR_3] THEN REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_CASES_TAC `v = &0` THENL
   [UNDISCH_TAC `u % (b - a) + v % (c - a):real^N = vec 0` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_EQ_0];
    UNDISCH_TAC `~(?c'. c - a:real^N = c' % (b - a))` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    EXISTS_TAC `--(u / v)` THEN
    UNDISCH_TAC `u % (b - a) + v % (c - a):real^N = vec 0` THEN
    DISCH_THEN(MP_TAC o AP_TERM `(%) (inv v):real^N->real^N`) THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; VECTOR_MUL_RZERO] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID] THEN
    REWRITE_TAC[real_div; VECTOR_MUL_LNEG] THEN
    REWRITE_TAC[REAL_MUL_SYM] THEN VECTOR_ARITH_TAC]);;

let MOI_S4YC_STD2_PARAM = prove
 (`!a b c:real^N.
     ~collinear {a,b,c}
     ==> ?g. homeomorphism (convex hull {vec 0,basis 1,basis 2},convex hull {a,b,c})
                           ((\x:real^2. a + x$1 % (b - a) + x$2 % (c - a)),g) /\
             IMAGE (\x:real^2. a + x$1 % (b - a) + x$2 % (c - a))
                   (relative_frontier (convex hull {vec 0,basis 1,basis 2})) =
             relative_frontier (convex hull {a,b,c})`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `l = \x:real^2. x$1 % (b - a) + x$2 % (c - a):real^N` THEN
  SUBGOAL_THEN `linear (l:real^2->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^2. a + x$1 % (b - a) + x$2 % (c - a):real^N) = (\x. a + l x)`
  SUBST1_TAC THENL [EXPAND_TAC "l" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!p q:real^2. IMAGE (\x. a + (l:real^2->real^N) x) (segment[p,q]) =
                             segment[a + l p,a + l q]` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN ASM_SIMP_TAC[SEGMENT_CONVEX_HULL; MOI_S4YC_AFFINE_HULL_IMAGE] THEN
    REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `a + (l:real^2->real^N) (vec 0) = a /\ a + l (basis 1) = b /\ a + l (basis 2) = c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN
    SIMP_TAC[VEC_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC MOI_PL2_STD_TRIANGLES THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC(MESON[] `(?g. (P:(real^N->real^2)->bool) g) /\ Q ==> ?g. P g /\ Q`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMP_COMPACT_CONVEX_HULL THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON];
      ASM_SIMP_TAC[MOI_S4YC_AFFINE_HULL_IMAGE] THEN ASM_REWRITE_TAC[IMAGE_CLAUSES];
      MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`; `(x:real^2)$1 - (y:real^2)$1`;
                     `(x:real^2)$2 - (y:real^2)$2`] MOI_S4YC_NONCOLLINEAR_INDEP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `a + (l:real^2->real^N) x = a + l y` THEN
        EXPAND_TAC "l" THEN VECTOR_ARITH_TAC;
        REWRITE_TAC[REAL_SUB_0; CART_EQ; DIMINDEX_2; FORALL_2] THEN SIMP_TAC[]]];
    ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE; IMAGE_UNION]]);;

(* ------------------------------------------------------------------------- *)
(* Half-plane charts of a triangle at a vertex, at the points                *)
(* of an open edge and at relative interior points; of 2-simplices and of    *)
(* PL 2-cells at every point.                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_S4YC_TRI_CHART = prove
 (`!a b c z:real^N.
     ~collinear {a,b,c} /\
     (z = a \/ z IN segment(a,b) \/ z IN relative_interior (convex hull {a,b,c}))
     ==> ?w (h:real^N->real^2) h' oo.
           moi_s4yc_hchart (convex hull {a,b,c}) (relative_frontier (convex hull {a,b,c}))
                           z w h h' oo`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`] MOI_S4YC_STD2_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `f = \x:real^2. a + x$1 % (b - a) + x$2 % (c - a):real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^2` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `?x0:real^2. x0 IN convex hull {vec 0,basis 1,basis 2} /\ (f:real^2->real^N) x0 = z /\
                ?w (h:real^2->real^2) h' oo.
                  moi_s4yc_hchart (convex hull {vec 0,basis 1,basis 2})
                    (relative_frontier (convex hull {vec 0,basis 1,basis 2})) x0 w h h' oo`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 MP_TAC ASSUME_TAC) o
      check (fun th -> is_disj (concl th))) THENL
     [EXISTS_TAC `vec 0:real^2` THEN REWRITE_TAC[MOI_S4YC_STD2_VERTEX_CHART] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
        EXPAND_TAC "f" THEN REWRITE_TAC[VEC_COMPONENT] THEN VECTOR_ARITH_TAC];
      REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `u % basis 1:real^2` THEN ASM_SIMP_TAC[MOI_S4YC_STD2_EDGE_CHART] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[MOI_PL2_IN_TRIANGLE_UP] THEN
        SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
        ASM_REAL_ARITH_TAC;
        EXPAND_TAC "f" THEN
        SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
        ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
      EXISTS_TAC `(g:real^N->real^2) z` THEN
      SUBGOAL_THEN `(z:real^N) IN convex hull {a,b,c}` ASSUME_TAC THENL
       [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^N->real^2) z IN convex hull {vec 0,basis 1,basis 2} /\
                    (f:real^2->real^N) (g z) = z` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((g:real^N->real^2) z IN relative_frontier (convex hull {vec 0,basis 1,basis 2}))`
      MP_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `(z:real^N) IN relative_frontier (convex hull {a,b,c})` MP_TAC THENL
         [SUBGOAL_THEN `(z:real^N) IN IMAGE (f:real^2->real^N)
                          (relative_frontier (convex hull {vec 0,basis 1,basis 2}))` MP_TAC THENL
           [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(g:real^N->real^2) z` THEN ASM_REWRITE_TAC[];
            ASM_REWRITE_TAC[]];
          REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `(g:real^N->real^2) z IN convex hull {vec 0,basis 1,basis 2}` THEN
      REWRITE_TAC[MOI_PL2_IN_TRIANGLE_UP; MOI_S4YC_STD2_RF] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4YC_STD2_INT_CHART THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`convex hull {vec 0:real^2,basis 1,basis 2}`; `convex hull {a:real^N,b,c}`;
                 `f:real^2->real^N`; `g:real^N->real^2`;
                 `relative_frontier (convex hull {vec 0:real^2,basis 1,basis 2})`;
                 `x0:real^2`; `w:real^2->bool`; `h:real^2->real^2`; `h':real^2->real^2`;
                 `oo:real^2->bool`] MOI_S4YC_HCHART_TRANSPORT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC FINITE_IMP_COMPACT_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (f:real^2->real^N) w`; `(h:real^2->real^2) o (g:real^N->real^2)`;
                        `(f:real^2->real^N) o (h':real^2->real^2)`; `oo:real^2->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4YC_SIMPLEX2_CHART = prove
 (`!(k:real^N->bool) z.
     &2 simplex k /\ z IN k
     ==> ?w (h:real^N->real^2) h' oo. moi_s4yc_hchart k (relative_frontier k) z w h h' oo`,
  REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `(z:real^N) IN relative_interior (convex hull {a,b,c}) \/ z = a \/ z = b \/ z = c \/
    z IN segment(a,b) \/ z IN segment(b,c) \/ z IN segment(c,a)`
  MP_TAC THENL
   [ASM_CASES_TAC `(z:real^N) IN relative_frontier (convex hull {a,b,c})` THENL
     [UNDISCH_TAC `(z:real^N) IN relative_frontier (convex hull {a,b,c})` THEN
      ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE; IN_UNION; SEGMENT_CLOSED_OPEN;
                   IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
      DISJ1_TAC THEN UNDISCH_TAC `~((z:real^N) IN relative_frontier (convex hull {a,b,c}))` THEN
      REWRITE_TAC[relative_frontier; IN_DIFF] THEN
      SUBGOAL_THEN `closure(convex hull {a:real^N,b,c}) = convex hull {a,b,c}` SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MATCH_MP_TAC FINITE_IMP_COMPACT_CONVEX_HULL THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC MOI_S4YC_TRI_CHART THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4YC_TRI_CHART THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `{a:real^N,b,c} = {b,c,a}` SUBST_ALL_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4YC_TRI_CHART THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `{a:real^N,b,c} = {c,a,b}` SUBST_ALL_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4YC_TRI_CHART THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4YC_TRI_CHART THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `{a:real^N,b,c} = {b,c,a}` SUBST_ALL_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4YC_TRI_CHART THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `{a:real^N,b,c} = {c,a,b}` SUBST_ALL_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4YC_TRI_CHART THEN ASM_REWRITE_TAC[]]);;

let MOI_S4YC_CELL2_CHART = prove
 (`!(c:real^N->bool) bd x.
     pl_cell_with_boundary 2 c bd /\ x IN c
     ==> ?w (h:real^N->real^2) h' oo. moi_s4yc_hchart c bd x w h h' oo`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(g:real^N->real^N) x IN k /\ f (g x) = x` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(g:real^N->real^N) x`] MOI_S4YC_SIMPLEX2_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^2`
    (X_CHOOSE_THEN `h':real^2->real^N` (X_CHOOSE_THEN `oo:real^2->bool` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `c:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`;
                 `relative_frontier k:real^N->bool`; `(g:real^N->real^N) x`; `w:real^N->bool`;
                 `h:real^N->real^2`; `h':real^2->real^N`; `oo:real^2->bool`]
                MOI_S4YC_HCHART_TRANSPORT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (f:real^N->real^N) w`; `(h:real^N->real^2) o (g:real^N->real^N)`;
                        `(f:real^N->real^N) o (h':real^2->real^N)`; `oo:real^2->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Half-line charts of segments (PL arcs) at every point, by                 *)
(* the affine parameter lam w = ((w - a) dot (b - a)) / |b - a|^2.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4YC_SEG_PARAM = prove
 (`!a b:real^N.
     ~(a = b)
     ==> (!s. (((a + s % (b - a)) - a) dot (b - a)) / ((b - a) dot (b - a)) = s) /\
         (!w. w IN segment[a,b]
              ==> w = a + (((w - a) dot (b - a)) / ((b - a) dot (b - a))) % (b - a) /\
                  &0 <= ((w - a) dot (b - a)) / ((b - a) dot (b - a)) /\
                  ((w - a) dot (b - a)) / ((b - a) dot (b - a)) <= &1) /\
         (!s. &0 <= s /\ s <= &1 ==> a + s % (b - a) IN segment[a,b])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((b - a:real^N) dot (b - a) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. (((a + s % (b - a)) - a) dot (b - a)) / ((b - a:real^N) dot (b - a)) = s`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[VECTOR_ARITH `(a + x) - a:real^N = x`; DOT_LMUL] THEN
    UNDISCH_TAC `~((b - a:real^N) dot (b - a) = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^N` THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `w:real^N = a + u % (b - a)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
    EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]);;

(* A window chart: the points of the segment with parameter in (p,q),      *)
(* shifted by c (c = 0 near the end a, c = p away from the ends).          *)

let MOI_S4YC_SEG_WINDOW_CHART = prove
 (`!a b z:real^N p q c.
     ~(a = b) /\ p < q /\ q <= &1 /\ (c = &0 \/ &0 < c /\ c <= p) /\
     z IN segment[a,b] /\
     p < ((z - a) dot (b - a)) / ((b - a) dot (b - a)) /\
     ((z - a) dot (b - a)) / ((b - a) dot (b - a)) < q
     ==> ?w (h:real^N->real^1) h' oo. moi_s4yc_hchart (segment[a,b]) {a,b} z w h h' oo`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(MATCH_MP MOI_S4YC_SEG_PARAM (ASSUME `~(a:real^N = b)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L1") (CONJUNCTS_THEN2 (LABEL_TAC "L2") (LABEL_TAC "L3"))) THEN
  ABBREV_TAC `lam = \w:real^N. ((w - a) dot (b - a)) / ((b - a) dot (b - a))` THEN
  SUBGOAL_THEN `(\x:real^N. lift((lam:real^N->real) x)) continuous_on (:real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^N. ((w - a) dot (b - a)) / ((b - a) dot (b - a)) = lam w`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [EXPAND_TAC "lam" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(lam:real^N->real) a = &0 /\ lam b = &1` STRIP_ASSUME_TAC THENL
   [USE_THEN "L1" (MP_TAC o SPEC `&0`) THEN USE_THEN "L1" (MP_TAC o SPEC `&1`) THEN
    REWRITE_TAC[VECTOR_ARITH `a + &0 % (b - a):real^N = a`;
                VECTOR_ARITH `a + &1 % (b - a):real^N = b`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {w:real^N | p < lam w /\ lam w < q}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^N. lift((lam:real^N->real) x)`; `(:real^N)`;
                   `{t:real^1 | t$1 > p} INTER {t:real^1 | t$1 < q}`] CONTINUOUS_OPEN_PREIMAGE) THEN
    ASM_SIMP_TAC[OPEN_UNIV; OPEN_INTER; OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT] THEN
    REWRITE_TAC[IN_UNIV; IN_INTER; IN_ELIM_THM; LIFT_COMPONENT; real_gt];
    ALL_TAC] THEN
  ABBREV_TAC `ww = segment[a:real^N,b] INTER {w | p < (lam:real^N->real) w /\ lam w < q}` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (segment[a:real^N,b])) ww` ASSUME_TAC THENL
   [EXPAND_TAC "ww" THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `oo = {t:real^1 | t$1 > p - c} INTER {t | t$1 < q - c}` THEN
  ABBREV_TAC `h = \w:real^N. lift((lam:real^N->real) w - c)` THEN
  ABBREV_TAC `h' = \t:real^1. a + (t$1 + c) % (b - a):real^N` THEN
  SUBGOAL_THEN `!w:real^N. w IN ww <=> w IN segment[a,b] /\ p < lam w /\ lam w < q`
  ASSUME_TAC THENL
   [EXPAND_TAC "ww" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!w:real^N. w IN ww ==> (h':real^1->real^N) (h w) = w) /\
    (!t:real^1. t IN oo INTER {y | &0 <= y$1} ==> (h:real^N->real^1) (h' t) = t) /\
    IMAGE (h:real^N->real^1) ww = oo INTER {y | &0 <= y$1}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!t:real^1. t IN oo <=> p - c < t$1 /\ t$1 < q - c` ASSUME_TAC THENL
     [EXPAND_TAC "oo" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
    SUBGOAL_THEN `!w:real^N. (h:real^N->real^1) w = lift(lam w - c)` ASSUME_TAC THENL
     [EXPAND_TAC "h" THEN REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!t:real^1. (h':real^1->real^N) t = a + (t$1 + c) % (b - a)` ASSUME_TAC THENL
     [EXPAND_TAC "h'" THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `w:real^N` THEN ASM_REWRITE_TAC[LIFT_COMPONENT; REAL_SUB_ADD] THEN STRIP_TAC THEN
      ASM_MESON_TAC[];
      X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[REAL_ARITH `(x + c) - c = x:real`] THEN
      DISCH_TAC THEN REWRITE_TAC[GSYM drop; LIFT_DROP];
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `t:real^1` THEN
      ASM_REWRITE_TAC[] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[LIFT_COMPONENT] THEN
        SUBGOAL_THEN `&0 <= (lam:real^N->real) w` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        STRIP_TAC THEN EXISTS_TAC `a + ((t:real^1)$1 + c) % (b - a):real^N` THEN
        ASM_REWRITE_TAC[REAL_ARITH `(x + c) - c = x:real`] THEN REPEAT CONJ_TAC THENL
         [REWRITE_TAC[GSYM drop; LIFT_DROP];
          USE_THEN "L3" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h':real^1->real^N) (oo INTER {y | &0 <= y$1}) = ww` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (h:real^N->real^1) ww = oo INTER {y | &0 <= y$1}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `!w:real^N. w IN ww ==> (h':real^1->real^N) (h w) = w` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^1) continuous_on ww /\
                (h':real^1->real^N) continuous_on (oo INTER {y | &0 <= y$1})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "h" THEN REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      EXPAND_TAC "h'" THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF] THEN MOI_S4YC_CONT_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`ww:real^N->bool`; `h:real^N->real^1`; `h':real^1->real^N`;
                        `oo:real^1->bool`] THEN
  REWRITE_TAC[moi_s4yc_hchart; DIMINDEX_1] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[homeomorphism] THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "oo" THEN
    SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^N` THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[LIFT_COMPONENT; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y:real^N = b)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) = a <=> lam y = &0` SUBST1_TAC THENL
     [EQ_TAC THENL
       [DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN
        SUBGOAL_THEN `y:real^N = a + lam y % (b - a)` SUBST1_TAC THENL
         [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_S4YC_SEG_CHART = prove
 (`!a b z:real^N.
     ~(a = b) /\ z IN segment[a,b]
     ==> ?w (h:real^N->real^1) h' oo. moi_s4yc_hchart (segment[a,b]) {a,b} z w h h' oo`,
  SUBGOAL_THEN
   `!a b z:real^N.
     ~(a = b) /\ z IN segment[a,b] /\ ~(z = b)
     ==> ?w (h:real^N->real^1) h' oo. moi_s4yc_hchart (segment[a,b]) {a,b} z w h h' oo`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(MATCH_MP MOI_S4YC_SEG_PARAM (ASSUME `~(a:real^N = b)`)) THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^N` o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `u = ((z - a) dot (b - a)) / ((b - a:real^N) dot (b - a))` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "zu") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(u = &1)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(z:real^N = b)` THEN REWRITE_TAC[] THEN
      USE_THEN "zu" SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REMOVE_THEN "zu" (K ALL_TAC) THEN
    MATCH_MP_TAC MOI_S4YC_SEG_WINDOW_CHART THEN
    ASM_CASES_TAC `u = &0` THENL
     [MAP_EVERY EXISTS_TAC [`-- &1`; `&1 / &2`; `&0`] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`u / &2`; `(&1 + u) / &2`; `u / &2`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `z:real^N = b` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`b:real^N`; `a:real^N`; `z:real^N`]) THEN
    SUBGOAL_THEN `segment[b:real^N,a] = segment[a,b] /\ {b,a} = {a,b}`
     (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL [MESON_TAC[SEGMENT_SYM]; SET_TAC[]]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_S4YC_RF_SEGMENT = prove
 (`!a b:real^N. ~(a = b) ==> relative_frontier(segment[a,b]) = {a,b}`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[relative_frontier; RELATIVE_INTERIOR_SEGMENT; CLOSURE_SEGMENT] THEN
  REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] ENDS_NOT_IN_SEGMENT) THEN SET_TAC[]);;

let MOI_S4YC_SIMPLEX1_CHART = prove
 (`!(k:real^N->bool) z.
     &1 simplex k /\ z IN k
     ==> ?w (h:real^N->real^1) h' oo. moi_s4yc_hchart k (relative_frontier k) z w h h' oo`,
  REWRITE_TAC[MOI_PL2_SIMPLEX_1] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[MOI_S4YC_RF_SEGMENT] THEN
  MATCH_MP_TAC MOI_S4YC_SEG_CHART THEN ASM_REWRITE_TAC[]);;

let MOI_S4YC_CELL1_CHART = prove
 (`!(c:real^N->bool) bd x.
     pl_cell_with_boundary 1 c bd /\ x IN c
     ==> ?w (h:real^N->real^1) h' oo. moi_s4yc_hchart c bd x w h h' oo`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(g:real^N->real^N) x IN k /\ f (g x) = x` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(g:real^N->real^N) x`] MOI_S4YC_SIMPLEX1_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^1`
    (X_CHOOSE_THEN `h':real^1->real^N` (X_CHOOSE_THEN `oo:real^1->bool` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `c:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`;
                 `relative_frontier k:real^N->bool`; `(g:real^N->real^N) x`; `w:real^N->bool`;
                 `h:real^N->real^1`; `h':real^1->real^N`; `oo:real^1->bool`]
                MOI_S4YC_HCHART_TRANSPORT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (f:real^N->real^N) w`; `(h:real^N->real^1) o (g:real^N->real^N)`;
                        `(f:real^N->real^N) o (h':real^1->real^N)`; `oo:real^1->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Ambient charts.  The boundary part of a half-space chart is               *)
(* an ambient chart of the boundary (projection to the first coordinates);   *)
(* charts of PL 2-spheres and PL circles at every point (boundary parts of   *)
(* the simplex charts, transported), and the identity chart of real^N.       *)
(* ------------------------------------------------------------------------- *)

let MOI_S4YC_EUCLID_CHART = prove
 (`!x:real^N. moi_s4yc_mchart (:real^N) x (:real^N) (\y. y) (\y. y)`,
  REWRITE_TAC[moi_s4yc_mchart; IMAGE_ID; IN_UNIV; OPEN_UNIV; HOMEOMORPHISM_ID; OPEN_IN_REFL]);;

let MOI_S4YC_HCHART_BOUNDARY = prove
 (`!(x1:real^M->bool) b1 x w (h:real^M->real^N) h' oo (p:real^N->real^P) (e:real^P->real^N).
     moi_s4yc_hchart x1 b1 x w h h' oo /\ b1 SUBSET x1 /\ x IN b1 /\
     linear p /\ linear e /\ (!u. p(e u) = u) /\ (!u. (e u)$(dimindex(:N)) = &0) /\
     (!y. y$(dimindex(:N)) = &0 ==> e(p y) = y)
     ==> moi_s4yc_mchart b1 x (w INTER b1) (p o h) (h' o e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4yc_hchart; moi_s4yc_mchart] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^M. y IN w INTER b1
                ==> ((h:real^M->real^N) y)$(dimindex(:N)) = &0 /\ h y IN oo`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^M. y IN w INTER b1
                ==> (e:real^P->real^N) ((p:real^N->real^P) ((h:real^M->real^N) y)) = h y`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean x1) (w:real^M->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `t:real^M->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[IN_INTER];
    SUBGOAL_THEN `IMAGE ((p:real^N->real^P) o (h:real^M->real^N)) (w INTER b1) =
                  {u | (e:real^P->real^N) u IN oo}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM; IN_ELIM_THM] THEN X_GEN_TAC `u:real^P` THEN
      EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `y:real^M` STRIP_ASSUME_TAC) THEN ASM_MESON_TAC[];
        DISCH_TAC THEN
        SUBGOAL_THEN `(e:real^P->real^N) u IN IMAGE (h:real^M->real^N) w` MP_TAC THENL
         [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; REAL_LE_REFL]; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^M` THEN
        STRIP_TAC THEN CONJ_TAC THENL
         [ASM_MESON_TAC[]; REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]]];
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT]];
    MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (h:real^M->real^N) (w INTER b1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`w:real^M->bool`; `IMAGE (h:real^M->real^N) w`] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SET_TAC[]];
      REWRITE_TAC[HOMEOMORPHISM; IMAGE_o; SUBSET_REFL] THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[FUN_IN_IMAGE]]]);;

let MOI_S4YC_HCHART_BOUNDARY3 = prove
 (`!(x1:real^M->bool) b1 x w (h:real^M->real^3) h' oo.
     moi_s4yc_hchart x1 b1 x w h h' oo /\ b1 SUBSET x1 /\ x IN b1
     ==> ?u (c:real^M->real^2) c'. moi_s4yc_mchart b1 x u c c'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x1:real^M->bool`; `b1:real^M->bool`; `x:real^M`; `w:real^M->bool`;
                 `h:real^M->real^3`; `h':real^3->real^M`; `oo:real^3->bool`;
                 `\y:real^3. y$1 % basis 1 + y$2 % basis 2:real^2`;
                 `\u:real^2. u$1 % basis 1 + u$2 % basis 2:real^3`] MOI_S4YC_HCHART_BOUNDARY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_3] THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2;
             DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    MESON_TAC[]]);;

let MOI_S4YC_HCHART_BOUNDARY2 = prove
 (`!(x1:real^M->bool) b1 x w (h:real^M->real^2) h' oo.
     moi_s4yc_hchart x1 b1 x w h h' oo /\ b1 SUBSET x1 /\ x IN b1
     ==> ?u (c:real^M->real^1) c'. moi_s4yc_mchart b1 x u c c'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x1:real^M->bool`; `b1:real^M->bool`; `x:real^M`; `w:real^M->bool`;
                 `h:real^M->real^2`; `h':real^2->real^M`; `oo:real^2->bool`;
                 `\y:real^2. lift(y$1)`;
                 `\u:real^1. drop u % basis 1:real^2`] MOI_S4YC_HCHART_BOUNDARY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_2] THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_1; DIMINDEX_2; FORALL_1; FORALL_2; drop;
                LIFT_COMPONENT] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_1;
             DIMINDEX_2; ARITH; LIFT_COMPONENT] THEN REAL_ARITH_TAC;
    MESON_TAC[]]);;

let MOI_S4YC_SPHERE2_CHART = prove
 (`!(s:real^N->bool) x.
     pl_sphere 2 s /\ x IN s ==> ?u (c:real^N->real^2) c'. moi_s4yc_mchart s x u c c'`,
  REWRITE_TAC[pl_sphere; pl_homeomorphism; ARITH_RULE `2 + 1 = 3`] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(g:real^N->real^N) x IN relative_frontier k /\ f (g x) = x` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(g:real^N->real^N) x`] MOI_S4YC_SIMPLEX3_CHART) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
    (X_CHOOSE_THEN `h':real^3->real^N` (X_CHOOSE_THEN `oo:real^3->bool` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `relative_frontier k:real^N->bool`; `(g:real^N->real^N) x`;
                 `w:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `oo:real^3->bool`]
                MOI_S4YC_HCHART_BOUNDARY3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `c:real^N->real^2`
    (X_CHOOSE_THEN `c':real^2->real^N` ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`relative_frontier k:real^N->bool`; `s:real^N->bool`; `f:real^N->real^N`;
                 `g:real^N->real^N`; `(g:real^N->real^N) x`; `u:real^N->bool`;
                 `c:real^N->real^2`; `c':real^2->real^N`] MOI_S4YC_MCHART_TRANSPORT) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_S4YC_SPHERE1_CHART = prove
 (`!(s:real^N->bool) x.
     pl_sphere 1 s /\ x IN s ==> ?u (c:real^N->real^1) c'. moi_s4yc_mchart s x u c c'`,
  REWRITE_TAC[pl_sphere; pl_homeomorphism; ARITH_RULE `1 + 1 = 2`] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(g:real^N->real^N) x IN relative_frontier k /\ f (g x) = x` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(g:real^N->real^N) x`] MOI_S4YC_SIMPLEX2_CHART) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^2`
    (X_CHOOSE_THEN `h':real^2->real^N` (X_CHOOSE_THEN `oo:real^2->bool` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `relative_frontier k:real^N->bool`; `(g:real^N->real^N) x`;
                 `w:real^N->bool`; `h:real^N->real^2`; `h':real^2->real^N`; `oo:real^2->bool`]
                MOI_S4YC_HCHART_BOUNDARY2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `c:real^N->real^1`
    (X_CHOOSE_THEN `c':real^1->real^N` ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`relative_frontier k:real^N->bool`; `s:real^N->bool`; `f:real^N->real^N`;
                 `g:real^N->real^N`; `(g:real^N->real^N) x`; `u:real^N->bool`;
                 `c:real^N->real^1`; `c':real^1->real^N`] MOI_S4YC_MCHART_TRANSPORT) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* Charts of the boundary of a PL 2-cell and of the frontier of a PL 3-ball. *)

let MOI_S4YC_CELL2_BD_CHART = prove
 (`!(c:real^N->bool) bd x.
     pl_cell_with_boundary 2 c bd /\ x IN bd
     ==> ?u (k:real^N->real^1) k'. moi_s4yc_mchart bd x u k k'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(bd:real^N->bool) SUBSET c` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^N->bool`; `bd:real^N->bool`; `x:real^N`] MOI_S4YC_CELL2_CHART) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^2`
    (X_CHOOSE_THEN `h':real^2->real^N` (X_CHOOSE_THEN `oo:real^2->bool` ASSUME_TAC)))) THEN
  MATCH_MP_TAC MOI_S4YC_HCHART_BOUNDARY2 THEN
  MAP_EVERY EXISTS_TAC [`c:real^N->bool`; `w:real^N->bool`; `h:real^N->real^2`;
                        `h':real^2->real^N`; `oo:real^2->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4YC_BALL_BD_CHART = prove
 (`!(b:real^3->bool) x.
     pl_ball 3 b /\ x IN frontier b
     ==> ?u (k:real^3->real^2) k'. moi_s4yc_mchart (frontier b) x u k k'`,
  MESON_TAC[MOI_S4L_BALL_FRONTIER_SPHERE; MOI_S4YC_SPHERE2_CHART]);;

(* ------------------------------------------------------------------------- *)
(* Set-level corollaries.  Open cell interiors in a surface or                *)
(* a curve, gluing of two cells or of two PL 3-balls, the side lemma for     *)
(* two balls with locally equal frontiers, basic facts on PL 3-balls, and   *)
(* connectedness of a PL 2-sphere minus a finite set.                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S4YC_CELL2_OPEN = prove
 (`!(s:real^N->bool) x c1 d1.
     (?u (c:real^N->real^2) c'. moi_s4yc_mchart s x u c c') /\
     pl_cell_with_boundary 2 c1 d1 /\ c1 SUBSET s /\ x IN c1 DIFF d1
     ==> ?v. open v /\ x IN v /\ s INTER v SUBSET c1 DIFF d1`,
  REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c1:real^N->bool`; `d1:real^N->bool`; `x:real^N`] MOI_S4YC_CELL2_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^2`
    (X_CHOOSE_THEN `h':real^2->real^N` (X_CHOOSE_THEN `oo:real^2->bool` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c1:real^N->bool`; `d1:real^N->bool`; `x:real^N`;
                 `u:real^N->bool`; `c:real^N->real^2`; `c':real^2->real^N`;
                 `w:real^N->bool`; `h:real^N->real^2`; `h':real^2->real^N`;
                 `oo:real^2->bool`] MOI_S4YC_HALF_OPEN) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4YC_CELL1_OPEN = prove
 (`!(s:real^N->bool) x c1 d1.
     (?u (c:real^N->real^1) c'. moi_s4yc_mchart s x u c c') /\
     pl_cell_with_boundary 1 c1 d1 /\ c1 SUBSET s /\ x IN c1 DIFF d1
     ==> ?v. open v /\ x IN v /\ s INTER v SUBSET c1 DIFF d1`,
  REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c1:real^N->bool`; `d1:real^N->bool`; `x:real^N`] MOI_S4YC_CELL1_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^1`
    (X_CHOOSE_THEN `h':real^1->real^N` (X_CHOOSE_THEN `oo:real^1->bool` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c1:real^N->bool`; `d1:real^N->bool`; `x:real^N`;
                 `u:real^N->bool`; `c:real^N->real^1`; `c':real^1->real^N`;
                 `w:real^N->bool`; `h:real^N->real^1`; `h':real^1->real^N`;
                 `oo:real^1->bool`] MOI_S4YC_HALF_OPEN) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4YC_CELLS2_GLUE = prove
 (`!(s:real^N->bool) x c1 d1 c2 d2.
     (?u (c:real^N->real^2) c'. moi_s4yc_mchart s x u c c') /\
     pl_cell_with_boundary 2 c1 d1 /\ pl_cell_with_boundary 2 c2 d2 /\
     c1 SUBSET s /\ c2 SUBSET s /\ x IN d1 /\
     (?v. open v /\ x IN v /\ v INTER d1 = v INTER d2) /\
     DISJOINT (c1 DIFF d1) (c2 DIFF d2)
     ==> ?v. open v /\ x IN v /\ s INTER v SUBSET c1 UNION c2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `c:real^N->real^2`
    (X_CHOOSE_THEN `c':real^2->real^N` ASSUME_TAC))) (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `(d1:real^N->bool) SUBSET c1 /\ (d2:real^N->bool) SUBSET c2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN c1 /\ x IN c2` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `v0:real^N->bool` STRIP_ASSUME_TAC o
      check (is_exists o concl)) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c1:real^N->bool`; `d1:real^N->bool`; `x:real^N`] MOI_S4YC_CELL2_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^N->bool` (X_CHOOSE_THEN `h1:real^N->real^2`
    (X_CHOOSE_THEN `h1':real^2->real^N` (X_CHOOSE_THEN `o1:real^2->bool` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`c2:real^N->bool`; `d2:real^N->bool`; `x:real^N`] MOI_S4YC_CELL2_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real^N->bool` (X_CHOOSE_THEN `h2:real^N->real^2`
    (X_CHOOSE_THEN `h2':real^2->real^N` (X_CHOOSE_THEN `o2:real^2->bool` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c1:real^N->bool`; `d1:real^N->bool`; `c2:real^N->bool`;
    `d2:real^N->bool`; `x:real^N`; `u:real^N->bool`;
    `c:real^N->real^2`; `c':real^2->real^N`; `w1:real^N->bool`; `h1:real^N->real^2`;
    `h1':real^2->real^N`; `o1:real^2->bool`; `w2:real^N->bool`; `h2:real^N->real^2`;
    `h2':real^2->real^N`; `o2:real^2->bool`] MOI_S4YC_GLUE) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4YC_CELLS1_GLUE = prove
 (`!(s:real^N->bool) x c1 d1 c2 d2.
     (?u (c:real^N->real^1) c'. moi_s4yc_mchart s x u c c') /\
     pl_cell_with_boundary 1 c1 d1 /\ pl_cell_with_boundary 1 c2 d2 /\
     c1 SUBSET s /\ c2 SUBSET s /\ x IN d1 /\
     (?v. open v /\ x IN v /\ v INTER d1 = v INTER d2) /\
     DISJOINT (c1 DIFF d1) (c2 DIFF d2)
     ==> ?v. open v /\ x IN v /\ s INTER v SUBSET c1 UNION c2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `c:real^N->real^1`
    (X_CHOOSE_THEN `c':real^1->real^N` ASSUME_TAC))) (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `(d1:real^N->bool) SUBSET c1 /\ (d2:real^N->bool) SUBSET c2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_CELL_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN c1 /\ x IN c2` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `v0:real^N->bool` STRIP_ASSUME_TAC o
      check (is_exists o concl)) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c1:real^N->bool`; `d1:real^N->bool`; `x:real^N`] MOI_S4YC_CELL1_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^N->bool` (X_CHOOSE_THEN `h1:real^N->real^1`
    (X_CHOOSE_THEN `h1':real^1->real^N` (X_CHOOSE_THEN `o1:real^1->bool` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`c2:real^N->bool`; `d2:real^N->bool`; `x:real^N`] MOI_S4YC_CELL1_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real^N->bool` (X_CHOOSE_THEN `h2:real^N->real^1`
    (X_CHOOSE_THEN `h2':real^1->real^N` (X_CHOOSE_THEN `o2:real^1->bool` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c1:real^N->bool`; `d1:real^N->bool`; `c2:real^N->bool`;
    `d2:real^N->bool`; `x:real^N`; `u:real^N->bool`;
    `c:real^N->real^1`; `c':real^1->real^N`; `w1:real^N->bool`; `h1:real^N->real^1`;
    `h1':real^1->real^N`; `o1:real^1->bool`; `w2:real^N->bool`; `h2:real^N->real^1`;
    `h2':real^1->real^N`; `o2:real^1->bool`] MOI_S4YC_GLUE) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4YC_BALL_DIFF_FRONTIER = prove
 (`!b:real^3->bool.
     pl_ball 3 b
     ==> closed b /\ frontier b SUBSET b /\ frontier b = b DIFF interior b /\
         b DIFF frontier b = interior b`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `closed (b:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_BALL_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN
  MP_TAC(ISPEC `b:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]);;

let MOI_S4YC_BALLS_GLUE = prove
 (`!(b1:real^3->bool) b2 x.
     pl_ball 3 b1 /\ pl_ball 3 b2 /\ x IN frontier b1 /\
     (?v. open v /\ x IN v /\ v INTER frontier b1 = v INTER frontier b2) /\
     DISJOINT (interior b1) (interior b2)
     ==> x IN interior (b1 UNION b2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPEC `b1:real^3->bool` MOI_S4YC_BALL_DIFF_FRONTIER) THEN
  MP_TAC(ISPEC `b2:real^3->bool` MOI_S4YC_BALL_DIFF_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN b1 /\ x IN b2` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `v0:real^3->bool` STRIP_ASSUME_TAC o
      check (is_exists o concl)) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b1:real^3->bool`; `x:real^3`] MOI_S4YC_BALL_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3->bool` (X_CHOOSE_THEN `h1:real^3->real^3`
    (X_CHOOSE_THEN `h1':real^3->real^3` (X_CHOOSE_THEN `o1:real^3->bool` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`b2:real^3->bool`; `x:real^3`] MOI_S4YC_BALL_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real^3->bool` (X_CHOOSE_THEN `h2:real^3->real^3`
    (X_CHOOSE_THEN `h2':real^3->real^3` (X_CHOOSE_THEN `o2:real^3->bool` ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`(:real^3)`; `b1:real^3->bool`; `frontier b1:real^3->bool`;
                 `b2:real^3->bool`; `frontier b2:real^3->bool`; `x:real^3`; `(:real^3)`;
                 `\y:real^3. y`; `\y:real^3. y`; `w1:real^3->bool`; `h1:real^3->real^3`;
                 `h1':real^3->real^3`; `o1:real^3->bool`; `w2:real^3->bool`;
                 `h2:real^3->real^3`; `h2':real^3->real^3`; `o2:real^3->bool`] MOI_S4YC_GLUE) THEN
  ASM_REWRITE_TAC[MOI_S4YC_EUCLID_CHART; SUBSET_UNIV; INTER_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[interior; IN_ELIM_THM] THEN EXISTS_TAC `v:real^3->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4YC_BALLS_SIDE = prove
 (`!(b:real^3->bool) a x.
     pl_ball 3 b /\ pl_ball 3 a /\ x IN frontier b /\
     (?v. open v /\ x IN v /\ v INTER frontier b = v INTER frontier a) /\
     DISJOINT (interior b) (interior a)
     ==> ?v. open v /\ x IN v /\ v INTER b = v DIFF interior a`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`b:real^3->bool`; `a:real^3->bool`; `x:real^3`] MOI_S4YC_BALLS_GLUE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^3->bool` STRIP_ASSUME_TAC o
    REWRITE_RULE[interior; IN_ELIM_THM]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v0:real^3->bool` STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
  EXISTS_TAC `v1 INTER v0:real^3->bool` THEN ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN
  MP_TAC(ISPEC `b:real^3->bool` MOI_S4YC_BALL_DIFF_FRONTIER) THEN
  MP_TAC(ISPEC `a:real^3->bool` MOI_S4YC_BALL_DIFF_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `a:real^3->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `b:real^3->bool` INTERIOR_SUBSET) THEN
  ASM SET_TAC[]);;

let MOI_S4YC_BALL_BASIC = prove
 (`!b:real^3->bool.
     pl_ball 3 b
     ==> compact b /\ connected (interior b) /\ ~(interior b = {}) /\
         b = closure (interior b) /\ frontier b = b DIFF interior b /\
         pl_sphere 2 (frontier b)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `compact (b:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_BALL_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPEC `b:real^3->bool` MOI_S4YC_BALL_DIFF_FRONTIER) THEN
  ASM_SIMP_TAC[MOI_S4L_BALL_FRONTIER_SPHERE] THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_ball 3 (b:real^3->bool)` THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `convex (k:real^3->bool) /\ closed k /\ ~(k = {})` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `&3 simplex ({}:real^3->bool)` THEN
      REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior (b:real^3->bool) = IMAGE (f:real^3->real^3) (relative_interior k)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:real^3->bool`; `b:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`]
      MOI_SCD_BALL_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `relative_interior k = k DIFF relative_frontier(k:real^3->bool) /\
                  relative_frontier k SUBSET k` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET] THEN REWRITE_TAC[relative_frontier] THEN
      ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
      MP_TAC(ISPEC `k:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `pl_homeomorphism (k,b) (f:real^3->real^3,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `k:real^3->bool`;
                   `relative_frontier k:real^3->bool`] IMAGE_DIFF_INJ_ALT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `b:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `pl_homeomorphism (k,b) (f:real^3->real^3,g)` THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; RELATIVE_INTERIOR_SUBSET];
      ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_RELATIVE_INTERIOR]];
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE (f:real^3->real^3) (closure (relative_interior k)) SUBSET
                    closure (IMAGE f (relative_interior k))` MP_TAC THENL
       [MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
        ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED];
        ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]];
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      UNDISCH_THEN `interior (b:real^3->bool) = IMAGE (f:real^3->real^3) (relative_interior k)`
        (SUBST1_TAC o SYM) THEN REWRITE_TAC[INTERIOR_SUBSET]]]);;

let MOI_S4YC_SPHERE2_DIFF_FINITE = prove
 (`!(s:real^N->bool) e. pl_sphere 2 s /\ FINITE e ==> connected (s DIFF e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism; ARITH_RULE `2 + 1 = 3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) (IMAGE g (s INTER e)) = s INTER e /\
                IMAGE (g:real^N->real^N) (s INTER e) SUBSET relative_frontier k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `!y:real^N. y IN s ==> (f:real^N->real^N) (g y) = y` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (g:real^N->real^N) s = relative_frontier k` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `s DIFF e = IMAGE (f:real^N->real^N) (relative_frontier k DIFF IMAGE g (s INTER e))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^N`; `relative_frontier k:real^N->bool`;
                   `IMAGE (g:real^N->real^N) (s INTER e)`] IMAGE_DIFF_INJ_ALT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `relative_frontier k:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (IMAGE (g:real^N->real^N) (s INTER e))` MP_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INTER]; ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (g:real^N->real^N) (s INTER e) SUBSET relative_frontier k` THEN
  SPEC_TAC(`IMAGE (g:real^N->real^N) (s INTER e)`, `t:real^N->bool`) THEN
  SUBGOAL_THEN `convex (k:real^N->bool) /\ bounded k /\ aff_dim k = &3` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED;
                  AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^N->bool` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[DIFF_EMPTY] THEN MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(:real^2)`; `a:real^N`]
    HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_2] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(t:real^N->bool) SUBSET relative_frontier k` THEN
      UNDISCH_TAC `(a:real^N) IN t` THEN SET_TAC[];
      INT_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^2` (X_CHOOSE_THEN `q:real^2->real^N` MP_TAC)) THEN
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (q:real^2->real^N) (IMAGE p (t DELETE (a:real^N))) = t DELETE a`
  ASSUME_TAC THENL
   [UNDISCH_TAC `!x:real^N. x IN relative_frontier k DELETE a ==> (q:real^2->real^N) (p x) = x` THEN
    UNDISCH_TAC `(t:real^N->bool) SUBSET relative_frontier k` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k DIFF t =
                IMAGE (q:real^2->real^N) ((:real^2) DIFF IMAGE p (t DELETE (a:real^N)))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`q:real^2->real^N`; `(:real^2)`;
                   `IMAGE (p:real^N->real^2) (t DELETE (a:real^N))`] IMAGE_DIFF_INJ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(a:real^N) IN t` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    MATCH_MP_TAC CONNECTED_OPEN_DIFF_COUNTABLE THEN
    REWRITE_TAC[OPEN_UNIV; CONNECTED_UNIV; DIMINDEX_2; LE_REFL] THEN
    MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DELETE]]);;


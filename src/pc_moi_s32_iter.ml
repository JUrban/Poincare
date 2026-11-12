(* ========================================================================= *)
(* pc_moi_s32_iter: Moise Sec 32 Step 1 for all levels and the limit (Moise  *)
(* p.226).  Main theorems LIMIT (MOI_S32_LIMIT of pc_moi_s3032_stmt) and     *)
(* ITERATE_2 (MOI_S32_ITERATE_2 of pc_moi_s3032_stmt3): the levels are       *)
(* enumerated as 0, 1, -1, 2, -2, ..., Step 1 gives a sequence of states,    *)
(* the members that miss the interior of the current even torus persist, and *)
(* the eventual members form the limit family, whose barrier is closed in M  *)
(* and separates.                                                            *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_s32_gfacts.ml";;
needs "src/pc_moi_s3032_stmt3.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: LIMIT.  A compact set off mm (and so off q) misses ms N for      *)
(* some N (finite subcover of the eventual-constancy neighbourhoods); a     *)
(* path in m DIFF mm from hs to ks would then join the two sides of the     *)
(* separation by ms N; so the component of m DIFF mm containing hs misses   *)
(* ks and separates.                                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_S3IT_EVENTUALLY_MISS = prove
 (`!(m:real^N->bool) (ms:num->real^N->bool) mm q p.
     compact p /\ p SUBSET m /\ DISJOINT p mm /\ q IN mm /\
     (!x. x IN m /\ ~(x = q)
          ==> ?u n0. open u /\ x IN u /\ !n. n0 <= n ==> ms n INTER u = mm INTER u)
     ==> ?N. DISJOINT p (ms N)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^N. x IN p
               ==> ?u n0. open u /\ x IN u /\
                          !n. n0 <= n ==> (ms:num->real^N->bool) n INTER u = mm INTER u`
  MP_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:real^N->real^N->bool`
    (X_CHOOSE_THEN `nn:real^N->num` (LABEL_TAC "uu"))) THEN
  UNDISCH_TAC `compact(p:real^N->bool)` THEN REWRITE_TAC[COMPACT_EQ_HEINE_BOREL] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (uu:real^N->real^N->bool) p`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`uu:real^N->real^N->bool`; `p:real^N->bool`; `f':(real^N->bool)->bool`]
                FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `p':real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `IMAGE (nn:real^N->num) p'` num_FINITE) THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN
  REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x:real^N. x IN s ==> ~(x IN t)`] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x:real^N. x IN p' /\ (y:real^N) IN (uu:real^N->real^N->bool) x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p SUBSET UNIONS (f':(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN p` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "uu" (MP_TAC o C MP (ASSUME `(x:real^N) IN p`) o SPEC `x:real^N`) THEN
  DISCH_THEN(MP_TAC o SPEC `N:num` o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM SET_TAC[]);;

let LIMIT = prove
 (MOI_S32_LIMIT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (subtopology euclidean m) ((m:real^N->bool) DIFF mm)` ASSUME_TAC
  THENL
   [UNDISCH_TAC `closed_in (subtopology euclidean m) (mm:real^N->bool)` THEN
    REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open ((m:real^N->bool) DIFF mm)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `m:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(hs:real^N->bool) SUBSET m DIFF mm /\ (ks:real^N->bool) SUBSET m DIFF mm`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!h k:real^N. h IN hs /\ k IN ks ==> ~(connected_component (m DIFF mm) h k)`
  (LABEL_TAC "key") THENL
   [MAP_EVERY X_GEN_TAC [`h:real^N`; `k:real^N`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM OPEN_PATH_CONNECTED_COMPONENT] THEN REWRITE_TAC[path_component] THEN
    DISCH_THEN(X_CHOOSE_THEN `gg:real^1->real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(h:real^N) IN path_image gg /\ (k:real^N) IN path_image gg`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`m:real^N->bool`; `ms:num->real^N->bool`; `mm:real^N->bool`; `q:real^N`;
                   `path_image (gg:real^1->real^N)`] MOI_S3IT_EVENTUALLY_MISS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[COMPACT_PATH_IMAGE] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    UNDISCH_TAC `!n. closed_in (subtopology euclidean m) ((ms:num->real^N->bool) n) /\
                     separates_in m (ms n) hs ks` THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o SPEC `N:num`) THEN REWRITE_TAC[separates_in] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `v:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `open (u:real^N->bool) /\ open (v:real^N->bool)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `m:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `gg:real^1->real^N` CONNECTED_PATH_IMAGE) THEN
    ASM_REWRITE_TAC[connected] THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[separates_in] THEN
  ASM_CASES_TAC `hs:real^N->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`{}:real^N->bool`; `(m:real^N->bool) DIFF mm`] THEN
    ASM_REWRITE_TAC[OPEN_IN_EMPTY; EMPTY_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `h0:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MAP_EVERY EXISTS_TAC
   [`connected_component ((m:real^N->bool) DIFF mm) h0`;
    `((m:real^N->bool) DIFF mm) DIFF connected_component (m DIFF mm) h0`] THEN
  SUBGOAL_THEN `connected_component ((m:real^N->bool) DIFF mm) h0 SUBSET m DIFF mm`
  ASSUME_TAC THENL [REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_SUBSET THEN ASM_SIMP_TAC[OPEN_CONNECTED_COMPONENT] THEN ASM SET_TAC[];
    MATCH_MP_TAC OPEN_SUBSET THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `(m:real^N->bool) DIFF mm` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(m:real^N->bool) DIFF mm`; `h0:real^N`] CLOSED_IN_CONNECTED_COMPONENT) THEN
    REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN SIMP_TAC[];
    SET_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `k:real^N` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN REWRITE_TAC[IN] THEN
    USE_THEN "key" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 2: geometry of the tower for the limit argument.  Revolution        *)
(* preserves disjointness; the region of the even torus T''_(2j) meets the  *)
(* level region of i only for j = i or j = i + 1; away from the centre      *)
(* g (vec 0), a point of M has an open neighbourhood meeting only finitely   *)
(* many solid tori g(rev(D_j)) (the FINITE clause of the tower on a small   *)
(* closed ball, invariance of domain for g).                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S3IT_REV_DISJOINT = prove
 (`!x y:real^3->bool. DISJOINT x y ==> DISJOINT (revolution x) (revolution y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `DISJOINT s t <=> !a:real^3. a IN s /\ a IN t ==> F`] THEN
  REWRITE_TAC[revolution; IN_ELIM_THM] THEN DISCH_TAC THEN X_GEN_TAC `p:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `q':real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(q:real^3) = q'` SUBST_ALL_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[ARITH_EQ];
    ASM_MESON_TAC[]]);;

let MOI_S3IT_REV_IN_CYL = prove
 (`!(g:real^3->real^3) v pp dd s2 k.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> revolution (dd k) SUBSET moi_s32_cyl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s32_model; moi_s32_tower] THEN STRIP_TAC THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN ASM SET_TAC[]);;

let MOI_S3IT_FAR_DISJOINT = prove
 (`!(g:real^3->real^3) v pp dd s2 a b.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ (a + &2 <= b \/ b + &2 <= a)
     ==> DISJOINT (IMAGE g (revolution (dd a))) (IMAGE g (revolution (dd b)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `DISJOINT (revolution ((dd:int->real^3->bool) a)) (revolution (dd b))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3IT_REV_DISJOINT THEN
    UNDISCH_TAC `moi_s32_tower g v pp dd s2` THEN REWRITE_TAC[moi_s32_tower] THEN
    STRIP_TAC THEN ASM_MESON_TAC[DISJOINT_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `a:int`] MOI_S3IT_REV_IN_CYL) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `b:int`] MOI_S3IT_REV_IN_CYL) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_s32_model g v` THEN REWRITE_TAC[moi_s32_model] THEN STRIP_TAC THEN
  REPEAT DISCH_TAC THEN
  REWRITE_TAC[SET_RULE `DISJOINT s t <=> !a:real^3. a IN s /\ a IN t ==> F`] THEN
  REWRITE_TAC[IN_IMAGE] THEN ASM SET_TAC[]);;

let MOI_S3IT_LVL_AWAY = prove
 (`!(g:real^3->real^3) v pp dd s2 i j.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ ~(j = i) /\ ~(j = i + &1)
     ==> DISJOINT (moi_s32_lvl g dd i) (IMAGE g (revolution (dd (&2 * j))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s32_lvl; DISJOINT_UNION] THEN
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC MOI_S3IT_FAR_DISJOINT THEN
  MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `s2:int->real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

let MOI_S3IT_LOCAL_FINITE = prove
 (`!(g:real^3->real^3) v pp dd s2 x.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     x IN moi_s32_open g /\ ~(x = g (vec 0))
     ==> ?u. open u /\ x IN u /\
             FINITE {j:int | ~(IMAGE g (revolution (dd j)) INTER u = {})}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^3) IN moi_s32_open g` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[OPEN_CONTAINS_BALL] (ISPEC `moi_s32_cyl` OPEN_INTERIOR)) THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = min (e / &2) (norm(y:real^3) / &2)` THEN
  SUBGOAL_THEN `&0 < r /\ r < e /\ r < norm(y:real^3)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN UNDISCH_TAC `~(y:real^3 = vec 0)` THEN
    REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(y:real^3,r) SUBSET interior moi_s32_cyl` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y:real^3,e)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (cball(y:real^3,r)) (vec 0 INSERT moi_s32_rim)` ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `!s t (a:real^3). DISJOINT s (a INSERT t) <=> ~(a IN s) /\ DISJOINT s t`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_CBALL; DIST_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. a SUBSET b /\ DISJOINT b c ==> DISJOINT a c`) THEN
    EXISTS_TAC `interior moi_s32_cyl` THEN ASM_REWRITE_TAC[MOI_S3GF_INTERIOR_CYL] THEN
    REWRITE_TAC[SET_RULE `DISJOINT s t <=> !a:real^3. a IN s /\ a IN t ==> F`] THEN
    REWRITE_TAC[IN_ELIM_THM; moi_s32_rim; moi_s32_disk] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {i:int | ~(revolution ((dd:int->real^3->bool) i) INTER cball(y,r) = {})}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_tower g v pp dd s2` THEN REWRITE_TAC[moi_s32_tower] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior moi_s32_cyl SUBSET moi_s32_cyl` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3GF_CYL_PARTS]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (g:real^3->real^3) (ball(y,r))` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[OPEN_BALL] THEN
    UNDISCH_TAC `moi_s32_model g v` THEN REWRITE_TAC[moi_s32_model] THEN STRIP_TAC THEN
    SUBGOAL_THEN `ball(y:real^3,r) SUBSET moi_s32_cyl` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`y:real^3`; `r:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{i:int | ~(revolution ((dd:int->real^3->bool) i) INTER cball(y,r) = {})}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `j:int` THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `j:int`]
                  MOI_S3IT_REV_IN_CYL) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s32_model g v` THEN REWRITE_TAC[moi_s32_model] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`y:real^3`; `r:real`] BALL_SUBSET_CBALL) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: an enumeration of the levels, 0, 1, -1, 2, -2, ... (Moise's       *)
(* order; any enumeration would do).                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_S3IT_EVEN_ODD_DIV = prove
 (`!n. (EVEN n ==> n = 2 * (n DIV 2)) /\ (~EVEN n ==> n + 1 = 2 * ((n + 1) DIV 2))`,
  GEN_TAC THEN REWRITE_TAC[GSYM NOT_EVEN] THEN CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    UNDISCH_TAC `EVEN n` THEN REWRITE_TAC[EVEN_MOD] THEN ARITH_TAC;
    MP_TAC(SPECL [`n + 1`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    SUBGOAL_THEN `EVEN(n + 1)` MP_TAC THENL
     [ASM_REWRITE_TAC[EVEN_ADD; ARITH; GSYM NOT_EVEN]; ALL_TAC] THEN
    REWRITE_TAC[EVEN_MOD] THEN ARITH_TAC]);;

let MOI_S3IT_INT_ENUM = prove
 (`?e:num->int. (!m n. e m = e n ==> m = n) /\ (!i. ?n. e n = i)`,
  EXISTS_TAC `\n. if EVEN n then --(&(n DIV 2)) else &((n + 1) DIV 2):int` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    MP_TAC(SPEC `m:num` MOI_S3IT_EVEN_ODD_DIV) THEN
    MP_TAC(SPEC `n:num` MOI_S3IT_EVEN_ODD_DIV) THEN
    ASM_CASES_TAC `EVEN m` THEN ASM_CASES_TAC `EVEN n` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INT_EQ_NEG2; INT_OF_NUM_EQ;
                INT_ARITH `--x = y <=> x + y = &0:int`;
                INT_ARITH `x = --y <=> x + y = &0:int`; INT_OF_NUM_ADD] THEN
    REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `i:int` THEN
    DISJ_CASES_TAC(INT_ARITH `&1 <= (i:int) \/ i <= &0`) THENL
     [SUBGOAL_THEN `?k. (i:int) = &k` (X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THENL
       [REWRITE_TAC[INT_OF_NUM_EXISTS] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&1 <= (&k:int)` THEN REWRITE_TAC[INT_OF_NUM_LE] THEN DISCH_TAC THEN
      EXISTS_TAC `2 * k - 1` THEN
      SUBGOAL_THEN `~EVEN(2 * k - 1) /\ (2 * k - 1 + 1) DIV 2 = k` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [SUBGOAL_THEN `2 * k - 1 = SUC(2 * (k - 1))` SUBST1_TAC THENL
           [ASM_ARITH_TAC; REWRITE_TAC[EVEN; EVEN_DOUBLE]];
          SUBGOAL_THEN `2 * k - 1 + 1 = 2 * k` SUBST1_TAC THENL
           [ASM_ARITH_TAC; MATCH_MP_TAC DIV_MULT THEN ARITH_TAC]];
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `?k. --(i:int) = &k` (X_CHOOSE_TAC `k:num`) THENL
       [REWRITE_TAC[INT_OF_NUM_EXISTS] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
      EXISTS_TAC `2 * k` THEN REWRITE_TAC[EVEN_DOUBLE] THEN
      SUBGOAL_THEN `(2 * k) DIV 2 = k` SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_MULT THEN ARITH_TAC; ASM_INT_ARITH_TAC]]]);;

(* The sequence of states produced by applying a one-level step along an    *)
(* injective enumeration e of the levels (dependent choice by recursion).    *)

let MOI_S3IT_ITERATE_SEQ = prove
 (`!(S:(B->bool)->A->bool) (C:A->A->B->bool) (e:num->B) a0.
     (!m n. e m = e n ==> m = n) /\ S {} a0 /\
     (!lev a i. S lev a /\ ~(i IN lev) ==> ?a'. S (i INSERT lev) a' /\ C a a' i)
     ==> ?f. f 0 = a0 /\
             (!n. S (IMAGE e {k | k < n}) (f n)) /\
             (!n. C (f n) (f (SUC n)) (e n))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (CONJUNCTS_THEN2 (LABEL_TAC "s0") (LABEL_TAC "step"))) THEN
  MP_TAC(ISPECL [`a0:A`; `\(x:A) (n:num). @a':A. S ((e:num->B) n INSERT IMAGE e {k | k < n}) a' /\
                                                 (C:A->A->B->bool) x a' (e n)`]
                num_RECURSION) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:num->A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rec")) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. IMAGE (e:num->B) {k | k < SUC n} = e n INSERT IMAGE e {k | k < n} /\
                    ~(e n IN IMAGE e {k | k < n})`
  (LABEL_TAC "lev") THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_IMAGE; IN_ELIM_THM; LT] THEN MESON_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `n:num = k` MP_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (S:(B->bool)->A->bool) (IMAGE (e:num->B) {k | k < n}) (f n)
        ==> ?a'. S (e n INSERT IMAGE e {k | k < n}) a' /\ (C:A->A->B->bool) (f n) a' (e n)`
  (LABEL_TAC "ex") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "step" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "lev" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `n:num` th)]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (S:(B->bool)->A->bool) (IMAGE (e:num->B) {k | k < n}) (f n)`
  (LABEL_TAC "st") THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[LT; EMPTY_GSPEC; IMAGE_CLAUSES];
      USE_THEN "lev" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `n:num` th)]) THEN
      USE_THEN "rec" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "ex" (MP_TAC o C MP (ASSUME `(S:(B->bool)->A->bool) (IMAGE (e:num->B) {k | k < n}) (f n)`) o SPEC `n:num`) THEN
      DISCH_THEN(MP_TAC o SELECT_RULE) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
  USE_THEN "rec" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "ex" (MP_TAC o C MP (SPEC `n:num` (ASSUME `!n. (S:(B->bool)->A->bool) (IMAGE (e:num->B) {k | k < n}) (f n)`)) o SPEC `n:num`) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 4: the sequence of states of Step 1 and its basic properties.        *)
(* moi_s3it_seq collects the model, the tower, the enumeration e of the      *)
(* levels and the states f n after the levels e 0, ..., e (n-1), each step   *)
(* changing the set and the members only inside the region of the even      *)
(* torus processed (LEVEL_2).  Members and sets far from the later regions  *)
(* stay; a finite set of levels is processed from some stage on.             *)
(* ------------------------------------------------------------------------- *)

let moi_s3it_seq = new_definition
 `moi_s3it_seq (g:real^3->real^3) v pp dd s2 (e:num->int)
               (f:num->(real^3->bool)->bool) <=>
    moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
    (!m n. e m = e n ==> m = n) /\ (!i. ?n. e n = i) /\
    (!n. moi_s32_state g dd s2 (IMAGE e {k | k < n}) (f n)) /\
    (!n. moi_s32_set g s2 (f (SUC n)) DIFF
           interior (IMAGE g (revolution (dd (&2 * e n)))) =
         moi_s32_set g s2 (f n) DIFF interior (IMAGE g (revolution (dd (&2 * e n))))) /\
    (!n. {c | c IN f (SUC n) /\
              DISJOINT c (interior (IMAGE g (revolution (dd (&2 * e n)))))} =
         {c | c IN f n /\ DISJOINT c (interior (IMAGE g (revolution (dd (&2 * e n)))))})`;;

(* Generic persistence along the steps. *)

let MOI_S3IT_MEMBER_STEPS = prove
 (`!(f:num->(A->bool)->bool) (rr:num->A->bool) c.
     (!n. {c | c IN f (SUC n) /\ DISJOINT c (rr n)} = {c | c IN f n /\ DISJOINT c (rr n)})
     ==> !n d. (!k. n <= k /\ k < n + d ==> DISJOINT c (rr k))
               ==> (c IN f (n + d) <=> c IN f n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "eq") THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "dj") THEN REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `DISJOINT (c:A->bool) (rr (n + d:num))` ASSUME_TAC THENL
   [USE_THEN "dj" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && not(is_forall(concl th)))) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "dj" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  USE_THEN "eq" (MP_TAC o SPEC `n + d:num`) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `c:A->bool`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3IT_SET_STEPS = prove
 (`!(s:num->A->bool) (rr:num->A->bool) u.
     (!n. s (SUC n) DIFF rr n = s n DIFF rr n)
     ==> !n d. (!k. n <= k /\ k < n + d ==> DISJOINT u (rr k))
               ==> s (n + d) INTER u = s n INTER u`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "eq") THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "dj") THEN REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `DISJOINT (u:A->bool) (rr (n + d:num))` ASSUME_TAC THENL
   [USE_THEN "dj" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && not(is_forall(concl th)))) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "dj" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  USE_THEN "eq" (MP_TAC o SPEC `n + d:num`) THEN ASM SET_TAC[]);;

(* A finite set of levels is processed from some stage on. *)

let MOI_S3IT_STAGE = prove
 (`!(e:num->int) J.
     (!m n. e m = e n ==> m = n) /\ (!i. ?n. e n = i) /\ FINITE J
     ==> ?N. !m. N <= m ==> ~(e m IN J)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `idx:int->num` o GEN_REWRITE_RULE I [SKOLEM_THM]) THEN
  MP_TAC(ISPEC `IMAGE (idx:int->num) J` num_FINITE) THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_TAC `a:num`) THEN
  EXISTS_TAC `a + 1` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(idx:int->num) (e (m:num)) = m` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(idx:int->num) (e (m:num)) <= a` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_ARITH_TAC]);;

(* Points of the barrier off K lie in finitely many level regions; members *)
(* lie in IMAGE g v. *)

let MOI_S3IT_LVL_IN_V = prove
 (`!(g:real^3->real^3) v pp dd s2 i.
     moi_s32_tower g v pp dd s2 ==> moi_s32_lvl g dd i SUBSET IMAGE g v`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S3GF_TOWER_TORI) THEN
  REWRITE_TAC[moi_s32_lvl; UNION_SUBSET] THEN MESON_TAC[]);;

let MOI_S3IT_POINT_LEVELS = prove
 (`!(g:real^3->real^3) v pp dd s2 x.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\ x IN IMAGE g v
     ==> FINITE {i:int | x IN moi_s32_lvl g dd i}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `x:real^3`]
                MOI_S3IT_LOCAL_FINITE) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `jj = {j:int | ~(IMAGE (g:real^3->real^3) (revolution (dd j)) INTER u = {})}` THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\j:int. j div &2) jj UNION IMAGE (\j:int. (j - &1) div &2) jj UNION
              IMAGE (\j:int. (j - &2) div &2) jj` THEN
  ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s32_lvl; IN_UNION; IN_IMAGE] THEN
  X_GEN_TAC `i:int` THEN STRIP_TAC THENL
   [DISJ1_TAC THEN EXISTS_TAC `&2 * i:int`;
    DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `&2 * i + &1:int`;
    DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `&2 * i + &2:int`] THEN
  (CONJ_TAC THENL
    [REWRITE_TAC[INT_ARITH `(&2 * i + &1) - &1 = &2 * i:int`;
                 INT_ARITH `(&2 * i + &2) - &2 = &2 * i:int`] THEN
     CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_DIV_UNIQ THEN EXISTS_TAC `&0:int` THEN
     INT_ARITH_TAC;
     EXPAND_TAC "jj" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[]]));;

(* ------------------------------------------------------------------------- *)
(* Part 5: persistence in the sequence.  A member inside the level          *)
(* region of i stays a member (both ways) at all stages after i and i + 1   *)
(* are processed; the barrier set is constant near a point x <> g (vec 0)   *)
(* after the finitely many regions near x are processed.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S3IT_LIMPT_INTER_OPEN = prove
 (`!s u x:real^N. x limit_point_of s /\ open u /\ x IN u ==> x limit_point_of (s INTER u)`,
  REWRITE_TAC[LIMPT_APPROACHABLE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min e d`) THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  UNDISCH_TAC `ball(x:real^N,d) SUBSET u` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]);;

let MOI_S3IT_SEQ_MEMBERS = prove
 (`!(g:real^3->real^3) v pp dd s2 e f c n m.
     moi_s3it_seq g v pp dd s2 e f /\ n <= m /\
     (!k. n <= k /\ k < m ==> DISJOINT c (interior (IMAGE g (revolution (dd (&2 * e k))))))
     ==> (c IN f m <=> c IN f n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3it_seq] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->(real^3->bool)->bool`;
                 `\k. interior (IMAGE (g:real^3->real^3) (revolution (dd (&2 * (e:num->int) k))))`;
                 `c:real^3->bool`] MOI_S3IT_MEMBER_STEPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`n:num`; `m - n:num`]) THEN
  SUBGOAL_THEN `n + (m - n) = m:num` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_S3IT_SEQ_SETS = prove
 (`!(g:real^3->real^3) v pp dd s2 e f u n m.
     moi_s3it_seq g v pp dd s2 e f /\ n <= m /\
     (!k. n <= k /\ k < m ==> DISJOINT u (interior (IMAGE g (revolution (dd (&2 * e k))))))
     ==> moi_s32_set g s2 (f m) INTER u = moi_s32_set g s2 (f n) INTER u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3it_seq] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\k. moi_s32_set (g:real^3->real^3) s2 ((f:num->(real^3->bool)->bool) k)`;
                 `\k. interior (IMAGE (g:real^3->real^3) (revolution (dd (&2 * (e:num->int) k))))`;
                 `u:real^3->bool`] MOI_S3IT_SET_STEPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`n:num`; `m - n:num`]) THEN
  SUBGOAL_THEN `n + (m - n) = m:num` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The members of a state: in a level region, nonempty, inside IMAGE g v,   *)
(* and off the regions of the other even tori.                              *)

let MOI_S3IT_MEMBER_FACTS = prove
 (`!(g:real^3->real^3) v pp dd s2 lev fam c.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_state g dd s2 lev fam /\ c IN fam
     ==> ?i. c SUBSET moi_s32_lvl g dd i /\ ~(c = {}) /\ c SUBSET IMAGE g v /\
             !j. ~(j = i) /\ ~(j = i + &1)
                 ==> DISJOINT c (interior (IMAGE g (revolution (dd (&2 * j)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s32_state g dd s2 lev fam` THEN REWRITE_TAC[moi_s32_state] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^3->bool` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `cc:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s32_lvl g dd i` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3IT_LVL_IN_V THEN
    MAP_EVERY EXISTS_TAC [`pp:int->real^3`; `s2:int->real^3->bool`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `j:int`]
                  MOI_S3IT_LVL_AWAY) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * j)))`
                 INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET moi_s32_lvl g dd i` THEN
    MATCH_ACCEPT_TAC(SET_RULE `!c l a b:real^3->bool.
      c SUBSET l ==> b SUBSET a ==> DISJOINT l a ==> DISJOINT c b`)]);;

(* A member inside the level region of i persists from a stage after which  *)
(* i and i + 1 are never processed. *)

let MOI_S3IT_PERSIST = prove
 (`!(g:real^3->real^3) v pp dd s2 e f c i n.
     moi_s3it_seq g v pp dd s2 e f /\ c SUBSET moi_s32_lvl g dd i /\
     (!m. n <= m ==> ~(e m = i) /\ ~(e m = i + &1))
     ==> !m. n <= m ==> (c IN f m <=> c IN f n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                 `f:num->(real^3->bool)->bool`; `c:real^3->bool`; `n:num`; `m:num`]
                MOI_S3IT_SEQ_MEMBERS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s3it_seq g v pp dd s2 e f` THEN REWRITE_TAC[moi_s3it_seq] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `(e:num->int) k`]
                MOI_S3IT_LVL_AWAY) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * (e:num->int) k)))`
               INTERIOR_SUBSET) THEN
  ASM SET_TAC[]);;

(* Every finite set of levels has a stage after which none is processed;   *)
(* the forms used below. *)

let MOI_S3IT_SEQ_STAGE = prove
 (`!(g:real^3->real^3) v pp dd s2 e f J.
     moi_s3it_seq g v pp dd s2 e f /\ FINITE J ==> ?N. !m. N <= m ==> ~(e m IN J)`,
  REWRITE_TAC[moi_s3it_seq] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_S3IT_STAGE THEN ASM_REWRITE_TAC[]);;

let MOI_S3IT_SEQ_PROCESSED = prove
 (`!(g:real^3->real^3) v pp dd s2 e f N i.
     moi_s3it_seq g v pp dd s2 e f /\ (!m. N <= m ==> ~(e m = i))
     ==> !n. N <= n ==> i IN IMAGE e {k | k < n}`,
  REWRITE_TAC[moi_s3it_seq] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `k:num` o SPEC `i:int` o check (fun th ->
    is_forall(concl th) && is_exists(snd(strip_forall(concl th))))) THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `N <= k:num` (fun th -> ASM_MESON_TAC[th]) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part 6: the limit family ff = the eventual members, and the limit        *)
(* barrier set: points of IMAGE g v have a stage after which the levels     *)
(* around them are never processed; eventual membership; disjointness,     *)
(* finiteness per level, the member clauses for every level; near every     *)
(* point of M other than g (vec 0) the sets of the sequence are eventually  *)
(* constant and equal to the set of ff.                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3IT_POINT_STAGE = prove
 (`!(g:real^3->real^3) v pp dd s2 e f y.
     moi_s3it_seq g v pp dd s2 e f /\ y IN IMAGE g v
     ==> ?N. !m i. N <= m /\ y IN moi_s32_lvl g dd i ==> ~(e m = i) /\ ~(e m = i + &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {i:int | y IN moi_s32_lvl g dd i}` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3it_seq g v pp dd s2 e f` THEN REWRITE_TAC[moi_s3it_seq] THEN
    STRIP_TAC THEN MATCH_MP_TAC MOI_S3IT_POINT_LEVELS THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `s2:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                 `f:num->(real^3->bool)->bool`;
                 `{i:int | y IN moi_s32_lvl g dd i} UNION
                  IMAGE (\i:int. i + &1) {i | y IN moi_s32_lvl g dd i}`]
                MOI_S3IT_SEQ_STAGE) THEN
  ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  REWRITE_TAC[IN_UNION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[]);;

let MOI_S3IT_EVENTUAL_MEMBER = prove
 (`!(g:real^3->real^3) v pp dd s2 e f y N c n.
     moi_s3it_seq g v pp dd s2 e f /\
     (!m i. N <= m /\ y IN moi_s32_lvl g dd i ==> ~(e m = i) /\ ~(e m = i + &1)) /\
     N <= n /\ c IN f n /\ y IN c
     ==> !m. n <= m ==> c IN f m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?i. c SUBSET moi_s32_lvl g dd i` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3it_seq g v pp dd s2 e f` THEN REWRITE_TAC[moi_s3it_seq] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`;
                   `IMAGE (e:num->int) {k | k < n}`; `(f:num->(real^3->bool)->bool) n`;
                   `c:real^3->bool`] MOI_S3IT_MEMBER_FACTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                 `f:num->(real^3->bool)->bool`; `c:real^3->bool`; `i:int`; `n:num`]
                MOI_S3IT_PERSIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `i:int`] o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "moi_s32_lvl" with Failure _ -> false))
          (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_S3IT_FF_DISJOINT = prove
 (`!(g:real^3->real^3) v pp dd s2 e f.
     moi_s3it_seq g v pp dd s2 e f
     ==> pairwise DISJOINT {c | ?n0. !n. n0 <= n ==> c IN f n}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3it_seq] THEN STRIP_TAC THEN
  REWRITE_TAC[pairwise; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real^3->bool`; `c2:real^3->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n1:num`)
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n2:num`) ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n1 + n2:num` o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "moi_s32_state" with Failure _ -> false))
        (concl th))) THEN
  REWRITE_TAC[moi_s32_state; pairwise] THEN
  DISCH_THEN(MP_TAC o SPECL [`c1:real^3->bool`; `c2:real^3->bool`] o CONJUNCT1) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

let MOI_S3IT_FF_FINITE = prove
 (`!(g:real^3->real^3) v pp dd s2 e f i.
     moi_s3it_seq g v pp dd s2 e f
     ==> FINITE {c | c IN {c | ?n0. !n. n0 <= n ==> c IN f n} /\
                     c SUBSET moi_s32_lvl g dd i}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                 `f:num->(real^3->bool)->bool`; `{i:int, i + &1}`] MOI_S3IT_SEQ_STAGE) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{c | c IN (f:num->(real^3->bool)->bool) N /\ c SUBSET moi_s32_lvl g dd i}` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `moi_s3it_seq g v pp dd s2 e f` THEN REWRITE_TAC[moi_s3it_seq] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "moi_s32_state" with Failure _ -> false))
          (concl th))) THEN
    REWRITE_TAC[moi_s32_state] THEN MESON_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `c:real^3->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n0:num`) ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                 `f:num->(real^3->bool)->bool`; `c:real^3->bool`; `i:int`; `N:num`]
                MOI_S3IT_PERSIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n0 + N:num`) THEN
  REWRITE_TAC[LE_ADDR] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part 7: the member clauses of the limit family for every level, the      *)
(* local eventual constancy of the barrier sets and the identification of   *)
(* the limit set, its closedness in M.                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_S3IT_FF_MEMBER = prove
 (`!(g:real^3->real^3) v pp dd s2 e f c.
     moi_s3it_seq g v pp dd s2 e f /\ c IN {c | ?n0. !n. n0 <= n ==> c IN f n}
     ==> ?i cc. c SUBSET moi_s32_lvl g dd i /\
                FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\
                UNIONS cc = c /\ connected c /\ ~(c = {}) /\
                surface_boundary cc = c INTER moi_s32_evens s2 /\
                c INTER moi_s32_evens s2 SUBSET
                  frontier (s2 (&2 * i)) UNION frontier (s2 (&2 * i + &2)) /\
                (i IN (:int)
                 ==> !jj. jj IN components (c INTER frontier (s2 (&2 * i)))
                          ==> moi_s32_ess s2 (&2 * i) jj) /\
                ((i + &1) IN (:int)
                 ==> !jj. jj IN components (c INTER frontier (s2 (&2 * i + &2)))
                          ==> moi_s32_ess s2 (&2 * i + &2) jj)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "seq") (X_CHOOSE_TAC `n0:num`)) THEN
  USE_THEN "seq" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s3it_seq]) THEN
  SUBGOAL_THEN `?y:real^3. y IN c /\ y IN IMAGE (g:real^3->real^3) v` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`;
                   `IMAGE (e:num->int) {k | k < n0}`; `(f:num->(real^3->bool)->bool) n0`;
                   `c:real^3->bool`] MOI_S3IT_MEMBER_FACTS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i0:int` STRIP_ASSUME_TAC) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                 `f:num->(real^3->bool)->bool`; `y:real^3`] MOI_S3IT_POINT_STAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  ABBREV_TAC `n = n0 + N:num` THEN
  SUBGOAL_THEN `(c:real^3->bool) IN f (n:num)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "n" THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "moi_s32_state" with Failure _ -> false))
        (concl th) && is_forall(concl th))) THEN
  REWRITE_TAC[moi_s32_state] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^3->bool` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:int` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `cc:(real^3->bool)->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_UNIV] THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s32_lvl g dd i` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. (!m. N <= m ==> ~((e:num->int) m = j)) ==> j IN IMAGE e {k | k < n}`
  (LABEL_TAC "proc") THENL
   [X_GEN_TAC `j:int` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                   `f:num->(real^3->bool)->bool`; `N:num`; `j:int`] MOI_S3IT_SEQ_PROCESSED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "n" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `i IN IMAGE (e:num->int) {k | k < n} /\ (i + &1) IN IMAGE e {k | k < n}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "proc" MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    USE_THEN "N" (MP_TAC o SPECL [`m:num`; `i:int`]) THEN ASM_SIMP_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_S3IT_FF_LOCAL = prove
 (`!(g:real^3->real^3) v pp dd s2 e f x.
     moi_s3it_seq g v pp dd s2 e f /\ x IN moi_s32_open g /\ ~(x = g (vec 0))
     ==> ?u N. open u /\ x IN u /\
               (!m. N <= m ==> moi_s32_set g s2 (f m) INTER u =
                               moi_s32_set g s2 (f N) INTER u) /\
               moi_s32_set g s2 {c | ?n0. !n. n0 <= n ==> c IN f n} INTER u =
               moi_s32_set g s2 (f N) INTER u`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "seq") STRIP_ASSUME_TAC) THEN
  USE_THEN "seq" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s3it_seq]) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `x:real^3`]
                MOI_S3IT_LOCAL_FINITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE {j:int | (&2 * j) IN
                  {j | ~(IMAGE (g:real^3->real^3) (revolution (dd j)) INTER u = {})}}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                 `f:num->(real^3->bool)->bool`;
                 `{j:int | (&2 * j) IN
                    {j | ~(IMAGE (g:real^3->real^3) (revolution (dd j)) INTER u = {})}}`]
                MOI_S3IT_SEQ_STAGE) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  SUBGOAL_THEN
   `!m:num. N <= m
        ==> DISJOINT u (interior (IMAGE (g:real^3->real^3)
                                    (revolution ((dd:int->real^3->bool) (&2 * (e:num->int) m)))))`
  (LABEL_TAC "dj") THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * e (m:num))))`
                 INTERIOR_SUBSET) THEN
    SPEC_TAC(`interior (IMAGE (g:real^3->real^3)
                (revolution ((dd:int->real^3->bool) (&2 * e (m:num)))))`,`b:real^3->bool`) THEN
    SPEC_TAC(`IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * e (m:num))))`,
             `a:real^3->bool`) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. N <= m ==> moi_s32_set g s2 ((f:num->(real^3->bool)->bool) m) INTER u =
                               moi_s32_set g s2 (f N) INTER u`
  (LABEL_TAC "const") THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3IT_SEQ_SETS THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`;
                          `e:num->int`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "dj" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_s32_set] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[IN_INTER; IN_UNION; IN_SING; IN_UNIONS; IN_ELIM_THM] THEN
  ASM_CASES_TAC `(y:real^3) IN u` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(y:real^3) IN moi_s32_evens s2` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `y = (g:real^3->real^3) (vec 0)` THEN ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_TAC `n0:num`) ASSUME_TAC)) THEN
    USE_THEN "const" (MP_TAC o SPEC `n0 + N:num`) THEN REWRITE_TAC[LE_ADDR] THEN
    REWRITE_TAC[moi_s32_set; EXTENSION; IN_INTER; IN_UNION; IN_SING; IN_UNIONS] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN EXISTS_TAC `c:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (g:real^3->real^3) v` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`;
                   `IMAGE (e:num->int) {k | k < N}`; `(f:num->(real^3->bool)->bool) N`;
                   `c':real^3->bool`] MOI_S3IT_MEMBER_FACTS) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                 `f:num->(real^3->bool)->bool`; `y:real^3`] MOI_S3IT_POINT_STAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Ny:num` (LABEL_TAC "Ny")) THEN
  USE_THEN "const" (MP_TAC o SPEC `N + Ny:num`) THEN REWRITE_TAC[LE_ADD] THEN
  REWRITE_TAC[moi_s32_set; EXTENSION; IN_INTER; IN_UNION; IN_SING; IN_UNIONS] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN ANTS_TAC THENL
   [EXISTS_TAC `c':real^3->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `N + Ny:num` THEN
  MATCH_MP_TAC MOI_S3IT_EVENTUAL_MEMBER THEN
  MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                        `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                        `y:real^3`; `Ny:num`] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part 8: closedness and separation of the limit barrier (LIMIT), the      *)
(* limit state for every level, and ITERATE_2.                               *)
(* ------------------------------------------------------------------------- *)

let MOI_S3IT_FF_SUBSET = prove
 (`!(g:real^3->real^3) v pp dd s2 e f.
     moi_s3it_seq g v pp dd s2 e f
     ==> moi_s32_set g s2 {c | ?n0. !n. n0 <= n ==> c IN f n} SUBSET moi_s32_open g`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "seq") THEN
  USE_THEN "seq" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s3it_seq]) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3GF_TOWER_TORI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[moi_s32_set; moi_s32_evens; UNION_SUBSET; SING_SUBSET] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THENL
   [X_GEN_TAC `i:int` THEN REWRITE_TAC[IN_UNIV] THEN ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `c:real^3->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `n0:num`) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`;
                 `IMAGE (e:num->int) {k | k < n0}`; `(f:num->(real^3->bool)->bool) n0`;
                 `c:real^3->bool`] MOI_S3IT_MEMBER_FACTS) THEN
  ASM_SIMP_TAC[LE_REFL] THEN ASM SET_TAC[]);;

let MOI_S3IT_FF_CLOSED = prove
 (`!(g:real^3->real^3) v pp dd s2 e f.
     moi_s3it_seq g v pp dd s2 e f
     ==> closed_in (subtopology euclidean (moi_s32_open g))
                   (moi_s32_set g s2 {c | ?n0. !n. n0 <= n ==> c IN f n})`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "seq") THEN
  USE_THEN "seq" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s3it_seq]) THEN
  REWRITE_TAC[CLOSED_IN_LIMPT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3IT_FF_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`; `e:num->int`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  ASM_CASES_TAC `x = (g:real^3->real^3) (vec 0)` THENL
   [ASM_REWRITE_TAC[moi_s32_set; IN_UNION; IN_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                 `f:num->(real^3->bool)->bool`; `x:real^3`] MOI_S3IT_FF_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^3) IN moi_s32_set g s2 ((f:num->(real^3->bool)->bool) N)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "moi_s32_state" with Failure _ -> false))
          (concl th) && is_forall(concl th))) THEN
    REWRITE_TAC[moi_s32_state; CLOSED_IN_LIMPT] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3` o CONJUNCT2 o CONJUNCT1 o
               CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LIMPT_SUBSET THEN
    EXISTS_TAC `moi_s32_set g s2 ((f:num->(real^3->bool)->bool) N) INTER u` THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    SUBGOAL_THEN `moi_s32_set g s2 ((f:num->(real^3->bool)->bool) N) INTER u =
                  moi_s32_set g s2 {c | ?n0. !n. n0 <= n ==> c IN f n} INTER u`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S3IT_LIMPT_INTER_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

(* Points kept off every barrier of the sequence are off the limit barrier. *)

let MOI_S3IT_FF_AVOID = prove
 (`!(g:real^3->real^3) v pp dd s2 e f p.
     moi_s3it_seq g v pp dd s2 e f /\ p IN moi_s32_open g /\ ~(p = g (vec 0)) /\
     (!n. ~(p IN moi_s32_set g s2 (f n)))
     ==> ~(p IN moi_s32_set g s2 {c | ?n0. !n. n0 <= n ==> c IN f n})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                 `f:num->(real^3->bool)->bool`; `p:real^3`] MOI_S3IT_FF_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (fun th ->
    is_forall(concl th) && is_neg(snd(dest_forall(concl th))))) THEN
  ASM SET_TAC[]);;

let MOI_S3IT_FF_SEP = prove
 (`!(g:real^3->real^3) v pp dd s2 e f.
     moi_s3it_seq g v pp dd s2 e f
     ==> separates_in (moi_s32_open g)
           (moi_s32_set g s2 {c | ?n0. !n. n0 <= n ==> c IN f n})
           {g moi_s32_qlo} {g moi_s32_qhi}`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "seq") THEN
  USE_THEN "seq" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s3it_seq]) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC MOI_S3GF_MODEL_POINTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN interior moi_s32_cyl ==> (g:real^3->real^3) z IN moi_s32_open g`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((g:real^3->real^3) moi_s32_qlo = g (vec 0)) /\
                ~((g:real^3->real^3) moi_s32_qhi = g (vec 0))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_model g v` THEN REWRITE_TAC[moi_s32_model] THEN STRIP_TAC THEN
    MP_TAC MOI_S3GF_CYL_PARTS THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(moi_s32_qlo = vec 0) /\ ~(moi_s32_qhi = vec 0)` MP_TAC THENL
     [REWRITE_TAC[moi_s32_qlo; moi_s32_qhi; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                  VEC_COMPONENT] THEN REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. ~((g:real^3->real^3) moi_s32_qlo IN
                         moi_s32_set g s2 ((f:num->(real^3->bool)->bool) n)) /\
                        ~(g moi_s32_qhi IN moi_s32_set g s2 (f n))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "moi_s32_state" with Failure _ -> false))
          (concl th) && is_forall(concl th))) THEN
    REWRITE_TAC[moi_s32_state; separates_in] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] LIMIT) THEN
  MAP_EVERY EXISTS_TAC [`\n. moi_s32_set g s2 ((f:num->(real^3->bool)->bool) n)`;
                        `(g:real^3->real^3) (vec 0)`] THEN
  REWRITE_TAC[CONNECTED_SING; SING_SUBSET] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3IT_FF_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`; `e:num->int`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SET_RULE `!s (a:real^3) b. DISJOINT s ({a} UNION {b}) <=> ~(a IN s) /\ ~(b IN s)`] THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_S3IT_FF_AVOID THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`; `e:num->int`] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "moi_s32_state" with Failure _ -> false))
          (concl th) && is_forall(concl th))) THEN
    REWRITE_TAC[moi_s32_state] THEN SIMP_TAC[];
    REWRITE_TAC[moi_s32_set; IN_UNION; IN_SING];
    REWRITE_TAC[moi_s32_set; IN_UNION; IN_SING];
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`;
                   `f:num->(real^3->bool)->bool`; `x:real^3`] MOI_S3IT_FF_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `N:num`] THEN ASM_SIMP_TAC[]]);;

let MOI_S3IT_FF_STATE = prove
 (`!(g:real^3->real^3) v pp dd s2 e f.
     moi_s3it_seq g v pp dd s2 e f
     ==> moi_s32_state g dd s2 (:int) {c | ?n0. !n. n0 <= n ==> c IN f n}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_s32_state] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3IT_FF_DISJOINT THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                          `dd:int->real^3->bool`; `s2:int->real^3->bool`; `e:num->int`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `c:real^3->bool` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3IT_FF_MEMBER THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `e:num->int`;
                          `f:num->(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:int` THEN MATCH_MP_TAC MOI_S3IT_FF_FINITE THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `s2:int->real^3->bool`; `e:num->int`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3IT_FF_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`; `e:num->int`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3IT_FF_SEP THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`; `e:num->int`] THEN
    ASM_REWRITE_TAC[]]);;

let ITERATE_2 = prove
 (MOI_S32_ITERATE_2,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lev2") (K ALL_TAC)) THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                       `dd:int->real^3->bool`; `s2:int->real^3->bool`;
                       `fam:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  X_CHOOSE_THEN `e:num->int` STRIP_ASSUME_TAC MOI_S3IT_INT_ENUM THEN
  MP_TAC(ISPECL
   [`moi_s32_state (g:real^3->real^3) dd s2`;
    `\(fam:(real^3->bool)->bool) (fam':(real^3->bool)->bool) (i:int).
        moi_s32_set (g:real^3->real^3) s2 fam' DIFF
          interior (IMAGE g (revolution ((dd:int->real^3->bool) (&2 * i)))) =
        moi_s32_set g s2 fam DIFF interior (IMAGE g (revolution (dd (&2 * i)))) /\
        {c | c IN fam' /\ DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))} =
        {c | c IN fam /\ DISJOINT c (interior (IMAGE g (revolution (dd (&2 * i)))))}`;
    `e:num->int`; `fam:(real^3->bool)->bool`] MOI_S3IT_ITERATE_SEQ) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`lev:int->bool`; `a:(real^3->bool)->bool`; `i:int`] THEN
    STRIP_TAC THEN
    REMOVE_THEN "lev2" (MP_TAC o SPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
      `dd:int->real^3->bool`; `s2:int->real^3->bool`; `lev:int->bool`;
      `a:(real^3->bool)->bool`; `i:int`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{c | ?n0. !n. n0 <= n ==> c IN (f:num->(real^3->bool)->bool) n}` THEN
  MATCH_MP_TAC MOI_S3IT_FF_STATE THEN
  MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `e:num->int`] THEN
  ASM_REWRITE_TAC[moi_s3it_seq]);;


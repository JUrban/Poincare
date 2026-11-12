(* ========================================================================= *)
(* pc_moi_lt_coverb: Moise GTM 47, the tower of the loop theorem             *)
(* (pp.188-189): double covers in the tower (lt_cover_b). Main theorems      *)
(* NO_SECTION, COMPLEXITY_LIFT, CELLWISE_FINITE, NEXT_SYSTEM (the statement  *)
(* terms MOI_LT_NO_SECTION, MOI_LT_COMPLEXITY_LIFT, MOI_LT_CELLWISE_FINITE,  *)
(* MOI_LT_NEXT_SYSTEM of pc_moi_loop_stmt.ml). Route: the identification set *)
(* of a lift is clopen and proper in that of the map (no section), so it has *)
(* fewer components; a section over a set carrying the loops would close up  *)
(* the lift of a path joining the two points of a fibre; the next system is  *)
(* the derived neighbourhood of the image subcomplex.                        *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_fnd_rn.ml";;
needs "src/pc_moi_lt_cova.ml";;

prioritize_real();;
type_invention_error := true;;



(* ------------------------------------------------------------------------- *)
(* CELLWISE_FINITE.  The identification set of a cellwise map               *)
(* is the finite union over pairs of cells (r,r') of the convex sets of the  *)
(* pairs (x,z) in r x r' with f x = f z (f is affine on r and on r').        *)
(* ------------------------------------------------------------------------- *)

let MOI_LCB_PAIRS_CELL_CONVEX = prove
 (`!(f:real^2->real^N) r r' l y l' y'.
     convex r /\ convex r' /\ linear l /\ (!x. x IN r ==> f x = l x + y) /\
     linear l' /\ (!x. x IN r' ==> f x = l' x + y')
     ==> convex {pastecart x z | x IN r /\ z IN r' /\ f x = f z}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONVEX_ALT; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^(2,2)finite_sum`; `b:real^(2,2)finite_sum`; `t:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `x1:real^2` (X_CHOOSE_THEN `z1:real^2` STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x2:real^2` (X_CHOOSE_THEN `z2:real^2` STRIP_ASSUME_TAC))
      STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(&1 - t) % x1 + t % x2:real^2`; `(&1 - t) % z1 + t % z2:real^2`] THEN
  ASM_REWRITE_TAC[PASTECART_ADD; GSYM PASTECART_CMUL] THEN
  SUBGOAL_THEN `(&1 - t) % x1 + t % x2:real^2 IN r /\ (&1 - t) % z1 + t % z2:real^2 IN r'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] (ASSUME `convex(r:real^2->bool)`));
      MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] (ASSUME `convex(r':real^2->bool)`))] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `l:real^2->real^N`; `y:real^N`; `r:real^2->bool`;
                 `x1:real^2`; `x2:real^2`; `t:real`] MOI_LCA_AFFINE_COMB) THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `l':real^2->real^N`; `y':real^N`; `r':real^2->bool`;
                 `z1:real^2`; `z2:real^2`; `t:real`] MOI_LCA_AFFINE_COMB) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

let CELLWISE_FINITE = prove
 (MOI_LT_CELLWISE_FINITE,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lt_cellwise] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `moi_lt_pairs (f:real^2->real^N) =
    UNIONS {{pastecart x z | x IN r /\ z IN r' /\ f x = f z} | r,r' | r IN p /\ r' IN p}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; moi_lt_pairs; FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`x:real^2`; `z:real^2`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `?r r':real^2->bool. r IN p /\ r' IN p /\ x IN r /\ z IN r'`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `UNIONS p = std_triangle` THEN
        REWRITE_TAC[EXTENSION; IN_UNIONS] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
      MAP_EVERY EXISTS_TAC [`r:real^2->bool`; `r':real^2->bool`] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; PASTECART_INJ] THEN ASM_MESON_TAC[];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`r:real^2->bool`; `r':real^2->bool`] THEN STRIP_TAC THEN
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; moi_lt_pairs; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^2`; `z:real^2`] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `z:real^2`] THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LTD_FINITE_COMPONENTS_UNIONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`r:real^2->bool`; `r':real^2->bool`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CONVEX_CONNECTED THEN
    FIRST_ASSUM(MP_TAC o SPEC `r:real^2->bool`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r':real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `l':real^2->real^N` (X_CHOOSE_THEN `y':real^N` STRIP_ASSUME_TAC)))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)))) THEN
    MATCH_MP_TAC MOI_LCB_PAIRS_CELL_CONVEX THEN
    MAP_EVERY EXISTS_TAC [`l:real^2->real^N`; `y:real^N`; `l':real^2->real^N`; `y':real^N`] THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX]]);;


(* ------------------------------------------------------------------------- *)
(* COMPLEXITY_LIFT.  A clopen proper subset of a set with                    *)
(* finitely many components has fewer components (MOI_LCB_CLOPEN_COMPONENTS_ *)
(* LT, general).  The identification set P2 of a lift f2 is contained in     *)
(* that P of f, closed, open in P (q is locally injective), and P2 <> P:     *)
(* otherwise f2 factors through f and gives a continuous section of q over   *)
(* the image of f (f is a closed map from the compact triangle).             *)
(* ------------------------------------------------------------------------- *)

let MOI_LCB_CLOPEN_COMPONENTS_LT = prove
 (`!u s:real^N->bool.
     FINITE (components u) /\ closed_in (subtopology euclidean u) s /\
     open_in (subtopology euclidean u) s /\ ~(s = u)
     ==> CARD (components s) < CARD (components u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `s:real^N->bool`] CLOPEN_UNIONS_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET u` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `k SUBSET components(s:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `K:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC COMPONENTS_INTERMEDIATE_SUBSET THEN
    EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `components(s:real^N->bool) = k` SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `C:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?x:real^N. x IN C` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN MATCH_MP_TAC IN_COMPONENTS_NONEMPTY THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?K:real^N->bool. K IN k /\ x IN K` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `C:real^N->bool`] IN_COMPONENTS_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_UNIONS] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `C:real^N->bool = K` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `C:real^N->bool`; `K:real^N->bool`] COMPONENTS_EQ) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM SET_TAC[]]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[PSUBSET] THEN
  DISCH_TAC THEN UNDISCH_TAC `~(s:real^N->bool = u)` THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM UNIONS_COMPONENTS]);;

let MOI_LCB_PAIRS_SUBSET = prove
 (`!(q:real^N->real^N) (f:real^2->real^N) f2.
     (!x. x IN std_triangle ==> q(f2 x) = f x)
     ==> moi_lt_pairs f2 SUBSET moi_lt_pairs f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lt_pairs; SUBSET; FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`x:real^2`; `y:real^2`] THEN ASM_MESON_TAC[]);;

let MOI_LCB_PAIRS_CLOSED = prove
 (`!(f2:real^2->real^N).
     f2 continuous_on std_triangle ==> closed (moi_lt_pairs f2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_lt_pairs (f2:real^2->real^N) =
    {z | z IN std_triangle PCROSS std_triangle /\
         (\z. f2(fstcart z) - f2(sndcart z)) z IN {vec 0}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_lt_pairs; EXTENSION; FORALL_PASTECART; IN_ELIM_THM; PASTECART_IN_PCROSS;
                FSTCART_PASTECART; SNDCART_PASTECART; IN_SING; VECTOR_SUB_EQ;
                PASTECART_INJ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
  REWRITE_TAC[CLOSED_SING] THEN
  SIMP_TAC[CLOSED_PCROSS; MOI_LTD_STD_TRIANGLE_BASIC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SIMP_TAC[]);;

let MOI_LCB_PAIRS_OPEN = prove
 (`!(c':real^N->bool) (q:real^N->real^N) s (f:real^2->real^N) f2.
     covering_space (c',q) s /\
     f2 continuous_on std_triangle /\ IMAGE f2 std_triangle SUBSET c' /\
     (!x. x IN std_triangle ==> q(f2 x) = f x)
     ==> open_in (subtopology euclidean (moi_lt_pairs f)) (moi_lt_pairs f2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LCB_PAIRS_SUBSET THEN EXISTS_TAC `q:real^N->real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_lt_pairs; FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`q:real^N->real^N`; `c':real^N->bool`; `s:real^N->bool`;
                 `(f2:real^2->real^N) x`] MOI_LCA_LOCAL_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj"))) THEN
  SUBGOAL_THEN
   `!z. z IN std_triangle
        ==> ?d. &0 < d /\
                !z'. z' IN std_triangle /\ dist(z',z) < d
                     ==> dist((f2:real^2->real^N) z',f2 z) < e`
  (LABEL_TAC "cont") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `(f2:real^2->real^N) continuous_on std_triangle` THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "cont" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN std_triangle`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "cont" (MP_TAC o C MATCH_MP (ASSUME `(y:real^2) IN std_triangle`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`x':real^2`; `y':real^2`] THEN DISCH_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; PASTECART_INJ] THEN
  DISCH_THEN(X_CHOOSE_THEN `x'':real^2` (X_CHOOSE_THEN `y'':real^2`
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN SUBST_ALL_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`x'':real^2`; `y'':real^2`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `dist(x'':real^2,x) < d1 /\ dist(y'':real^2,y) < d2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `dist(pastecart (x:real^2) (y:real^2),pastecart x'' y'') < min d1 d2` THEN
    MP_TAC(ISPECL [`x - x'':real^2`; `y - y'':real^2`] NORM_LE_PASTECART) THEN
    MP_TAC(ISPECL [`x:real^2`; `x'':real^2`] NORM_SUB) THEN
    MP_TAC(ISPECL [`y:real^2`; `y'':real^2`] NORM_SUB) THEN
    REWRITE_TAC[dist; PASTECART_SUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f2:real^2->real^N) x'' IN c' /\ f2 y'' IN c'` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `dist((f2:real^2->real^N) x,f2 x'') < e /\ dist(f2 x,f2 y'') < e`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[DIST_SYM] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d1:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(f2:real^2->real^N) x = f2 y` THEN DISCH_THEN SUBST1_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d2:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^N->real^N) ((f2:real^2->real^N) x'') = q (f2 y'')` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_LCB_FACTOR_SECTION = prove
 (`!(q:real^N->real^N) c' (f:real^2->real^N) f2.
     f continuous_on std_triangle /\ f2 continuous_on std_triangle /\
     IMAGE f2 std_triangle SUBSET c' /\ (!x. x IN std_triangle ==> q(f2 x) = f x) /\
     (!x y. x IN std_triangle /\ y IN std_triangle /\ f x = f y ==> f2 x = f2 y)
     ==> ?h. h continuous_on (IMAGE f std_triangle) /\
             IMAGE h (IMAGE f std_triangle) SUBSET c' /\
             !y. y IN IMAGE f std_triangle ==> q(h y) = y`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `h = \y:real^N. (f2:real^2->real^N)
                               (@x. x IN std_triangle /\ (f:real^2->real^N) x = y)` THEN
  SUBGOAL_THEN `!x. x IN std_triangle ==> (h:real^N->real^N) ((f:real^2->real^N) x) = f2 x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(@x'. x' IN std_triangle /\ (f:real^2->real^N) x' = f x) IN std_triangle /\
      f (@x'. x' IN std_triangle /\ f x' = f x) = f x`
    STRIP_ASSUME_TAC THENL
     [CONV_TAC SELECT_CONV THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `h:real^N->real^N` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC(ISPECL [`f:real^2->real^N`; `h:real^N->real^N`; `std_triangle`;
                       `IMAGE (f:real^2->real^N) std_triangle`; `c':real^N->bool`]
                CONTINUOUS_ON_COMPOSE_QUOTIENT) THEN
  REWRITE_TAC[SUBSET_REFL] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC CLOSED_MAP_IMP_QUOTIENT_MAP THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real^2->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_MESON_TAC[CLOSED_IN_IMP_SUBSET];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; CLOSED_IN_IMP_SUBSET];
        MATCH_MP_TAC CLOSED_IN_COMPACT THEN EXISTS_TAC `std_triangle` THEN
        ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC]]];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `f2:real^2->real^N` THEN
    ASM_SIMP_TAC[o_THM]]);;

let COMPLEXITY_LIFT = prove
 (MOI_LT_COMPLEXITY_LIFT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_lt_tower_complexity] THEN
  MATCH_MP_TAC MOI_LCB_CLOPEN_COMPONENTS_LT THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LCB_PAIRS_SUBSET THEN EXISTS_TAC `q:real^N->real^N` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_LCB_PAIRS_CLOSED THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MOI_LCB_PAIRS_OPEN THEN
    MAP_EVERY EXISTS_TAC [`c':real^N->bool`; `q:real^N->real^N`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    UNDISCH_TAC `~(?h. h continuous_on IMAGE (f:real^2->real^N) std_triangle /\
                       IMAGE h (IMAGE f std_triangle) SUBSET c' /\
                       (!y. y IN IMAGE f std_triangle ==> (q:real^N->real^N) (h y) = y))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LCB_FACTOR_SECTION THEN
    EXISTS_TAC `f2:real^2->real^N` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `pastecart (x:real^2) (y:real^2) IN moi_lt_pairs (f2:real^2->real^N)`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_lt_pairs; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `y:real^2`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_lt_pairs; IN_ELIM_THM; PASTECART_INJ] THEN MESON_TAC[]]]);;


(* ------------------------------------------------------------------------- *)
(* NO_SECTION.  If h were a section over a: join the two points              *)
(* x1 <> x2 of a fibre over a point of a by a path g in UNIONS c' (a        *)
(* connected polyhedron, hence path connected); q o g is freely homotopic to *)
(* a loop p in a (loops_carried); the lifted homotopy KK starts at g, so its *)
(* end tracks start at x1 and x2 and end at different points; hence the lift *)
(* x -> KK(1,x) of p is not closed.  But both lifts of p are closed: one is  *)
(* h o p and the other starts and ends at the second point of a 2-point     *)
(* fibre (lift uniqueness from either end).                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_LCB_SLICE_CONT = prove
 (`!(k:real^(1,1)finite_sum->real^N) t0.
     k continuous_on (interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]) /\
     t0 IN interval[vec 0,vec 1]
     ==> (\x. k(pastecart t0 x)) continuous_on interval[vec 0,vec 1] /\
         (\t. k(pastecart t t0)) continuous_on interval[vec 0,vec 1]`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS]);;

let NO_SECTION = prove
 (MOI_LT_NO_SECTION,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path_connected (UNIONS c':real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `UNIONS c':real^N->bool` PATH_CONNECTED_EQ_CONNECTED_LPC) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC ANR_IMP_LOCALLY_PATH_CONNECTED THEN
      MATCH_MP_TAC ANR_FINITE_UNIONS_CONVEX_CLOSED THEN
      ASM_MESON_TAC[MOI_FM3_LF_CONVEX; MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^N->real^N) continuous_on UNIONS c' /\ IMAGE q (UNIONS c') = UNIONS c`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COVERING_SPACE_IMP_CONTINUOUS; COVERING_SPACE_IMP_SURJECTIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `vec 0 IN interval[vec 0:real^1,vec 1] /\ vec 1 IN interval[vec 0:real^1,vec 1]`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]; ALL_TAC] THEN
  (* the fibre over a point y0 of a and a path between its two points *)
  SUBGOAL_THEN `?y0:real^N. y0 IN a` STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `y0:real^N` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `(HAS_SIZE):(real^N->bool)->num->bool`)) (concl th))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^N` (X_CHOOSE_THEN `x2:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x1:real^N) IN UNIONS c' /\ (q:real^N->real^N) x1 = y0 /\
                (x2:real^N) IN UNIONS c' /\ q x2 = y0`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `path_connected (UNIONS c':real^N->bool)` THEN REWRITE_TAC[path_connected] THEN
  DISCH_THEN(MP_TAC o SPECL [`x1:real^N`; `x2:real^N`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path ((q:real^N->real^N) o (g:real^1->real^N)) /\
                path_image (q o g) SUBSET UNIONS c /\
                pathfinish (q o g) = pathstart (q o g)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE]];
    ALL_TAC] THEN
  (* the loop p in a and the free homotopy HH *)
  UNDISCH_TAC `loops_carried (a:real^N->bool) (UNIONS c)` THEN REWRITE_TAC[loops_carried] THEN
  DISCH_THEN(MP_TAC o SPEC `(q:real^N->real^N) o (g:real^1->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^1->real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `homotopic_loops (UNIONS c) ((q:real^N->real^N) o (g:real^1->real^N)) p` THEN
  REWRITE_TAC[homotopic_loops; HOMOTOPIC_WITH_EUCLIDEAN; pathstart; pathfinish] THEN
  DISCH_THEN(X_CHOOSE_THEN `HH:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  (* the lifted homotopy KK *)
  MP_TAC(ISPECL [`q:real^N->real^N`; `UNIONS c':real^N->bool`; `UNIONS c:real^N->bool`;
                 `HH:real^(1,1)finite_sum->real^N`; `g:real^1->real^N`;
                 `interval[vec 0:real^1,vec 1]`] COVERING_SPACE_LIFT_HOMOTOPY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[path]; ASM_MESON_TAC[path_image]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `KK:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  (* points of the square and slices *)
  SUBGOAL_THEN
   `!z:real^1. z IN interval[vec 0:real^1,vec 1]
        ==> pastecart z (vec 0:real^1) IN
              interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1] /\
            pastecart z (vec 1:real^1) IN
              interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1] /\
            pastecart (vec 1:real^1) z IN
              interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1]`
  ASSUME_TAC THENL [ASM_SIMP_TAC[PASTECART_IN_PCROSS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1]
        ==> (HH:real^(1,1)finite_sum->real^N) z IN UNIONS c /\
            (KK:real^(1,1)finite_sum->real^N) z IN UNIONS c'`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`KK:real^(1,1)finite_sum->real^N`; `vec 0:real^1`] MOI_LCB_SLICE_CONT) THEN
  MP_TAC(ISPECL [`KK:real^(1,1)finite_sum->real^N`; `vec 1:real^1`] MOI_LCB_SLICE_CONT) THEN
  MP_TAC(ISPECL [`HH:real^(1,1)finite_sum->real^N`; `vec 0:real^1`] MOI_LCB_SLICE_CONT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  (* the end tracks of KK lift the same path from x1 <> x2 *)
  SUBGOAL_THEN
   `~((KK:real^(1,1)finite_sum->real^N) (pastecart (vec 1) (vec 0)) =
      KK (pastecart (vec 1) (vec 1)))`
  ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(x1:real^N = x2)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(KK:real^(1,1)finite_sum->real^N) (pastecart (vec 0) (vec 0)) =
      KK (pastecart (vec 0) (vec 1))`
    MP_TAC THENL
     [MP_TAC(ISPECL [`q:real^N->real^N`;
                     `\t. (HH:real^(1,1)finite_sum->real^N) (pastecart t (vec 0))`;
                     `\t. (KK:real^(1,1)finite_sum->real^N) (pastecart t (vec 0))`;
                     `\t. (KK:real^(1,1)finite_sum->real^N) (pastecart t (vec 1))`;
                     `UNIONS c':real^N->bool`; `UNIONS c:real^N->bool`;
                     `interval[vec 0:real^1,vec 1]`; `vec 1:real^1`; `vec 0:real^1`]
        COVERING_SPACE_LIFT_UNIQUE) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[CONNECTED_INTERVAL] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[pathstart; pathfinish]];
    ALL_TAC] THEN
  (* the loop p in a and the lift x -> KK(1,x) of p *)
  SUBGOAL_THEN `(p:real^1->real^N) (vec 0) IN a /\ p (vec 1) = p (vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `p:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN
      REWRITE_TAC[pathstart] THEN ASM SET_TAC[];
      ASM_MESON_TAC[pathstart; pathfinish]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a0 x0. a0 IN interval[vec 0:real^1,vec 1] /\ x0 IN interval[vec 0,vec 1] /\
            (KK:real^(1,1)finite_sum->real^N) (pastecart (vec 1) a0) = (h:real^N->real^N) (p a0)
            ==> KK (pastecart (vec 1) x0) = h (p x0)`
  (LABEL_TAC "uq") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`q:real^N->real^N`; `p:real^1->real^N`;
                   `\x. (KK:real^(1,1)finite_sum->real^N) (pastecart (vec 1) x)`;
                   `(h:real^N->real^N) o (p:real^1->real^N)`;
                   `UNIONS c':real^N->bool`; `UNIONS c:real^N->bool`;
                   `interval[vec 0:real^1,vec 1]`; `a0:real^1`; `x0:real^1`]
      COVERING_SPACE_LIFT_UNIQUE) THEN
    REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CONNECTED_INTERVAL] THEN
    SUBGOAL_THEN `IMAGE (p:real^1->real^N) (interval[vec 0,vec 1]) SUBSET a` ASSUME_TAC THENL
     [ASM_MESON_TAC[path_image]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[path];
      ASM SET_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `t:real^1` o check (fun th ->
        is_forall(concl th) && not(is_imp(snd(dest_forall(concl th)))) &&
        can (find_term ((=) `p:real^1->real^N`)) (concl th))) THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ASM_MESON_TAC[path]; ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]];
      REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the 2-point fibre over p(0) *)
  SUBGOAL_THEN `{x | x IN UNIONS c' /\ (q:real^N->real^N) x = p (vec 0:real^1)} HAS_SIZE 2`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `(HAS_SIZE):(real^N->bool)->num->bool`)) (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!w:real^N. w IN UNIONS c' /\ (q:real^N->real^N) w = p (vec 0:real^1) ==> w = u1 \/ w = u2`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    UNDISCH_TAC `{x | x IN UNIONS c' /\ (q:real^N->real^N) x = p (vec 0:real^1)} =
                 {u1:real^N, u2}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(h:real^N->real^N) ((p:real^1->real^N) (vec 0)) =
    (KK:real^(1,1)finite_sum->real^N) (pastecart (vec 1) (vec 0)) \/
    h (p (vec 0)) = KK (pastecart (vec 1) (vec 1))`
  MP_TAC THENL
   [SUBGOAL_THEN
     `((KK:real^(1,1)finite_sum->real^N) (pastecart (vec 1) (vec 0)) = u1 \/
       KK (pastecart (vec 1) (vec 0)) = u2) /\
      (KK (pastecart (vec 1) (vec 1)) = u1 \/ KK (pastecart (vec 1) (vec 1)) = u2) /\
      ((h:real^N->real^N) ((p:real^1->real^N) (vec 0)) = u1 \/ h (p (vec 0)) = u2)`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (vec 1) (vec 0):real^(1,1)finite_sum` o
          check (fun th -> is_forall(concl th) &&
                           can (find_term ((=) `HH:real^(1,1)finite_sum->real^N`)) (concl th) &&
                           can (find_term ((=) `KK:real^(1,1)finite_sum->real^N`)) (concl th) &&
                           not (can (find_term ((=) `c':(real^N->bool)->bool`)) (concl th)))) THEN
        ASM_SIMP_TAC[];
        ASM_SIMP_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (vec 1) (vec 1):real^(1,1)finite_sum` o
          check (fun th -> is_forall(concl th) &&
                           can (find_term ((=) `HH:real^(1,1)finite_sum->real^N`)) (concl th) &&
                           can (find_term ((=) `KK:real^(1,1)finite_sum->real^N`)) (concl th) &&
                           not (can (find_term ((=) `c':(real^N->bool)->bool`)) (concl th)))) THEN
        ASM_SIMP_TAC[];
        ASM SET_TAC[];
        ASM SET_TAC[]];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [REMOVE_THEN "uq" (MP_TAC o SPECL [`vec 0:real^1`; `vec 1:real^1`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    REMOVE_THEN "uq" (MP_TAC o SPECL [`vec 1:real^1`; `vec 0:real^1`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* NEXT_SYSTEM.  l = the simplices of c' inside the image of                 *)
(* f2 (a finite subcomplex with polyhedron the image); c2 = the derived      *)
(* neighbourhood complex of l in c', fr = the derived frontier.  The cells   *)
(* of f2 are refined by the preimages of the simplices of sd(sd c') inside   *)
(* their images, which lie in c2.                                             *)
(* ------------------------------------------------------------------------- *)

let MOI_LCB_IMAGE_SUBCOMPLEX = prove
 (`!(f2:real^2->real^N) c'.
     lf_simplicial_complex c' /\ moi_lt_cellwise f2 c'
     ==> simplicial_subcomplex {s | s IN c' /\ s SUBSET IMAGE f2 std_triangle} c' /\
         UNIONS {s | s IN c' /\ s SUBSET IMAGE f2 std_triangle} = IMAGE f2 std_triangle`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; SUBSET_RESTRICT; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `moi_lt_cellwise (f2:real^2->real^N) c'` THEN REWRITE_TAC[moi_lt_cellwise] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?r:real^2->bool. r IN p /\ x IN r` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (f2:real^2->real^N) r` THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM SET_TAC[];
    ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

let MOI_LCB_SD2_COVER = prove
 (`!(c:(real^N->bool)->bool) s.
     lf_simplicial_complex c /\ s IN c
     ==> s = UNIONS {t | t IN barycentric_subdivision (barycentric_subdivision c) /\
                         ~(t = {}) /\ t SUBSET s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN MESON_TAC[]] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` BARYCENTRIC_SUBDIVISION_REFINES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `barycentric_subdivision (c:(real^N->bool)->bool)`
    BARYCENTRIC_SUBDIVISION_REFINES) THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?rho:real^N->bool. rho IN f /\ x IN rho` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `rho:real^N->bool`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?t:real^N->bool. t IN g /\ x IN t` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ASM SET_TAC[]]);;

let MOI_LCB_CELLWISE_REFINE = prove
 (`!(f2:real^2->real^N) c' c2.
     FINITE c' /\ lf_simplicial_complex c' /\ moi_lt_cellwise f2 c' /\
     (!t. t IN barycentric_subdivision (barycentric_subdivision c') /\ ~(t = {}) /\
          t SUBSET IMAGE f2 std_triangle ==> t IN c2)
     ==> moi_lt_cellwise f2 c2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_lt_cellwise (f2:real^2->real^N) c'` THEN REWRITE_TAC[moi_lt_cellwise] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `sd2 = barycentric_subdivision (barycentric_subdivision (c':(real^N->bool)->bool))` THEN
  EXISTS_TAC
   `{r INTER {x | (f2:real^2->real^N) x IN t} | r,t |
     r IN p /\ t IN {t | t IN sd2 /\ ~(t = {}) /\ t SUBSET IMAGE f2 r}}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    EXPAND_TAC "sd2" THEN ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?r:real^2->bool. r IN p /\ x IN r` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (f2:real^2->real^N) r IN c'` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c':(real^N->bool)->bool`; `IMAGE (f2:real^2->real^N) r`]
      MOI_LCB_SD2_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `(f2:real^2->real^N) x` o
      GEN_REWRITE_RULE I [EXTENSION]) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`r:real^2->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:real^2->bool`; `t:real^N->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real^2->bool` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `polytope:(real^2->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `IMAGE (f2:real^2->real^N) (r INTER {x | f2 x IN t}) = t` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `r INTER {x | (f2:real^2->real^N) x IN t} =
                    r INTER {x | (l:real^2->real^N) x + y IN t}` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_PLM_POLYHEDRON_AFFINE_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC POLYTOPE_IMP_POLYHEDRON THEN
      MATCH_MP_TAC MOI_FM3_LF_POLYTOPE THEN EXISTS_TAC `sd2:(real^N->bool)->bool` THEN
      EXPAND_TAC "sd2" THEN ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF] THEN
      UNDISCH_TAC `(t:real^N->bool) IN sd2` THEN EXPAND_TAC "sd2" THEN SIMP_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MAP_EVERY EXISTS_TAC [`l:real^2->real^N`; `y:real^N`] THEN ASM_SIMP_TAC[IN_INTER]]]);;

let NEXT_SYSTEM = prove
 (MOI_LT_NEXT_SYSTEM,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c':(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f2:real^2->real^N`; `c':(real^N->bool)->bool`] MOI_LCB_IMAGE_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `l = {s:real^N->bool | s IN c' /\ s SUBSET IMAGE (f2:real^2->real^N) std_triangle}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c':(real^N->bool)->bool`; `l:(real^N->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c':(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_COMBINATORIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c':(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_DEFORMATION_RETRACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  EXISTS_TAC `derived_nbhd_complex (c':(real^N->bool)->bool) l` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* orientability *)
    DISCH_TAC THEN MATCH_MP_TAC MOI_FD_ORIENTABLE_SUBSET THEN
    EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (c':(real^N->bool)->bool))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPEC `c':(real^N->bool)->bool` COMBINATORIAL_WB_BARYCENTRIC) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPEC `barycentric_subdivision (c':(real^N->bool)->bool)`
        COMBINATORIAL_WB_BARYCENTRIC) THEN
      ASM_SIMP_TAC[];
      ASM_MESON_TAC[simplicial_subcomplex]];
    (* cellwise *)
    MATCH_MP_TAC MOI_LCB_CELLWISE_REFINE THEN EXISTS_TAC `c':(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC FACE_OF_REFL THEN MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
      EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (c':(real^N->bool)->bool))` THEN
      ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF]];
    (* image inside *)
    MP_TAC(ISPECL [`subtopology euclidean (UNIONS c':real^N->bool)`;
                   `derived_nbhd (c':(real^N->bool)->bool) l`] INTERIOR_OF_SUBSET) THEN
    ASM SET_TAC[];
    (* the frontier *)
    EXISTS_TAC `derived_frontier (c':(real^N->bool)->bool) l` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN EXISTS_TAC `UNIONS c':real^N->bool` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[derived_frontier] THEN
        MP_TAC(ISPECL [`subtopology euclidean (UNIONS c':real^N->bool)`;
                       `derived_nbhd (c':(real^N->bool)->bool) l`] CLOSED_IN_FRONTIER_OF) THEN
        REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
        ASM_MESON_TAC[MOI_LTD_FINITE_COMPLEX_CLOSED]];
      REWRITE_TAC[derived_frontier; frontier_of] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[]]]);;


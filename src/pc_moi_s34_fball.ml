(* ========================================================================= *)
(* pc_moi_s34_fball: main theorem FBALL : |- MOI_S34_FBALL                  *)
(* (pc_moi_s34_stmt.ml, Moise p.241, Lemma 5): from CELLNB_BODY (small      *)
(* polyhedral cell neighbourhoods in general position, Lemma 3) and LEMMA4  *)
(* (H_1 carried by small ones), a family of face balls with the invariant   *)
(* moi_s34_fbinv.  For each 2-simplex s the ball is chosen in an open set   *)
(* W_s: inside the carrier of s and the set of LEMMA4, away from the vertex *)
(* balls of the other vertices (locally finitely many near h(s), by the     *)
(* frame), and inside U UNION a neighbourhood of h(s) minus U, U the        *)
(* interior of f1(N), with radii chosen symmetrically so that different W_s *)
(* meet only in U.                                                          *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1. Point-set lemmas in real^3: avoiding a locally finite family of  *)
(* closed sets, compact sets inside open sets, and symmetric radii for a    *)
(* locally finite family of pairwise disjoint compact sets.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Q_AVOID = prove
 (`!(k:real^3->bool) (I0:A->bool) (z:A->real^3->bool).
     (!i. i IN I0 ==> closed (z i) /\ DISJOINT k (z i)) /\
     (!y. y IN k ==> ?u. open u /\ y IN u /\ FINITE {i | i IN I0 /\ ~(z i INTER u = {})})
     ==> ?w. open w /\ k SUBSET w /\ !i. i IN I0 ==> DISJOINT w (z i)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cl") (LABEL_TAC "lf")) THEN
  SUBGOAL_THEN
   `!y:real^3. y IN k ==> ?w. open w /\ y IN w /\ !i. i IN I0 ==> DISJOINT w ((z:A->real^3->bool) i)`
  MP_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "lf" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u DIFF UNIONS (IMAGE (z:A->real^3->bool)
                    {i | i IN I0 /\ ~(z i INTER u = {})})` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_DIFF; IN_UNIONS; FORALL_IN_IMAGE; NOT_EXISTS_THM] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `c:real^3->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      USE_THEN "cl" (MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(z:A->real^3->bool) i INTER u = {}` THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `!a b c:real^3->bool. c SUBSET b ==> DISJOINT (a DIFF b) c`) THEN
      MATCH_MP_TAC(SET_RULE `!f (x:real^3->bool). x IN f ==> x SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `i:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `ww:real^3->real^3->bool`) THEN
  EXISTS_TAC `UNIONS (IMAGE (ww:real^3->real^3->bool) k)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE] THEN ASM_MESON_TAC[];
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `i:A` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[DISJOINT; INTER_COMM]]);;

let MOI_S4Q_COMPACT_IN_OPEN = prove
 (`!(k:real^3->bool) v.
     compact k /\ open v /\ k SUBSET v
     ==> ?e. &0 < e /\ !x y. x IN k /\ dist(x,y) < e ==> y IN v`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `k:real^3->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  ASM_CASES_TAC `v:real^3->bool = (:real^3)` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[IN_UNIV; REAL_LT_01]; ALL_TAC] THEN
  EXISTS_TAC `setdist(k,(:real^3) DIFF v)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_LE; SETDIST_POS_LE] THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN
    ASM_SIMP_TAC[SETDIST_EQ_0_COMPACT_CLOSED; GSYM OPEN_CLOSED] THEN
    ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(y:real^3) IN v` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:real^3->bool`; `(:real^3) DIFF v`; `x:real^3`; `y:real^3`]
      SETDIST_LE_DIST) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Part 2. Symmetric radii: for a locally finite family of pairwise        *)
(* disjoint compact sets in real^3 there are radii d s > 0 such that the   *)
(* open d s-neighbourhoods of different members are disjoint.              *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Q_FINITE_MIN = prove
 (`!(f:A->real) c. FINITE c /\ (!q. q IN c ==> &0 < f q)
                   ==> ?d. &0 < d /\ d <= &1 /\ !q. q IN c ==> &4 * d <= f q`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `c:A->bool`] THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d ((f:A->real) a / &4)` THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:A`) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let MOI_S4Q_LF_COVER = prove
 (`!(I0:A->bool) (e:A->real^3->bool) s.
     compact (e s) /\
     (!y. y IN e s
          ==> ?u. open u /\ y IN u /\ FINITE {s' | s' IN I0 /\ ~(e s' INTER u = {})})
     ==> ?v. open v /\ e s SUBSET v /\
             FINITE {s' | s' IN I0 /\ ~(e s' INTER v = {})}`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->real^3->bool` (LABEL_TAC "u")) THEN
  UNDISCH_TAC `compact((e:A->real^3->bool) s)` THEN
  REWRITE_TAC[COMPACT_EQ_HEINE_BOREL] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (u:real^3->real^3->bool) (e(s:A))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THENL
     [USE_THEN "u" (MP_TAC o SPEC `y:real^3`) THEN ASM_SIMP_TAC[];
      EXISTS_TAC `y:real^3` THEN USE_THEN "u" (MP_TAC o SPEC `y:real^3`) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `UNIONS (IMAGE (u:real^3->real^3->bool) c)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "u" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `UNIONS (IMAGE (\y. {s' | s' IN I0 /\
                    ~((e:A->real^3->bool) s' INTER (u:real^3->real^3->bool) y = {})}) c)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "u" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `s':A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[]]);;

let MOI_S4Q_RADIUS = prove
 (`!(I0:A->bool) (e:A->real^3->bool) s.
     s IN I0 /\ (!s. s IN I0 ==> compact (e s)) /\
     (!s s'. s IN I0 /\ s' IN I0 /\ ~(s = s') ==> DISJOINT (e s) (e s')) /\
     (!y. y IN e s
          ==> ?u. open u /\ y IN u /\ FINITE {s' | s' IN I0 /\ ~(e s' INTER u = {})})
     ==> ?d. &0 < d /\
             !x y s'. x IN e s /\ dist(x,y) < &2 * d /\
                      s' IN I0 /\ ~(s' = s) /\ y IN e s'
                      ==> &2 * d <= setdist(e s,e s')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cpt")
    (CONJUNCTS_THEN2 (LABEL_TAC "dis") ASSUME_TAC))) THEN
  ASM_CASES_TAC `(e:A->real^3->bool) s = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  MP_TAC(ISPECL [`I0:A->bool`; `e:A->real^3->bool`; `s:A`] MOI_S4Q_LF_COVER) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(e:A->real^3->bool) s`; `v:real^3->bool`] MOI_S4Q_COMPACT_IN_OPEN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ee:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ee"))) THEN
  ABBREV_TAC `ff = {s' | s' IN I0 /\ ~(s' = s) /\ ~((e:A->real^3->bool) s' INTER v = {})}` THEN
  MP_TAC(ISPECL [`\s':A. setdist((e:A->real^3->bool) s,e s')`; `ff:A->bool`]
    MOI_S4Q_FINITE_MIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{s' | s' IN I0 /\ ~((e:A->real^3->bool) s' INTER v = {})}` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "ff" THEN SET_TAC[];
      EXPAND_TAC "ff" THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s':A` THEN
      STRIP_TAC THEN REWRITE_TAC[REAL_LT_LE; SETDIST_POS_LE] THEN
      CONV_TAC(RAND_CONV SYM_CONV) THEN
      SUBGOAL_THEN `compact((e:A->real^3->bool) s) /\ compact (e s')` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~((e:A->real^3->bool) s' = {})` ASSUME_TAC THENL
       [UNDISCH_TAC `~((e:A->real^3->bool) s' INTER v = {})` THEN SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(e:A->real^3->bool) s INTER e s' = {}` ASSUME_TAC THENL
       [USE_THEN "dis" (MP_TAC o SPECL [`s:A`; `s':A`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(s':A = s)` THEN MESON_TAC[];
          SIMP_TAC[DISJOINT]];
        ALL_TAC] THEN
      ASM_SIMP_TAC[SETDIST_EQ_0_COMPACT_CLOSED; COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd")))) THEN
  EXISTS_TAC `min (ee / &2) d` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`; `s':A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN v` ASSUME_TAC THENL
   [USE_THEN "ee" MATCH_MP_TAC THEN EXISTS_TAC `x:real^3` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "dd" (MP_TAC o SPEC `s':A`) THEN ANTS_TAC THENL
   [EXPAND_TAC "ff" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ASM_REAL_ARITH_TAC]);;

let MOI_S4Q_RADII = prove
 (`!(I0:A->bool) (e:A->real^3->bool).
     (!s. s IN I0 ==> compact (e s)) /\
     (!s s'. s IN I0 /\ s' IN I0 /\ ~(s = s') ==> DISJOINT (e s) (e s')) /\
     (!s y. s IN I0 /\ y IN e s
            ==> ?u. open u /\ y IN u /\ FINITE {s' | s' IN I0 /\ ~(e s' INTER u = {})})
     ==> ?d. (!s. s IN I0 ==> &0 < d s) /\
             !s s' x x' y. s IN I0 /\ s' IN I0 /\ ~(s = s') /\
                           x IN e s /\ x' IN e s' /\ dist(x,y) < d s /\ dist(x',y) < d s'
                           ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s:A. s IN I0
          ==> ?d. &0 < d /\
                  !x y s'. x IN e s /\ dist(x,y) < &2 * d /\
                           s' IN I0 /\ ~(s' = s) /\ y IN (e:A->real^3->bool) s'
                           ==> &2 * d <= setdist(e s,e s')`
  MP_TAC THENL
   [X_GEN_TAC `s:A` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S4Q_RADIUS THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:A->real` (LABEL_TAC "d")) THEN
  EXISTS_TAC `d:A->real` THEN CONJ_TAC THENL
   [X_GEN_TAC `s:A` THEN DISCH_TAC THEN
    USE_THEN "d" (MP_TAC o SPEC `s:A`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:A`; `s':A`; `x:real^3`; `x':real^3`; `y:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `dist(x:real^3,x') < (d:A->real) s + d s'` ASSUME_TAC THENL
   [UNDISCH_TAC `dist(x:real^3,y) < (d:A->real) s` THEN
    UNDISCH_TAC `dist(x':real^3,y) < (d:A->real) s'` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `(d:A->real) s' <= d s \/ d s <= d s'`) THENL
   [USE_THEN "d" (MP_TAC o SPECL [`x:real^3`; `x':real^3`; `s':A`] o
                  CONJUNCT2 o C MP (ASSUME `(s:A) IN I0`) o SPEC `s:A`) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [ASM_REAL_ARITH_TAC; UNDISCH_TAC `~(s:A = s')` THEN MESON_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(e:A->real^3->bool) s`; `(e:A->real^3->bool) s'`;
                   `x:real^3`; `x':real^3`] SETDIST_LE_DIST) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    USE_THEN "d" (MP_TAC o SPECL [`x':real^3`; `x:real^3`; `s:A`] o
                  CONJUNCT2 o C MP (ASSUME `(s':A) IN I0`) o SPEC `s':A`) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(e:A->real^3->bool) s'`; `(e:A->real^3->bool) s`;
                   `x':real^3`; `x:real^3`] SETDIST_LE_DIST) THEN
    ASM_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Part 3. Facts about the frame used for the choice of the face balls.     *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Q_FACES_MEET = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) s s'.
     lf_simplicial_complex tt /\ simplicial_subcomplex kk tt /\
     (!x y. x IN UNIONS tt /\ y IN UNIONS tt /\ h x = h y ==> x = y) /\
     s IN moi_s34_simp kk (&2) /\ s' IN moi_s34_simp kk (&2) /\ ~(s = s')
     ==> IMAGE h s INTER IMAGE h s' SUBSET IMAGE h (UNIONS (skeleton 1 kk))`,
  REWRITE_TAC[moi_s34_simp; IN_ELIM_THM; simplicial_subcomplex] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(s:real^N->bool) IN tt /\ s' IN tt` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^3) s INTER IMAGE h s' = IMAGE h (s INTER s')`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!(f:real^N->real^3) a b u.
        a SUBSET u /\ b SUBSET u /\ (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y)
        ==> IMAGE f a INTER IMAGE f b = IMAGE f (a INTER b)`) THEN
    EXISTS_TAC `UNIONS (tt:(real^N->bool)->bool)` THEN
    USE_THEN "inj" (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `!a:real^N->bool f. a IN f ==> a SUBSET UNIONS f`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC IMAGE_SUBSET THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `s':real^N->bool`] o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex (s:real^N->bool) /\ convex (s':real^N->bool)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((s:real^N->bool) INTER s' = s)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`(s:real^N->bool) INTER s'`; `s':real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
    ASM_REWRITE_TAC[INT_LT_REFL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim((s:real^N->bool) INTER s') <= &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(s:real^N->bool) INTER s'`; `s:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) INTER s' IN kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!a:real^N->bool f. a IN f ==> a SUBSET UNIONS f`) THEN
  REWRITE_TAC[skeleton; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]);;

let MOI_S4Q_AVOID_VB = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) (f1:real^N->real^3)
    (car:(real^N->bool)->real^3->bool) s.
     s IN kk /\ ~(s = {}) /\ IMAGE h s SUBSET car s /\
     (!v. {v} IN kk
          ==> IMAGE f1 (moi_s34_vb tt kk v) SUBSET car {v} /\
              pl_ball 3 (IMAGE f1 (moi_s34_vb tt kk v))) /\
     (!v q. {v} IN kk /\ q IN kk /\ ~(v IN q) ==> DISJOINT (car {v}) (IMAGE h q)) /\
     (!y. y IN UNIONS {car q | q | q IN kk /\ ~(q = {})}
          ==> ?u. open u /\ y IN u /\
                  FINITE {q | q IN kk /\ ~(q = {}) /\ ~(car q INTER u = {})})
     ==> ?w. open w /\ IMAGE h s SUBSET w /\
             !v. {v} IN kk /\ ~(v IN s)
                 ==> DISJOINT w (IMAGE f1 (moi_s34_vb tt kk v))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "vb")
      (CONJUNCTS_THEN2 (LABEL_TAC "dis") (LABEL_TAC "lf")))))) THEN
  MP_TAC(ISPECL [`IMAGE (h:real^N->real^3) s`; `{v:real^N | {v} IN kk /\ ~(v IN s)}`;
                 `\v:real^N. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`]
    MOI_S4Q_AVOID) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
      USE_THEN "vb" (MP_TAC o SPEC `v:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN ASM_MESON_TAC[MOI_S4D_PL_BALL_COMPACT];
        USE_THEN "dis" (MP_TAC o SPECL [`v:real^N`; `s:real^N->bool`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM SET_TAC[]];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "lf" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
       [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `(car:(real^N->bool)->real^3->bool) s` THEN
        CONJ_TAC THENL [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `u:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{v:real^N | {v} IN {q | q IN kk /\ ~(q = {}) /\
                                         ~((car:(real^N->bool)->real^3->bool) q INTER u = {})}}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; NOT_INSERT_EMPTY] THEN
        X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "vb" (MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 4. The theorem FBALL (MOI_S34_FBALL).                               *)
(* ------------------------------------------------------------------------- *)

let FBALL = prove
 (MOI_S34_FBALL,
  DISCH_THEN(LABEL_TAC "cnb") THEN DISCH_THEN(LABEL_TAC "l4") THEN
  MAP_EVERY X_GEN_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                       `car:(real^N->bool)->real^3->bool`] THEN
  DISCH_THEN(fun th -> LABEL_TAC "hyp" th THEN STRIP_ASSUME_TAC th) THEN
  UNDISCH_TAC `moi_s34_tube (tt:(real^N->bool)->bool) kk` THEN
  REWRITE_TAC[moi_s34_tube] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s34_emb (h:real^N->real^3) (UNIONS tt)` THEN
  REWRITE_TAC[moi_s34_emb] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")) THEN
  MP_TAC(ASSUME `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car`) THEN
  REWRITE_TAC[moi_s34_frame] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "U" (el 2 cs) THEN LABEL_TAC "car" (el 4 cs) THEN
    LABEL_TAC "vball" (el 6 cs) THEN LABEL_TAC "cardis" (el 8 cs) THEN
    LABEL_TAC "carlf" (el 11 cs)) THEN
  ABBREV_TAC `U = interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))` THEN
  SUBGOAL_THEN `open (U:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[OPEN_INTERIOR]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN moi_s34_simp kk (&2)
                  ==> s IN kk /\ ~(s = {}) /\ s IN tt /\ compact s /\
                      IMAGE (h:real^N->real^3) s SUBSET car s /\
                      compact (IMAGE h s)` (LABEL_TAC "simp") THENL
   [X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) IN tt` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `compact (s:real^N->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "car" (MP_TAC o SPEC `s:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `UNIONS (tt:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!a:real^N->bool f. a IN f ==> a SUBSET UNIONS f`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the symmetric radii *)
  MP_TAC(ISPECL [`moi_s34_simp (kk:(real^N->bool)->bool) (&2)`;
                 `\s. IMAGE (h:real^N->real^3) s DIFF U`] MOI_S4Q_RADII) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN MATCH_MP_TAC COMPACT_DIFF THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "simp" (MP_TAC o SPEC `s:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s':real^N->bool`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `s:real^N->bool`; `s':real^N->bool`]
        MOI_S4Q_FACES_MEET) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "U" MP_TAC THEN SET_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `y:real^3`] THEN STRIP_TAC THEN
      USE_THEN "simp" (MP_TAC o SPEC `s:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      USE_THEN "carlf" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
       [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        EXISTS_TAC `(car:(real^N->bool)->real^3->bool) s` THEN
        CONJ_TAC THENL [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `u:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
      USE_THEN "simp" (MP_TAC o SPEC `s':real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->real` (CONJUNCTS_THEN2
    (LABEL_TAC "dpos") (LABEL_TAC "dsep"))) THEN
  (* the sets of LEMMA4 *)
  USE_THEN "l4" (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] o
    GEN `s:real^N->bool` o
    SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
           `ep:real^N->real`; `f1:real^N->real^3`;
           `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `w4:(real^N->bool)->real^3->bool` (LABEL_TAC "w4")) THEN
  (* the sets avoiding the other vertex balls *)
  SUBGOAL_THEN
   `!s:real^N->bool. s IN moi_s34_simp kk (&2)
      ==> ?w. open w /\ IMAGE (h:real^N->real^3) s SUBSET w /\
              !v. {v} IN kk /\ ~(v IN s)
                  ==> DISJOINT w (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`
  MP_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "simp" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S4Q_AVOID_VB THEN
    EXISTS_TAC `car:(real^N->bool)->real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "vball" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `wd:(real^N->bool)->real^3->bool` (LABEL_TAC "wd")) THEN
  (* the open sets W s and the balls *)
  ABBREV_TAC
   `ww = \s:real^N->bool.
           (U UNION UNIONS (IMAGE (\x. ball(x,d s)) (IMAGE (h:real^N->real^3) s DIFF U)))
           INTER wd s INTER car s INTER w4 s` THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN moi_s34_simp kk (&2)
                  ==> open ((ww:(real^N->bool)->real^3->bool) s) /\
                      IMAGE (h:real^N->real^3) s SUBSET ww s`
  (LABEL_TAC "ww") THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN EXPAND_TAC "ww" THEN
    REWRITE_TAC[] THEN
    USE_THEN "simp" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    USE_THEN "wd" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    USE_THEN "w4" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [USE_THEN "hyp" (fun th -> ASM_REWRITE_TAC[th]); ALL_TAC] THEN
    STRIP_TAC THEN
    USE_THEN "car" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET_INTER] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; EXISTS_IN_IMAGE; IN_DIFF] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^3) IN U` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    USE_THEN "dpos" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "cnb" (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] o
    GEN `s:real^N->bool` o
    SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
           `ep:real^N->real`; `f1:real^N->real^3`;
           `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
           `(ww:(real^N->bool)->real^3->bool) s`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `cb:(real^N->bool)->real^3->bool` (LABEL_TAC "cb")) THEN
  EXISTS_TAC `cb:(real^N->bool)->real^3->bool` THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN moi_s34_simp kk (&2)
      ==> pl_ball 3 ((cb:(real^N->bool)->real^3->bool) s) /\
          IMAGE (h:real^N->real^3) s SUBSET interior (cb s) /\
          (!x. x IN moi_s34_trace tt kk f1 (cb s)
               ==> pl_crossing_at (frontier (cb s)) (IMAGE f1 (moi_s34_bd tt kk)) x) /\
          (!g x. g IN moi_s34_simp kk (&1) /\
                 x IN frontier (cb s) INTER
                      IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
                 ==> pl_curve_crossing_at (IMAGE f1 (moi_s34_bd tt kk))
                       (moi_s34_trace tt kk f1 (cb s))
                       (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) x) /\
          FINITE (components (moi_s34_trace tt kk f1 (cb s))) /\
          FINITE (frontier (cb s) INTER moi_s34_rims tt kk f1) /\
          cb s SUBSET wd s /\ cb s SUBSET car s /\ cb s SUBSET w4 s /\
          cb s SUBSET (U UNION UNIONS (IMAGE (\x. ball(x,d s)) (IMAGE h s DIFF U)))`
  (LABEL_TAC "cbs") THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "ww" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cb" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [USE_THEN "hyp" (fun th -> ASM_REWRITE_TAC[th]); STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(cb:(real^N->bool)->real^3->bool) s SUBSET ww s` THEN
    EXPAND_TAC "ww" THEN REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s34_fbinv; moi_s34_fb1; moi_s34_fb2] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "cbs" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "simp" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (h:real^N->real^3) s` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[relative_frontier] THEN
      SUBGOAL_THEN `closure (s:real^N->bool) = s` SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_CLOSED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
        SET_TAC[]];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `(cb:(real^N->bool)->real^3->bool) s` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      ASM_MESON_TAC[MOI_S4D_PL_BALL_COMPACT];
      X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
      USE_THEN "wd" (MP_TAC o SPEC `s:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^N` o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(cb:(real^N->bool)->real^3->bool) s SUBSET wd s` THEN SET_TAC[];
      USE_THEN "w4" (MP_TAC o SPEC `s:real^N->bool`) THEN
      ANTS_TAC THENL [USE_THEN "hyp" (fun th -> ASM_REWRITE_TAC[th]); ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `(cb:(real^N->bool)->real^3->bool) s` o
                 CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s':real^N->bool`] THEN STRIP_TAC THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "cbs" (MP_TAC o SPEC `s:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "cbs" (MP_TAC o SPEC `s':real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(y:real^3) IN U` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(?x. x IN IMAGE (h:real^N->real^3) s DIFF U /\ dist(x,y) < d s) /\
    (?x'. x' IN IMAGE (h:real^N->real^3) s' DIFF U /\ dist(x',y) < d s')`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(cb:(real^N->bool)->real^3->bool) s SUBSET
                   (U UNION UNIONS (IMAGE (\x. ball(x,d s)) (IMAGE h s DIFF U)))`;
      UNDISCH_TAC `(cb:(real^N->bool)->real^3->bool) s' SUBSET
                   (U UNION UNIONS (IMAGE (\x. ball(x,d s')) (IMAGE h s' DIFF U)))`] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; EXISTS_IN_IMAGE; IN_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "dsep" (MP_TAC o SPECL [`s:real^N->bool`; `s':real^N->bool`;
                                   `x:real^3`; `x':real^3`; `y:real^3`]) THEN
  MATCH_MP_TAC(TAUT `!p. p ==> ~p ==> F`) THEN
  REMOVE_THEN "dsep" (K ALL_TAC) THEN ASM_REWRITE_TAC[]);;


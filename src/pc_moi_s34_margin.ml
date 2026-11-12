(* ========================================================================= *)
(* pc_moi_s34_margin: the Sec 34 unit s34_margin.  Main theorem MARGIN :    *)
(* |- MOI_S34_MARGIN (pc_moi_s34_stmt.ml, Moise p.241, Lemma 5 (7)): for a  *)
(* 3-simplex r of kk the vertices of kk outside r lie in the unbounded      *)
(* component of the complement of a closed d-neighbourhood of h(r UNION    *)
(* the vertex balls of r).  Proof: Y, the union of the closed stars of the  *)
(* vertices of r in the first barycentric subdivision of tt, contains r    *)
(* and the vertex balls, is compact and an AR (the stars and all their      *)
(* intersections are starlike), and lies in the open stars of the vertices *)
(* of r, so it contains no other vertex; h is open on those open stars     *)
(* (invariance of domain at vertices with PL 2-sphere links), so the images *)
(* of the other vertices do not accumulate at h(Y); the complement of h(Y) *)
(* is connected (CONNECTED_COMPLEMENT_CONTRACTIBLE), and a compactness     *)
(* argument gives one d for all of them.                                    *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_s34_scella.ml";;
needs "src/pc_moi_star.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A uniform margin in real^3: if the complement of a compact k is          *)
(* connected and the closure of s misses k, one d > 0 puts every point of  *)
(* s in the outside of the closed d-neighbourhood of k (paths to a far      *)
(* point, finitely many by compactness).                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4M_FAR_OUTSIDE = prove
 (`!(z:real^3->bool) B p. z SUBSET cball(vec 0,B) /\ B < norm p
                          ==> p IN outside z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `outside(cball(vec 0:real^3,B)) SUBSET outside z` MP_TAC THENL
   [ASM_SIMP_TAC[OUTSIDE_MONO]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> s SUBSET t ==> x IN t`) THEN
  SIMP_TAC[OUTSIDE_CONVEX; CONVEX_CBALL] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC);;

let MOI_S4M_CONNECTED_OUTSIDE = prove
 (`!(z:real^3->bool) t p q.
     connected t /\ DISJOINT t z /\ p IN t /\ q IN t /\ q IN outside z
     ==> p IN outside z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[outside; IN_ELIM_THM] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3->bool) SUBSET connected_component ((:real^3) DIFF z) q`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `connected_component ((:real^3) DIFF z) p =
                connected_component ((:real^3) DIFF z) q`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN ASM SET_TAC[]);;

let MOI_S4M_FINITE_MIN = prove
 (`!(e:real^3->real) c. FINITE c /\ (!q. q IN c ==> &0 < e q)
                        ==> ?d. &0 < d /\ d <= &1 /\ !q. q IN c ==> &4 * d <= e q`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^3`; `c:real^3->bool`] THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d ((e:real^3->real) a / &4)` THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:real^3`) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let MOI_S4M_OUTSIDE_UNIFORM = prove
 (`!(k:real^3->bool) (s:real^3->bool).
     compact k /\ connected((:real^3) DIFF k) /\ DISJOINT k (closure s)
     ==> ?d. &0 < d /\
             !p. p IN s ==> p IN outside {y | ?x. x IN k /\ dist(y,x) <= d}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `k:real^3->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC] THEN
    REWRITE_TAC[REAL_LT_01; OUTSIDE_EMPTY; IN_UNIV];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bnd"))) THEN
  ABBREV_TAC `z0:real^3 = (B + &2) % basis 1` THEN
  SUBGOAL_THEN `norm(z0:real^3) = B + &2` ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `path_connected((:real^3) DIFF k)` (LABEL_TAC "pc") THENL
   [MATCH_MP_TAC CONNECTED_OPEN_PATH_CONNECTED THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ABBREV_TAC `cc = closure s INTER cball(vec 0:real^3,B + &2)` THEN
  SUBGOAL_THEN
   `!q:real^3. q IN cc
        ==> ?e g. &0 < e /\ path g /\ pathstart g = q /\ pathfinish g = z0 /\
                  !y x. y IN path_image g /\ x IN k ==> e <= dist(y,x)`
  MP_TAC THENL
   [X_GEN_TAC `q:real^3` THEN EXPAND_TAC "cc" THEN REWRITE_TAC[IN_INTER] THEN
    STRIP_TAC THEN
    USE_THEN "pc" (MP_TAC o GEN_REWRITE_RULE I [path_connected]) THEN
    DISCH_THEN(MP_TAC o SPECL [`q:real^3`; `z0:real^3`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_DIFF; IN_UNIV] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        DISCH_TAC THEN REMOVE_THEN "bnd" (MP_TAC o SPEC `z0:real^3`) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `setdist(path_image(g:real^1->real^3),k)` THEN
    EXISTS_TAC `g:real^1->real^3` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_LE; SETDIST_POS_LE] THEN
      CONV_TAC(RAND_CONV SYM_CONV) THEN
      ASM_SIMP_TAC[SETDIST_EQ_0_COMPACT_CLOSED; COMPACT_PATH_IMAGE;
                   COMPACT_IMP_CLOSED; PATH_IMAGE_NONEMPTY] THEN
      ASM SET_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SETDIST_LE_DIST THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->real`
   (X_CHOOSE_THEN `g:real^3->real^1->real^3` (LABEL_TAC "paths"))) THEN
  SUBGOAL_THEN `compact(cc:real^3->bool)` MP_TAC THENL
   [EXPAND_TAC "cc" THEN MATCH_MP_TAC CLOSED_INTER_COMPACT THEN
    REWRITE_TAC[CLOSED_CLOSURE; COMPACT_CBALL];
    ALL_TAC] THEN
  REWRITE_TAC[COMPACT_EQ_HEINE_BOREL] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\q:real^3. ball(q,e q / &2)) cc`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN EXISTS_TAC `q:real^3` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    USE_THEN "paths" (fun th -> MP_TAC(CONJUNCT1(MP (SPEC `q:real^3` th)
                                  (ASSUME `(q:real^3) IN cc`)))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`e:real^3->real`; `c:real^3->bool`] MOI_S4M_FINITE_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
    USE_THEN "paths" (MP_TAC o SPEC `q:real^3`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dmin")))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `zz = {y:real^3 | ?x. x IN k /\ dist(y,x) <= d}` THEN
  SUBGOAL_THEN `(zz:real^3->bool) SUBSET cball(vec 0,B + &1)` ASSUME_TAC THENL
   [EXPAND_TAC "zz" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL_0] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "bnd" (fun th -> MP_TAC(MP (SPEC `x:real^3` th)
                               (ASSUME `(x:real^3) IN k`))) THEN
    UNDISCH_TAC `dist(y:real^3,x) <= d` THEN UNDISCH_TAC `d <= &1` THEN
    REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `B + &1 < norm(p:real^3)` THENL
   [MATCH_MP_TAC MOI_S4M_FAR_OUTSIDE THEN EXISTS_TAC `B + &1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN cc` ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN REWRITE_TAC[IN_INTER; IN_CBALL_0] THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CLOSURE_SUBSET] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?q:real^3. q IN c /\ p IN ball(q,e q / &2)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(cc:real^3->bool) SUBSET UNIONS (IMAGE (\q. ball(q,e q / &2)) c)` THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3) IN cc` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "paths" (MP_TAC o SPEC `q:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far"))))) THEN
  USE_THEN "dmin" (MP_TAC o SPEC `q:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(q:real^3) IN path_image((g:real^3->real^1->real^3) q) /\
                (z0:real^3) IN path_image(g q)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4M_CONNECTED_OUTSIDE THEN
  MAP_EVERY EXISTS_TAC
   [`segment[p:real^3,q] UNION path_image((g:real^3->real^1->real^3) q)`;
    `z0:real^3`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN
    ASM_SIMP_TAC[CONNECTED_SEGMENT; CONNECTED_PATH_IMAGE] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `q:real^3` THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    EXPAND_TAC "zz" THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNION;
      NOT_IN_EMPTY; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[TAUT `~((a \/ b) /\ c) <=> (c ==> ~a /\ ~b)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(e:real^3->real) q <= dist(q:real^3,x)` MP_TAC THENL
       [USE_THEN "far" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `y:real^3`] DIST_IN_CLOSED_SEGMENT) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(p:real^3) IN ball(q,e q / &2)` THEN
      UNDISCH_TAC `dist(y:real^3,x) <= d` THEN
      UNDISCH_TAC `&4 * d <= (e:real^3->real) q` THEN
      REWRITE_TAC[IN_BALL] THEN CONV_TAC NORM_ARITH;
      DISCH_TAC THEN
      SUBGOAL_THEN `(e:real^3->real) q <= dist(y:real^3,x)` MP_TAC THENL
       [USE_THEN "far" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `dist(y:real^3,x) <= d` THEN
      UNDISCH_TAC `&4 * d <= (e:real^3->real) q` THEN
      UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC];
    REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT];
    ASM_REWRITE_TAC[IN_UNION];
    MATCH_MP_TAC MOI_S4M_FAR_OUTSIDE THEN EXISTS_TAC `B + &1` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Closed stars of vertices in the first barycentric subdivision:           *)
(* they lie in the open stars (in t) of their vertices, contain no other   *)
(* vertex, are compact, and those of the vertices of a simplex cover it.   *)
(* ------------------------------------------------------------------------- *)

let moi_s4m_st = new_definition
 `moi_s4m_st (t:(real^N->bool)->bool) (v:real^N) =
    UNIONS {s | s IN barycentric_subdivision t /\ v IN s}`;;

let MOI_S4M_EXTREME_IN = prove
 (`!x s:real^N->bool. x extreme_point_of s ==> x IN s`,
  SIMP_TAC[extreme_point_of]);;

let MOI_S4M_IN_ST = prove
 (`!(t:(real^N->bool)->bool) v x.
     lf_simplicial_complex t /\ {v} IN t
     ==> (x IN moi_s4m_st t v <=>
          ?h. moi_bar_chain t h /\ {v} IN h /\
              x IN convex hull (IMAGE simplex_barycentre h))`,
  SIMP_TAC[moi_s4m_st; MOI_FTA_IN_STAR1]);;

let MOI_S4M_ST_OPEN_STAR = prove
 (`!(t:(real^N->bool)->bool) v.
     lf_simplicial_complex t /\ {v} IN t
     ==> moi_s4m_st t v SUBSET moi_sta_open_star t v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  ASM_SIMP_TAC[MOI_S4M_IN_ST] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `f:(real^N->bool)->bool`; `x:real^N`]
    MOI_BAR_CHAIN_HULL_RI) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain (t:(real^N->bool)->bool) g` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `x IN relative_interior (convex hull (IMAGE simplex_barycentre
                                          (g:(real^N->bool)->bool)))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; RELATIVE_INTERIOR_EMPTY;
                    NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `g:(real^N->bool)->bool`; `x:real^N`]
    MOI_BAR_CHAIN_RI_MAX) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `m = UNIONS (g:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `(m:real^N->bool) IN t /\ (v:real^N) IN m` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_bar_chain]) THEN ASM SET_TAC[];
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                     `v:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN m` ASSUME_TAC THENL
   [ASM_MESON_TAC[REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^N->bool) INTER m = m` MP_TAC THENL
   [MATCH_MP_TAC MOI_FTA_FACE_RI THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    ASM_MESON_TAC[];
    ASM SET_TAC[]]);;

let MOI_S4M_OPEN_STAR_VERTEX = prove
 (`!(t:(real^N->bool)->bool) v w.
     {w} IN t /\ w IN moi_sta_open_star t v ==> w = v`,
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{w:real^N}`) THEN
  ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[]);;

let MOI_S4M_ST_FINITE = prove
 (`!(t:(real^N->bool)->bool) v.
     lf_simplicial_complex t /\ {v} IN t
     ==> FINITE {s | s IN barycentric_subdivision t /\ v IN s}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision (t:(real^N->bool)->bool)) /\
                UNIONS (barycentric_subdivision t) = UNIONS t`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FTA_BS_FACTS]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `v:real^N` o last o CONJUNCTS o
    GEN_REWRITE_RULE I [lf_simplicial_complex] o
    check (fun th -> concl th = `lf_simplicial_complex
                                   (barycentric_subdivision (t:(real^N->bool)->bool))`)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
  ASM SET_TAC[]);;

let MOI_S4M_ST_COMPACT = prove
 (`!(t:(real^N->bool)->bool) v.
     lf_simplicial_complex t /\ {v} IN t ==> compact (moi_s4m_st t v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s4m_st] THEN
  MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[MOI_S4M_ST_FINITE] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision (t:(real^N->bool)->bool))`
  MP_TAC THENL [ASM_MESON_TAC[MOI_FTA_BS_FACTS]; ALL_TAC] THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
  ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]);;

let MOI_S4M_SIMPLEX_IN_STS = prove
 (`!(t:(real^N->bool)->bool) r.
     lf_simplicial_complex t /\ r IN t
     ==> r SUBSET UNIONS {moi_s4m_st t v | v | v IN r /\ {v} IN t}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:int`; `r:real^N->bool`; `x:real^N`] MOI_BAR_SIMPLEX_COVERED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(f:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `x IN convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{u:real^N->bool | u face_of r}`; `f:(real^N->bool)->bool`]
    MOI_FTA_CHAIN_MIN) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `m0 = INTERS (f:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `(m0:real^N->bool) face_of r /\ ~(m0 = {})` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_bar_chain]) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (m0:real^N->bool) /\ convex m0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_COMPACT; FACE_OF_IMP_CONVEX; SIMPLEX_IMP_COMPACT;
                  SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  MP_TAC(ISPEC `m0:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real^N`) THEN
  SUBGOAL_THEN `(v:real^N) extreme_point_of r /\ v IN m0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[EXTREME_POINT_OF_FACE; MOI_S4M_EXTREME_IN]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN t` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    ASM_MESON_TAC[FACE_OF_SING];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
  EXISTS_TAC `moi_s4m_st t (v:real^N)` THEN EXISTS_TAC `v:real^N` THEN
  REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MOI_S4M_EXTREME_IN]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S4M_IN_ST] THEN
  EXISTS_TAC `{v:real^N} INSERT f` THEN REWRITE_TAC[IN_INSERT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
      EXISTS_TAC `{u:real^N->bool | u face_of r}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
      ASM_MESON_TAC[];
      X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN DISJ1_TAC THEN
      REWRITE_TAC[SING_SUBSET] THEN ASM SET_TAC[]];
    MATCH_MP_TAC(SET_RULE `!s t (x:real^N). x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The union Y of the stars of the vertices of a simplex r is an AR:        *)
(* the intersection of the stars of a nonempty set G of vertices of r is a *)
(* finite union of simplices of the subdivision, each containing the       *)
(* barycentre of the face hull G (so it is starlike and an ANR), and the   *)
(* unions are assembled by AR_CLOSED_UNION (induction on the vertex set).  *)
(* ------------------------------------------------------------------------- *)

let MOI_S4M_FACE_HULL_IN = prove
 (`!(t:(real^N->bool)->bool) r G.
     lf_simplicial_complex t /\ r IN t /\
     G SUBSET {v | v IN r /\ {v} IN t}
     ==> convex hull G IN t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(G:real^N->bool) SUBSET c` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^N) IN r /\ {v} IN t` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^N) extreme_point_of r` MP_TAC THENL
     [MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN
      EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_SIMP_TAC[MOI_FTA_LF_BAR];
      ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  EXISTS_TAC `G:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S4M_HULL_FACTS = prove
 (`!(t:(real^N->bool)->bool) G g.
     lf_simplicial_complex t /\ g IN t /\ g = convex hull G /\ ~(G = {})
     ==> ~(g = {}) /\ (!v. v IN G ==> v IN g) /\
         (!s. s IN t /\ (!v. v IN G ==> v IN s) ==> g SUBSET s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN
  CONJ_TAC THENL [SIMP_TAC[HULL_INC]; ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX]);;

let MOI_S4M_STS_INTER_SUB = prove
 (`!(t:(real^N->bool)->bool) G g.
     lf_simplicial_complex t /\ g IN t /\ g = convex hull G /\ ~(G = {}) /\
     (!v. v IN G ==> {v} IN t)
     ==> INTERS (IMAGE (moi_s4m_st t) G) SUBSET
         UNIONS {convex hull (IMAGE simplex_barycentre h) | h |
                 moi_bar_chain t h /\ g IN h /\ !s. s IN h ==> g SUBSET s}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4M_HULL_FACTS o
    (fun th -> CONJ (CONJUNCT1 th) (CONJ (CONJUNCT1(CONJUNCT2 th))
      (CONJ (CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))
            (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ving") (LABEL_TAC "hullmin"))) THEN
  FIRST_X_ASSUM(fun th -> if is_conj (concl th)
    then REPEAT_TCL CONJUNCTS_THEN
           (fun c -> if is_eq (concl c) then ALL_TAC else ASSUME_TAC c) th
    else failwith "not the hypothesis") THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  REWRITE_TAC[INTERS_IMAGE] THEN GEN_REWRITE_TAC I [SUBSET] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(LABEL_TAC "all") THEN
  SUBGOAL_THEN `!v:real^N. v IN G ==> ?h. moi_bar_chain t h /\ {v} IN h /\
                    x IN convex hull (IMAGE simplex_barycentre h)`
  (LABEL_TAC "allh") THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`; `x:real^N`]
      MOI_S4M_IN_ST) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN USE_THEN "all" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(G:real^N->bool = {})`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `v0:real^N`) THEN
  USE_THEN "allh" (MP_TAC o SPEC `v0:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `f0:(real^N->bool)->bool`; `x:real^N`]
    MOI_BAR_CHAIN_HULL_RI) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain (t:(real^N->bool)->bool) g0` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!v s:real^N->bool. v IN G /\ s IN g0 ==> v IN s` ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`v:real^N`; `s:real^N->bool`] THEN STRIP_TAC THEN
    USE_THEN "allh" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `f:(real^N->bool)->bool`; `x:real^N`]
      MOI_BAR_CHAIN_HULL_RI) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g1:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `g1:(real^N->bool)->bool = g0` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_RI_UNIQUE THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `x:real^N`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_BAR_CHAIN_SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `v:real^N`] MOI_FTA_CHAIN_VERTEX_ALL) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN g0 ==> g SUBSET s` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "hullmin" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                 ((g:real^N->bool) INSERT g0))` THEN
  EXISTS_TAC `(g:real^N->bool) INSERT g0` THEN
  SUBGOAL_THEN `moi_bar_chain (t:(real^N->bool)->bool) (g INSERT g0)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!s t (x:real^N). x IN s /\ s SUBSET t ==> x IN t`) THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre (g0:(real^N->bool)->bool))` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET];
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

let MOI_S4M_STS_INTER_SUP = prove
 (`!(t:(real^N->bool)->bool) G g.
     lf_simplicial_complex t /\ g IN t /\ g = convex hull G /\ ~(G = {}) /\
     (!v. v IN G ==> {v} IN t)
     ==> UNIONS {convex hull (IMAGE simplex_barycentre h) | h |
                 moi_bar_chain t h /\ g IN h /\ !s. s IN h ==> g SUBSET s}
         SUBSET INTERS (IMAGE (moi_s4m_st t) G)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4M_HULL_FACTS o
    (fun th -> CONJ (CONJUNCT1 th) (CONJ (CONJUNCT1(CONJUNCT2 th))
      (CONJ (CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))
            (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ving") (LABEL_TAC "hullmin"))) THEN
  FIRST_X_ASSUM(fun th -> if is_conj (concl th)
    then REPEAT_TCL CONJUNCTS_THEN
           (fun c -> if is_eq (concl c) then ALL_TAC else ASSUME_TAC c) th
    else failwith "not the hypothesis") THEN
  GEN_REWRITE_TAC I [SUBSET] THEN
  REWRITE_TAC[FORALL_IN_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `h:(real^N->bool)->bool` THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[INTERS_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `{v:real^N} IN t` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S4M_IN_ST] THEN
  SUBGOAL_THEN `{v:real^N} SUBSET g` ASSUME_TAC THENL
   [REWRITE_TAC[SING_SUBSET] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `{v:real^N} INSERT h` THEN REWRITE_TAC[IN_INSERT] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN ASM_MESON_TAC[SUBSET_TRANS];
    MATCH_MP_TAC(SET_RULE `!s t (x:real^N). x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                              (h:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

let MOI_S4M_STS_INTER_EQ = prove
 (`!(t:(real^N->bool)->bool) G g.
     lf_simplicial_complex t /\ g IN t /\ g = convex hull G /\ ~(G = {}) /\
     (!v. v IN G ==> {v} IN t)
     ==> INTERS (IMAGE (moi_s4m_st t) G) =
         UNIONS {convex hull (IMAGE simplex_barycentre h) | h |
                 moi_bar_chain t h /\ g IN h /\ !s. s IN h ==> g SUBSET s}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4M_STS_INTER_SUB; MATCH_MP_TAC MOI_S4M_STS_INTER_SUP] THEN
  FIRST_ASSUM ACCEPT_TAC);;

let MOI_S4M_ST_CHAINS_FINITE = prove
 (`!(t:(real^N->bool)->bool) v.
     lf_simplicial_complex t /\ {v} IN t
     ==> FINITE {h | moi_bar_chain t h /\ !s. s IN h ==> v IN s}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `v:real^N` o last o CONJUNCTS o
    GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[IN_SING]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{h | h SUBSET {s:real^N->bool | s IN t /\ ~(s INTER u = {})}}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_bar_chain] THEN ASM SET_TAC[]);;

let MOI_S4M_STS_INTER_AR = prove
 (`!(t:(real^N->bool)->bool) G g.
     lf_simplicial_complex t /\ g IN t /\ g = convex hull G /\ ~(G = {}) /\
     (!v. v IN G ==> {v} IN t)
     ==> AR (INTERS (IMAGE (moi_s4m_st t) G))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_S4M_STS_INTER_EQ) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4M_HULL_FACTS o
    (fun th -> CONJ (CONJUNCT1 th) (CONJ (CONJUNCT1(CONJUNCT2 th))
      (CONJ (CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))
            (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ving") (LABEL_TAC "hullmin"))) THEN
  FIRST_X_ASSUM(fun th -> if is_conj (concl th)
    then REPEAT_TCL CONJUNCTS_THEN
           (fun c -> if is_eq (concl c) then ALL_TAC else ASSUME_TAC c) th
    else failwith "not the hypothesis") THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(G:real^N->bool = {})`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `v0:real^N`) THEN
  SUBGOAL_THEN `(v0:real^N) IN g` ASSUME_TAC THENL
   [USE_THEN "ving" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[AR_ANR] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ANR_FINITE_UNIONS_CONVEX_CLOSED THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{h | moi_bar_chain t h /\ !s:real^N->bool. s IN h ==> v0 IN s}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S4M_ST_CHAINS_FINITE THEN ASM_SIMP_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `h:(real^N->bool)->bool` THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `h:(real^N->bool)->bool` THEN
      STRIP_TAC THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      MATCH_MP_TAC FINITE_IMP_COMPACT THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_MESON_TAC[moi_bar_chain]];
    MATCH_MP_TAC STARLIKE_IMP_CONTRACTIBLE THEN REWRITE_TAC[starlike] THEN
    EXISTS_TAC `simplex_barycentre (g:real^N->bool)` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre {g:real^N->bool})` THEN
      EXISTS_TAC `{g:real^N->bool}` THEN
      ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; IN_SING; SUBSET_REFL] THEN
      REWRITE_TAC[MOI_FTA_HULL_SING_CHAIN; IN_SING];
      REWRITE_TAC[FORALL_IN_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                  FORALL_IN_GSPEC] THEN
      X_GEN_TAC `h:(real^N->bool)->bool` THEN REPEAT DISCH_TAC THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE `!s t (f:(real^N->bool)->bool).
                               s SUBSET t /\ t IN f ==> s SUBSET UNIONS f`) THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre (h:(real^N->bool)->bool))` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[CONVEX_CONTAINS_SEGMENT_IMP; CONVEX_CONVEX_HULL] THEN
        MATCH_MP_TAC HULL_INC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `h:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[]]];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `simplex_barycentre (g:real^N->bool)` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre {g:real^N->bool})` THEN
    EXISTS_TAC `{g:real^N->bool}` THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; IN_SING; SUBSET_REFL] THEN
    REWRITE_TAC[MOI_FTA_HULL_SING_CHAIN; IN_SING]]);;

let MOI_S4M_STS_FACTS = prove
 (`!(t:(real^N->bool)->bool) r G.
     lf_simplicial_complex t /\ r IN t /\
     G SUBSET {v | v IN r /\ {v} IN t} /\ ~(G = {})
     ==> compact (INTERS (IMAGE (moi_s4m_st t) G)) /\
         AR (INTERS (IMAGE (moi_s4m_st t) G))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_INTERS THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S4M_ST_COMPACT THEN
    ASM SET_TAC[];
    MATCH_MP_TAC MOI_S4M_STS_INTER_AR THEN
    EXISTS_TAC `convex hull (G:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4M_FACE_HULL_IN THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]]]);;

let MOI_S4M_STS_UNION_AR = prove
 (`!(t:(real^N->bool)->bool) r.
     lf_simplicial_complex t /\ r IN t
     ==> !ff. FINITE ff
              ==> ff SUBSET {v | v IN r /\ {v} IN t} /\ ~(ff = {})
                  ==> !H. H SUBSET {v | v IN r /\ {v} IN t}
                          ==> AR (UNIONS (IMAGE (\v. INTERS (IMAGE (moi_s4m_st t)
                                                                (v INSERT H))) ff))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `ff:real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET; NOT_INSERT_EMPTY] THEN STRIP_TAC THEN
  X_GEN_TAC `H:real^N->bool` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [IMAGE_CLAUSES] THEN
  REWRITE_TAC[UNIONS_INSERT] THEN BETA_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `r:real^N->bool`;
                 `(a:real^N) INSERT H`] MOI_S4M_STS_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[INSERT_SUBSET; NOT_INSERT_EMPTY]; ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `ff:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[CONJUNCT1 IMAGE_CLAUSES; UNIONS_0; UNION_EMPTY]; ALL_TAC] THEN
  MATCH_MP_TAC AR_CLOSED_UNION THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `r:real^N->bool`;
                   `(v:real^N) INSERT H`] MOI_S4M_STS_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INSERT_SUBSET; NOT_INSERT_EMPTY] THEN ASM SET_TAC[];
                    SIMP_TAC[]];
    ASM_REWRITE_TAC[];
    USE_THEN "ih" (MP_TAC o SPEC `H:real^N->bool` o
      C MP (CONJ (ASSUME `(ff:real^N->bool) SUBSET {v | v IN r /\ {v} IN t}`)
                 (ASSUME `~(ff:real^N->bool = {})`))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    SUBGOAL_THEN
     `INTERS (IMAGE (moi_s4m_st t) ((a:real^N) INSERT H)) INTER
      UNIONS (IMAGE (\v. INTERS (IMAGE (moi_s4m_st t) (v INSERT H))) ff) =
      UNIONS (IMAGE (\v. INTERS (IMAGE (moi_s4m_st t) (v INSERT a INSERT H))) ff)`
    SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_CLAUSES; INTERS_INSERT] THEN SET_TAC[]; ALL_TAC] THEN
    USE_THEN "ih" (MP_TAC o SPEC `(a:real^N) INSERT H` o
      C MP (CONJ (ASSUME `(ff:real^N->bool) SUBSET {v | v IN r /\ {v} IN t}`)
                 (ASSUME `~(ff:real^N->bool = {})`))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INSERT_SUBSET]; DISCH_THEN ACCEPT_TAC]]);;

let MOI_S4M_Y_FACTS = prove
 (`!(t:(real^N->bool)->bool) r.
     lf_simplicial_complex t /\ r IN t /\ ~(r = {})
     ==> compact (UNIONS {moi_s4m_st t v | v | v IN r /\ {v} IN t}) /\
         AR (UNIONS {moi_s4m_st t v | v | v IN r /\ {v} IN t})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {v:real^N | v IN r /\ {v} IN t} /\
                ~({v:real^N | v IN r /\ {v} IN t} = {})` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `{v:real^N | v IN r /\ {v} IN t} = c` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `v:real^N` THEN
      EQ_TAC THENL
       [STRIP_TAC THEN
        SUBGOAL_THEN `(v:real^N) extreme_point_of r` MP_TAC THENL
         [MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN
          EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_SIMP_TAC[MOI_FTA_LF_BAR];
          ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]];
        DISCH_TAC THEN
        SUBGOAL_THEN `(v:real^N) extreme_point_of r` ASSUME_TAC THENL
         [ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[MOI_S4M_EXTREME_IN]; ALL_TAC] THEN
        ASM_MESON_TAC[FACE_OF_SING]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE];
      DISCH_TAC THEN UNDISCH_TAC `~(r:real^N->bool = {})` THEN
      ASM_REWRITE_TAC[CONVEX_HULL_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {moi_s4m_st t v | v | v IN r /\ {v} IN t} =
                UNIONS (IMAGE (\v:real^N. INTERS (IMAGE (moi_s4m_st t) (v INSERT {})))
                              {v | v IN r /\ {v} IN t})`
  SUBST1_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES; INTERS_1] THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM; IMAGE_CLAUSES; INTERS_1] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4M_ST_COMPACT THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `r:real^N->bool`] MOI_S4M_STS_UNION_AR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `{v:real^N | v IN r /\ {v} IN t}`) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN DISCH_THEN(MP_TAC o SPEC `{}:real^N->bool`) THEN
    REWRITE_TAC[EMPTY_SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* Invariance of domain at a vertex with a PL 2-sphere link: an             *)
(* injective continuous map into real^3 sends the open star to an open set *)
(* (the closed star is a cone PL homeomorphic to a 3-simplex, the open star *)
(* corresponds to its interior; MOI_FTA_STAR_CHART).                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S4M_OPEN_STAR_IMAGE = prove
 (`!(t:(real^N->bool)->bool) (h:real^N->real^3) v.
     lf_simplicial_complex t /\ {v} IN t /\
     pl_sphere 2 (UNIONS (simplicial_link t v)) /\
     h continuous_on UNIONS t /\
     (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y)
     ==> open (IMAGE h (moi_sta_open_star t v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_STAR_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `p:real^N->real^3`
    (X_CHOOSE_THEN `q:real^3->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "plh") (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))))))) THEN
  SUBGOAL_THEN
   `moi_sta_open_star t (v:real^N) =
    UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link t v)} DIFF
    UNIONS (simplicial_link t v)` SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_STA_OPEN_STAR_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {segment[v:real^N,y] | y | y IN UNIONS (simplicial_link t v)} SUBSET
    UNIONS t` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`] MOI_FTA_STAR_EQ_CONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (simplicial_link t (v:real^N)) SUBSET
    UNIONS {segment[v,y] | y | y IN UNIONS (simplicial_link t v)}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN EXISTS_TAC `segment[v:real^N,y]` THEN
    REWRITE_TAC[ENDS_IN_SEGMENT] THEN EXISTS_TAC `y:real^N` THEN
    ASM_REWRITE_TAC[IN_UNIONS];
    ALL_TAC] THEN
  REMOVE_THEN "plh" (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `interior (S:real^3->bool) = S DIFF relative_frontier S`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `affine hull (S:real^3->bool) = (:real^3)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN
      MATCH_MP_TAC AFF_DIM_SIMPLEX THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[relative_frontier; RELATIVE_INTERIOR_INTERIOR] THEN
    SUBGOAL_THEN `closure (S:real^3->bool) = S` SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC SIMPLEX_IMP_CLOSED THEN
      EXISTS_TAC `&3:int` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `S:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `L = UNIONS (simplicial_link (t:(real^N->bool)->bool) v)` THEN
  ABBREV_TAC `K = UNIONS {segment[v:real^N,y] | y | y IN L}` THEN
  SUBGOAL_THEN `(K:real^N->bool) DIFF L = IMAGE (q:real^3->real^N) (interior S)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (p:real^N->real^3) L = relative_frontier S` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE
     `!(p:real^N->real^3) q kk ll ss.
        (!x. x IN kk ==> q (p x) = x) /\ IMAGE p kk = ss /\
        (!y. y IN ss ==> p (q y) = y) /\ IMAGE q ss = kk /\ ll SUBSET kk
        ==> kk DIFF ll = IMAGE q (ss DIFF IMAGE p ll)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN
  REWRITE_TAC[OPEN_INTERIOR] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^3->bool` THEN
      ASM_REWRITE_TAC[INTERIOR_SUBSET];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `UNIONS (t:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `S:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN REWRITE_TAC[o_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN S /\ (y:real^3) IN S` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `S:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^3->real^N) x = q y` MP_TAC THENL
     [UNDISCH_TAC `!x y. x IN UNIONS (t:(real^N->bool)->bool) /\ y IN UNIONS t /\
                         (h:real^N->real^3) x = h y ==> x = y` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(p:real^N->real^3) (q (x:real^3)) = p (q y)` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem MARGIN (MOI_S34_MARGIN).                                *)
(* ------------------------------------------------------------------------- *)

let MOI_S4M_IMAGE_STAR_AVOID = prove
 (`!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3) r v.
     kk SUBSET tt /\ v IN r /\
     (!x y. x IN UNIONS tt /\ y IN UNIONS tt /\ h x = h y ==> x = y)
     ==> IMAGE h (moi_sta_open_star tt v) INTER
         {h w | w | {w} IN kk /\ ~(w IN r)} = {}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj"))) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `y:real^3 = h (z:real^N)`)) THEN
  SUBGOAL_THEN `{w:real^N} IN tt` ASSUME_TAC THENL
   [UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) = z` SUBST_ALL_TAC THENL
   [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^N}` THEN
      ASM_REWRITE_TAC[IN_SING];
      UNDISCH_TAC `(z:real^N) IN moi_sta_open_star tt v` THEN
      REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) = v` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOI_S4M_OPEN_STAR_VERTEX THEN
    EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `~((v:real^N) IN r)` THEN ASM_REWRITE_TAC[]]);;

let MARGIN = prove
 (MOI_S34_MARGIN,
  REWRITE_TAC[moi_s34_tube; moi_s34_emb; moi_s34_simp; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `r:real^N->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(kk:(real^N->bool)->bool) SUBSET tt /\
                (!s f. s IN kk /\ f face_of s ==> f IN kk)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->bool) IN tt /\ ~(r = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM SET_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(r:real^N->bool) = &3` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. v IN r /\ {v} IN tt
                           ==> {v} IN kk /\ pl_sphere 2 (UNIONS (simplicial_link tt v))`
  (LABEL_TAC "verts") THENL
   [X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `{v:real^N} IN kk` ASSUME_TAC THENL
     [SUBGOAL_THEN `(v:real^N) extreme_point_of r` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN
        EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_SIMP_TAC[MOI_FTA_LF_BAR];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!s f. s IN (kk:(real^N->bool)->bool) /\ f face_of s
                                  ==> f IN kk`) (concl th))) THEN
      EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `graph_in_complex (tt:(real^N->bool)->bool) (skeleton 1 kk)` THEN
    REWRITE_TAC[graph_in_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Y = UNIONS {moi_s4m_st tt v | v | (v:real^N) IN r /\ {v} IN tt}` THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `r:real^N->bool`] MOI_S4M_Y_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `r UNION moi_s34_ft tt kk r SUBSET (Y:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4M_SIMPLEX_IN_STS THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_s34_ft; moi_s34_vb; derived_dual_cell; GSYM moi_s4m_st] THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      EXISTS_TAC `moi_s4m_st tt (v:real^N)` THEN CONJ_TAC THENL
       [EXISTS_TAC `v:real^N` THEN ASM SET_TAC[];
        UNDISCH_TAC `(x:real^N) IN c` THEN ASM_REWRITE_TAC[IN_INTER] THEN
        SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN Y
                ==> ?v. v IN r /\ {v} IN tt /\ x IN moi_sta_open_star tt v`
  (LABEL_TAC "ycov") THENL
   [EXPAND_TAC "Y" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v:real^N`] MOI_S4M_ST_OPEN_STAR) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:real^N->bool) SUBSET UNIONS tt` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "ycov" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (h:real^N->real^3) Y) /\
                connected ((:real^3) DIFF IMAGE h Y)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^N->real^3) continuous_on Y` ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `UNIONS (tt:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `compact (IMAGE (h:real^N->real^3) Y)` ASSUME_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_COMPLEMENT_CONTRACTIBLE THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    MP_TAC(ISPECL [`Y:real^N->bool`; `IMAGE (h:real^N->real^3) Y`]
      HOMEOMORPHIC_CONTRACTIBLE) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[AR_IMP_CONTRACTIBLE] THEN
    REWRITE_TAC[homeomorphic] THEN EXISTS_TAC `h:real^N->real^3` THEN
    MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!x y. x IN UNIONS (tt:(real^N->bool)->bool) /\ y IN UNIONS tt /\
                       (h:real^N->real^3) x = h y ==> x = y` THEN
    UNDISCH_TAC `(Y:real^N->bool) SUBSET UNIONS tt` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `S = {(h:real^N->real^3) w | w | {w} IN kk /\ ~(w IN r)}` THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (h:real^N->real^3) Y) (closure S)` ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `!f:real^N->real^3 s t.
                   DISJOINT (IMAGE f s) t <=> !x. x IN s ==> ~(f x IN t)`] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "ycov" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    USE_THEN "verts" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `h:real^N->real^3`; `v:real^N`]
      MOI_S4M_OPEN_STAR_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `r:real^N->bool`; `v:real^N`]
      MOI_S4M_IMAGE_STAR_AVOID) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (h:real^N->real^3) (moi_sta_open_star tt v)`;
                   `S:real^3->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN moi_sta_open_star tt v` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (h:real^N->real^3) Y`; `S:real^3->bool`]
    MOI_S4M_OUTSIDE_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unif"))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!a s t:real^3->bool. a IN s /\ s SUBSET t ==> a IN t`) THEN
  EXISTS_TAC `outside {y | ?x. x IN IMAGE (h:real^N->real^3) Y /\ dist(y,x) <= d}` THEN
  CONJ_TAC THENL
   [USE_THEN "unif" MATCH_MP_TAC THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC OUTSIDE_MONO THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(h:real^N->real^3) x` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]]);;


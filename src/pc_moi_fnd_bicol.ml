(* ========================================================================= *)
(* pc_moi_fnd_bicol: bicollars of two-sided closed surfaces in the interior *)
(* of a combinatorial 3-manifold with boundary, inside any given relative   *)
(* neighbourhood (Moise GTM 47, 26.3, p.192), and in real^3 from the        *)
(* corrected 26.6.  Main theorems (terms of pc_moi_fnd_stmt.ml):             *)
(*   SURFACE_BICOLLAR    : |- MOI_FND_BICOLLAR                               *)
(*   SURFACE_BICOLLAR_R3 : |- MOI_FND_BICOLLAR_R3                            *)
(* Route (DG Bicollar.lean:103): simultaneous subdivision (s need not be a  *)
(* subcomplex of c); one component of the surface at a time; a fine second *)
(* derived neighbourhood N of the component; the closures A, B of the two   *)
(* components of N minus S are combinatorial 3-manifolds with boundary     *)
(* (2D Schoenflies MOI_S4O_SPHERE_PIECE at the vertices of S) and S is a    *)
(* union of components of their boundaries; BOUNDARY_COLLAR of A and of B   *)
(* restricted to S x [0,1], glued along S x 0.                               *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_collar.ml";;
needs "src/pc_moi_fnd_cm2.ml";;
needs "src/pc_moi_s28_trib.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Generic tools.  PL 2-spheres are topological 2-spheres; purity of PL      *)
(* 2-sphere and 2-ball complexes and of combinatorial 3-manifolds with       *)
(* boundary; restriction of a collar to a union of components of the         *)
(* collared set; two collars glued into a bicollar; interiors in nested      *)
(* subspaces.                                                                *)
(* ========================================================================= *)

(* A PL 2-sphere is homeomorphic to the round 2-sphere (the proof of         *)
(* MOI_S4L_SPHERE2_HOMEO of pc_moi_s34_tinf, which is not in this closure).  *)

let MOI_FBC_SPHERE2_HOMEO = prove
 (`!s:real^N->bool. pl_sphere 2 s ==> s homeomorphic sphere(vec 0:real^3,&1)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN
  EXISTS_TAC `relative_frontier k:real^N->bool` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `sphere(vec 0:real^3,&1) = relative_frontier(cball(vec 0,&1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[RELATIVE_FRONTIER_CBALL; REAL_OF_NUM_EQ; ARITH_EQ];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
    REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL; DIMINDEX_3;
                REAL_LT_01] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT;
                  COMPACT_IMP_BOUNDED; AFF_DIM_SIMPLEX]]);;

(* PL 2-spheres and 2-balls are nonempty.                                    *)

let MOI_FBC_SPHERE_BALL_NONEMPTY = prove
 (`!x:real^N->bool. pl_sphere 2 x \/ pl_ball 2 x ==> ~(x = {})`,
  GEN_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_FBC_SPHERE2_HOMEO) THEN
    DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `({}:real^N->bool) homeomorphic sphere(vec 0:real^3,&1)` THEN
    REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_ball]) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `k:real^N->bool = {}` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
    UNDISCH_TAC `&2 simplex ({}:real^N->bool)` THEN
    REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC]);;

(* Purity of finite complexes triangulating a PL 2-sphere or 2-ball.         *)

let MOI_FBC_LINK_PURE = prove
 (`!(L:(real^N->bool)->bool) s.
     simplicial_complex L /\
     (pl_sphere 2 (UNIONS L) \/ pl_ball 2 (UNIONS L)) /\
     s IN L /\ ~(s = {})
     ==> ?t. t IN L /\ aff_dim t = &2 /\ s SUBSET t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC MOI_SCF_SURF_PURE THEN ASM_SIMP_TAC[MOI_FBC_SPHERE2_HOMEO];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_ball]) THEN
    REWRITE_TAC[pl_homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC MOI_FM3_DISK_PURE THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `g:real^N->real^N`; `f:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[]]);;

(* Purity of finite combinatorial 3-manifolds with boundary.                *)

let MOI_FBC_CMWB3_PURE = prove
 (`!(c:(real^N->bool)->bool) s.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ s IN c /\ ~(s = {})
     ==> ?r. r IN c /\ aff_dim r = &3 /\ s SUBSET r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool) /\ simplicial_complex c`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o
      GEN_REWRITE_RULE I [combinatorial_manifold_with_boundary]) THEN
    ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_SC_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `pl_sphere 2 (UNIONS (simplicial_link c (v:real^N))) \/
                pl_ball 2 (UNIONS (simplicial_link c v))` ASSUME_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (simplicial_link c (v:real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LINK_SC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN
   `?t0:real^N->bool. t0 IN simplicial_link c v /\ aff_dim t0 = &2 /\ s0 SUBSET t0`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `s0:real^N->bool = {}` THENL
     [SUBGOAL_THEN `?s1:real^N->bool. s1 IN simplicial_link c v /\ ~(s1 = {})`
      STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        SUBGOAL_THEN `UNIONS (simplicial_link c (v:real^N)) = {}` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPEC `UNIONS (simplicial_link c (v:real^N))`
          MOI_FBC_SPHERE_BALL_NONEMPTY) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `s1:real^N->bool`]
        MOI_FBC_LINK_PURE) THEN
      ASM_REWRITE_TAC[EMPTY_SUBSET] THEN MESON_TAC[];
      MATCH_MP_TAC MOI_FBC_LINK_PURE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t0:real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `convex hull ((v:real^N) INSERT t0)` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [INT_ARITH_TAC; MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]]);;

(* Interiors in nested subspaces.                                            *)

let MOI_FBC_INTERIOR_TRANS = prove
 (`!(x:real^N->bool) y w a.
     y SUBSET x /\
     a SUBSET (subtopology euclidean y) interior_of w /\
     a SUBSET (subtopology euclidean x) interior_of y
     ==> a SUBSET (subtopology euclidean x) interior_of w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SUBSET; interior_of; IN_ELIM_THM; OPEN_IN_OPEN] THEN
  STRIP_TAC THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `o1:real^N->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `o2:real^N->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `x INTER (o1 INTER o2):real^N->bool` THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `o1 INTER o2:real^N->bool` THEN ASM_SIMP_TAC[OPEN_INTER];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Collars restricted to a union of components, and two collars glued into a *)
(* bicollar (DG CollarRestriction.lean, BicollarGluing.lean).                *)
(* ========================================================================= *)

(* Restriction.  If p collars b in x and b splits into the disjoint closed   *)
(* sets sb and b DIFF sb, then p restricted to sb x [0,1] is a collar of sb *)
(* in x: sb stays in the interior because the collar of b DIFF sb is a      *)
(* compact set missing sb.                                                   *)

let MOI_FBC_COLLAR_RESTRICT = prove
 (`!(x:real^N->bool) b sb w (p:real^(N,1)finite_sum->real^N) q.
     pl_homeomorphism (b PCROSS interval[vec 0:real^1,vec 1],w) (p,q) /\
     b SUBSET (subtopology euclidean x) interior_of w /\
     (!y. y IN b ==> p(pastecart y (vec 0)) = y) /\
     compact b /\ sb SUBSET b /\ closed sb /\ closed (b DIFF sb) /\
     locally_polyhedral sb
     ==> ?q'. pl_homeomorphism (sb PCROSS interval[vec 0:real^1,vec 1],
                                IMAGE p (sb PCROSS interval[vec 0,vec 1])) (p,q') /\
              IMAGE p (sb PCROSS interval[vec 0,vec 1]) SUBSET w /\
              sb SUBSET (subtopology euclidean x) interior_of
                          (IMAGE p (sb PCROSS interval[vec 0,vec 1]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `bounded (b:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (sb:real^N->bool) /\ compact (b DIFF sb:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(sb:real^N->bool) PCROSS interval[vec 0:real^1,vec 1] SUBSET (b:real^N->bool) PCROSS interval[vec 0,vec 1]`
  ASSUME_TAC THENL [ASM_SIMP_TAC[PCROSS_MONO; SUBSET_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_map_on (sb PCROSS interval[vec 0:real^1,vec 1])
              (p:real^(N,1)finite_sum->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `(b:real^N->bool) PCROSS interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FCL_LP_PCROSS THEN ASM_REWRITE_TAC[MOI_FCL_UNIT_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(sb:real^N->bool) PCROSS interval[vec 0:real^1,vec 1]`;
                 `p:real^(N,1)finite_sum->real^N`] MOI_FCL_PLH_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
    MAP_EVERY X_GEN_TAC [`z1:real^(N,1)finite_sum`; `z2:real^(N,1)finite_sum`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(q:real^N->real^(N,1)finite_sum) (p z1) = z1 /\ q (p z2) = z2`
    MP_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ASM_MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `g:real^N->real^(N,1)finite_sum`)] THEN
  EXISTS_TAC `g:real^N->real^(N,1)finite_sum` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `w = IMAGE (p:real^(N,1)finite_sum->real^N)
              ((sb:real^N->bool) PCROSS interval[vec 0:real^1,vec 1]) UNION
        IMAGE p ((b DIFF sb:real^N->bool) PCROSS interval[vec 0,vec 1])`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `w:real^N->bool`)) THEN
    REWRITE_TAC[GSYM IMAGE_UNION; GSYM PCROSS_UNION] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `w:real^N->bool`)) THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN (subtopology euclidean x) interior_of w` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[interior_of; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u INTER ((:real^N) DIFF
    IMAGE (p:real^(N,1)finite_sum->real^N) ((b DIFF sb:real^N->bool) PCROSS interval[vec 0,vec 1]))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER_OPEN THEN ASM_REWRITE_TAC[GSYM closed] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(b:real^N->bool) PCROSS interval[vec 0:real^1,vec 1]` THEN
    ASM_SIMP_TAC[PCROSS_MONO; SUBSET_REFL; SUBSET_DIFF];
    ASM_REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^(N,1)finite_sum` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(q:real^N->real^(N,1)finite_sum) y = z /\
                  q y = pastecart y (vec 0)`
    MP_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `y:real^N`)) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        SUBGOAL_THEN `(b DIFF sb:real^N->bool) PCROSS interval[vec 0:real^1,vec 1] SUBSET
                      (b:real^N->bool) PCROSS interval[vec 0,vec 1]` MP_TAC THENL
         [ASM_SIMP_TAC[PCROSS_MONO; SUBSET_REFL; SUBSET_DIFF]; ASM SET_TAC[]];
        SUBGOAL_THEN `(p:real^(N,1)finite_sum->real^N) (pastecart y (vec 0)) = y`
        (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL] THEN ASM SET_TAC[]];
      DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
      UNDISCH_TAC `(q:real^N->real^(N,1)finite_sum) y IN
                   (b DIFF sb:real^N->bool) PCROSS interval[vec 0,vec 1]` THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_DIFF]];
    UNDISCH_TAC `u SUBSET (w:real^N->bool)` THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `w:real^N->bool`)) THEN SET_TAC[]]);;

(* Two images meeting in t.                                                 *)

let MOI_FBC_IMAGE_MEET = prove
 (`!(f:A->B) s1 s2 t z1 z2.
     IMAGE f s1 INTER IMAGE f s2 = t /\ z1 IN s1 /\ z2 IN s2 /\ f z1 = f z2
     ==> f z1 IN t /\ f z2 IN t`,
  SET_TAC[]);;

(* Gluing.  Two collars of sb whose images meet exactly in sb give a        *)
(* bicollar: p1 on sb x [0,1], p2 composed with the flip on sb x [-1,0].     *)

let MOI_FBC_GLUE = prove
 (`!(sb:real^N->bool) w1 w2 (p1:real^(N,1)finite_sum->real^N) q1 p2 q2.
     compact sb /\ locally_polyhedral sb /\
     pl_homeomorphism (sb PCROSS interval[vec 0:real^1,vec 1],w1) (p1,q1) /\
     pl_homeomorphism (sb PCROSS interval[vec 0:real^1,vec 1],w2) (p2,q2) /\
     (!y. y IN sb ==> p1(pastecart y (vec 0)) = y /\ p2(pastecart y (vec 0)) = y) /\
     w1 INTER w2 = sb
     ==> ?p q. pl_homeomorphism
                 (sb PCROSS interval[--vec 1:real^1,vec 1],w1 UNION w2) (p,q) /\
               !y. y IN sb ==> p(pastecart y (vec 0)) = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (MP_TAC o GEN_REWRITE_RULE I [pl_homeomorphism])
    (CONJUNCTS_THEN2 (MP_TAC o GEN_REWRITE_RULE I [pl_homeomorphism])
     STRIP_ASSUME_TAC)))) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `fl = \z:real^(N,1)finite_sum. pastecart (fstcart z) (--(sndcart z))` THEN
  SUBGOAL_THEN
   `!x t. (fl:real^(N,1)finite_sum->real^(N,1)finite_sum) (pastecart x t) =
          pastecart x (--t)`
  ASSUME_TAC THENL
   [EXPAND_TAC "fl" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  ABBREV_TAC
   `p = \z:real^(N,1)finite_sum.
          if &0 <= drop(sndcart z) then (p1:real^(N,1)finite_sum->real^N) z
          else p2 ((fl:real^(N,1)finite_sum->real^(N,1)finite_sum) z)` THEN
  ABBREV_TAC `h1 = (sb:real^N->bool) PCROSS interval[vec 0:real^1,vec 1]` THEN
  ABBREV_TAC `h2 = (sb:real^N->bool) PCROSS interval[--vec 1:real^1,vec 0]` THEN
  SUBGOAL_THEN `compact (h1:real^(N,1)finite_sum->bool) /\
                compact (h2:real^(N,1)finite_sum->bool) /\
                locally_polyhedral (h2:real^(N,1)finite_sum->bool) /\
                (!y. y IN sb ==> pastecart (y:real^N) (vec 0:real^1) IN h1)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h1"; "h2"] THEN
    SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; ASSUME `compact (sb:real^N->bool)`;
             PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL] THEN
    MATCH_MP_TAC MOI_FCL_LP_PCROSS THEN
    REWRITE_TAC[POLYTOPE_INTERVAL; ASSUME `locally_polyhedral (sb:real^N->bool)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!z. z IN h1 ==> (p:real^(N,1)finite_sum->real^N) z = p1 z) /\
    (!z. z IN h2 ==> p z = p2 ((fl:real^(N,1)finite_sum->real^(N,1)finite_sum) z))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "h1"; "h2"] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `y:real^1 = vec 0` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_NEG_0] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sb:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1] = h1 UNION h2`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h1"; "h2"] THEN
    REWRITE_TAC[GSYM PCROSS_UNION] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (fl:real^(N,1)finite_sum->real^(N,1)finite_sum) h2 = h1 /\
    (!z. z IN h2 ==> fl z IN h1) /\ (!z. fl (fl z) = z)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h1"; "h2"] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PASTECART; EXISTS_PASTECART;
                PASTECART_IN_PCROSS; PASTECART_INJ] THEN
    REWRITE_TAC[ASSUME `!x t. (fl:real^(N,1)finite_sum->real^(N,1)finite_sum)
                               (pastecart x t) = pastecart x (--t)`;
                PASTECART_INJ; VECTOR_NEG_NEG; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real^1`] THEN EQ_TAC THENL
       [STRIP_TAC THEN ASM_REWRITE_TAC[DROP_NEG] THEN ASM_REAL_ARITH_TAC;
        STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^N`; `--t:real^1`] THEN
        ASM_REWRITE_TAC[VECTOR_NEG_NEG; DROP_NEG] THEN ASM_REAL_ARITH_TAC];
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* PL *)
  SUBGOAL_THEN
   `pl_map_on (h1 UNION h2:real^(N,1)finite_sum->bool)
              (p:real^(N,1)finite_sum->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_UNION THEN
    ASM_SIMP_TAC[CLOSED_SUBSET; SUBSET_UNION; COMPACT_IMP_CLOSED] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `p1:real^(N,1)finite_sum->real^N` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `(p2:real^(N,1)finite_sum->real^N) o
                  (fl:real^(N,1)finite_sum->real^(N,1)finite_sum)` THEN
      ASM_SIMP_TAC[o_THM] THEN
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
      EXISTS_TAC `h1:real^(N,1)finite_sum->bool` THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN
      MATCH_MP_TAC MOI_PTR_PL_MAP_ON_LINEAR THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "fl" THEN MATCH_MP_TAC LINEAR_PASTECART THEN
      REWRITE_TAC[ETA_AX; LINEAR_FSTCART] THEN
      MATCH_MP_TAC LINEAR_COMPOSE_NEG THEN REWRITE_TAC[ETA_AX; LINEAR_SNDCART]];
    ALL_TAC] THEN
  (* images *)
  SUBGOAL_THEN
   `IMAGE (p:real^(N,1)finite_sum->real^N) h1 = w1 /\ IMAGE p h2 = w2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (p1:real^(N,1)finite_sum->real^N) h1` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_EQ THEN
        ASM_SIMP_TAC[];
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE (p2:real^(N,1)finite_sum->real^N)
                    (IMAGE (fl:real^(N,1)finite_sum->real^(N,1)finite_sum) h2)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_o] THEN
        MATCH_MP_TAC IMAGE_EQ THEN
        ASM_SIMP_TAC[o_THM];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* points of sb *)
  SUBGOAL_THEN
   `!y. y IN sb ==> pastecart (y:real^N) (vec 0:real^1) IN h1 /\
                    (p:real^(N,1)finite_sum->real^N) (pastecart y (vec 0)) = y /\
                    (q1:real^N->real^(N,1)finite_sum) y = pastecart y (vec 0) /\
                    (q2:real^N->real^(N,1)finite_sum) y = pastecart y (vec 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pastecart (y:real^N) (vec 0:real^1) IN h1` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN h1 UNION h2 /\ (p:real^(N,1)finite_sum->real^N) z IN sb
        ==> z = pastecart (p z) (vec 0)`
  (LABEL_TAC "zl") THENL
   [X_GEN_TAC `z:real^(N,1)finite_sum` THEN REWRITE_TAC[IN_UNION] THEN
    STRIP_TAC THENL
     [ASM_MESON_TAC[];
      SUBGOAL_THEN `(fl:real^(N,1)finite_sum->real^(N,1)finite_sum) z =
                    pastecart ((p:real^(N,1)finite_sum->real^N) z) (vec 0)`
      MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `fl:real^(N,1)finite_sum->real^(N,1)finite_sum`) THEN
      ASM_REWRITE_TAC[VECTOR_NEG_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!z. z IN h1 ==> (q1:real^N->real^(N,1)finite_sum)
                       ((p:real^(N,1)finite_sum->real^N) z) = z) /\
    (!z. z IN h2 ==> (q2:real^N->real^(N,1)finite_sum) (p z) =
                     (fl:real^(N,1)finite_sum->real^(N,1)finite_sum) z)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h1 UNION h2:real^(N,1)finite_sum->bool`;
                 `p:real^(N,1)finite_sum->real^N`] MOI_FCL_PLH_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_UNION] THEN
    MAP_EVERY X_GEN_TAC [`z1:real^(N,1)finite_sum`; `z2:real^(N,1)finite_sum`] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `(q1:real^N->real^(N,1)finite_sum) (p (z1:real^(N,1)finite_sum))` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL [`p:real^(N,1)finite_sum->real^N`; `h1:real^(N,1)finite_sum->bool`;
                     `h2:real^(N,1)finite_sum->bool`; `sb:real^N->bool`;
                     `z1:real^(N,1)finite_sum`; `z2:real^(N,1)finite_sum`]
        MOI_FBC_IMAGE_MEET) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "zl" (MP_TAC o SPEC `z1:real^(N,1)finite_sum`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
      USE_THEN "zl" (MP_TAC o SPEC `z2:real^(N,1)finite_sum`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
      UNDISCH_TAC `(p:real^(N,1)finite_sum->real^N) z1 = p z2` THEN MESON_TAC[];
      MP_TAC(ISPECL [`p:real^(N,1)finite_sum->real^N`; `h2:real^(N,1)finite_sum->bool`;
                     `h1:real^(N,1)finite_sum->bool`; `sb:real^N->bool`;
                     `z1:real^(N,1)finite_sum`; `z2:real^(N,1)finite_sum`]
        MOI_FBC_IMAGE_MEET) THEN
      ANTS_TAC THENL
       [ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "zl" (MP_TAC o SPEC `z1:real^(N,1)finite_sum`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
      USE_THEN "zl" (MP_TAC o SPEC `z2:real^(N,1)finite_sum`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
      UNDISCH_TAC `(p:real^(N,1)finite_sum->real^N) z1 = p z2` THEN MESON_TAC[];
      SUBGOAL_THEN `(fl:real^(N,1)finite_sum->real^(N,1)finite_sum) z1 = fl z2`
      MP_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `(q2:real^N->real^(N,1)finite_sum) (p (z1:real^(N,1)finite_sum))` THEN
        CONJ_TAC THENL
         [CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        DISCH_THEN(MP_TAC o AP_TERM `fl:real^(N,1)finite_sum->real^(N,1)finite_sum`) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:real^N->real^(N,1)finite_sum`) THEN
  MAP_EVERY EXISTS_TAC [`p:real^(N,1)finite_sum->real^N`;
                        `q:real^N->real^(N,1)finite_sum`] THEN
  ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `pl_homeomorphism (h1 UNION h2,IMAGE (p:real^(N,1)finite_sum->real^N)
                                  (h1 UNION h2)) (p,q)` THEN
  ASM_REWRITE_TAC[IMAGE_UNION]);;

(* ========================================================================= *)
(* The two sides of a closed surface subcomplex L of a finite combinatorial  *)
(* 3-manifold with boundary K (abstract form).  L is full in K, misses the   *)
(* boundary, and the complement has exactly two components K1, K2, each      *)
(* accumulating on all of L.  Every tetrahedron of K lies on one side;       *)
(* closure K1 is the union of the tetrahedra on side 1; the two closures     *)
(* meet in UNIONS L and cover UNIONS K; K1 is open in UNIONS K.              *)
(* ========================================================================= *)

let moi_fbc_split = new_definition
 `moi_fbc_split (K:(real^N->bool)->bool) L K1 K2 <=>
    FINITE K /\ combinatorial_manifold_with_boundary 3 K /\
    simplicial_subcomplex L K /\ combinatorial_manifold 2 L /\
    (!q. q IN K ==> q INTER UNIONS L IN L /\ (q INTER UNIONS L) face_of q) /\
    DISJOINT (UNIONS L) (complex_boundary K) /\
    components (UNIONS K DIFF UNIONS L) = {K1,K2} /\ ~(K1 = K2) /\
    UNIONS L SUBSET closure K1 /\ UNIONS L SUBSET closure K2`;;

let MOI_FBC_SPLIT_SYM = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fbc_split K L K1 K2 ==> moi_fbc_split K L K2 K1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fbc_split] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_FBC_SPLIT_FACTS = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fbc_split K L K1 K2
     ==> lf_simplicial_complex K /\ simplicial_complex K /\
         FINITE L /\ simplicial_complex L /\ lf_simplicial_complex L /\
         L SUBSET K /\ UNIONS L SUBSET UNIONS K /\
         (!s. s IN L ==> aff_dim s <= &2) /\
         (!s. s IN K ==> compact s /\ convex s) /\
         K1 IN components (UNIONS K DIFF UNIONS L) /\
         K2 IN components (UNIONS K DIFF UNIONS L) /\
         K1 INTER K2 = {} /\
         K1 UNION K2 = UNIONS K DIFF UNIONS L /\
         compact (UNIONS K) /\ compact (UNIONS L)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fbc_split] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `(L:(real^N->bool)->bool) SUBSET K` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K ==> compact s /\ convex s` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_COMPACT; MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF; IN_INSERT] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_MESON_TAC[MOI_FRN_SA_CM_DIM];
    ASM_MESON_TAC[COMPONENTS_NONOVERLAP; IN_INSERT];
    FIRST_X_ASSUM(MP_TAC o AP_TERM `UNIONS:((real^N->bool)->bool)->real^N->bool` o
      check (fun th -> is_eq(concl th) &&
        (try fst(dest_const(rator(lhs(concl th)))) = "components"
         with Failure _ -> false))) THEN
    REWRITE_TAC[GSYM UNIONS_COMPONENTS; UNIONS_2] THEN MESON_TAC[];
    MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]]);;

(* A tetrahedron minus L is connected (star-shaped from a relative interior *)
(* point) and contains the relative interior, so it lies on exactly one    *)
(* side.                                                                     *)

let MOI_FBC_TET_SIDE = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 R.
     moi_fbc_split K L K1 K2 /\ R IN K /\ aff_dim R = &3
     ==> ~(relative_interior R = {}) /\
         relative_interior R SUBSET R DIFF UNIONS L /\
         (R DIFF UNIONS L SUBSET K1 \/ R DIFF UNIONS L SUBSET K2) /\
         ~(R DIFF UNIONS L SUBSET K1 /\ R DIFF UNIONS L SUBSET K2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fbc_split]) THEN
  SUBGOAL_THEN `compact (R:real^N->bool) /\ convex R` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(R INTER UNIONS L = R:real^N->bool)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `aff_dim (R:real^N->bool) <= &2` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior R SUBSET R DIFF UNIONS (L:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`R INTER UNIONS (L:(real^N->bool)->bool)`; `R:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_SIMP_TAC[] THEN MP_TAC(ISPEC `R:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior R:real^N->bool = {})` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim ({}:real^N->bool) = &3` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real^N`) THEN
  SUBGOAL_THEN `(c:real^N) IN R DIFF UNIONS L` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `R DIFF UNIONS L SUBSET
                connected_component (UNIONS K DIFF UNIONS L) (c:real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC STARLIKE_IMP_CONNECTED THEN REWRITE_TAC[starlike] THEN
      EXISTS_TAC `c:real^N` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      MP_TAC(ISPECL [`R:real^N->bool`; `c:real^N`; `y:real^N`]
        IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPEC `R:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
        UNDISCH_TAC `relative_interior R SUBSET R DIFF UNIONS (L:(real^N->bool)->bool)` THEN
        UNDISCH_TAC `(c:real^N) IN R DIFF UNIONS L` THEN
        UNDISCH_TAC `(y:real^N) IN R DIFF UNIONS L` THEN SET_TAC[]];
      SUBGOAL_THEN `(R:real^N->bool) SUBSET UNIONS K` MP_TAC THENL
       [ASM SET_TAC[]; SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_component (UNIONS K DIFF UNIONS L) (c:real^N) = K1 \/
                connected_component (UNIONS K DIFF UNIONS L) c = K2` MP_TAC THENL
   [SUBGOAL_THEN `connected_component (UNIONS K DIFF UNIONS L) (c:real^N) IN
                  components (UNIONS K DIFF UNIONS (L:(real^N->bool)->bool))` MP_TAC THENL
     [REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `c:real^N` THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `(R:real^N->bool) SUBSET UNIONS K` MP_TAC THENL
       [ASM SET_TAC[]; UNDISCH_TAC `(c:real^N) IN R DIFF UNIONS L` THEN SET_TAC[]];
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN
  UNDISCH_TAC `(c:real^N) IN R DIFF UNIONS L` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "SUBSET" &&
        lhand(concl th) = `R DIFF UNIONS (L:(real^N->bool)->bool)`
    with Failure _ -> false)) THEN
  SET_TAC[]);;

(* Every point of K lies in a tetrahedron.                                   *)

let MOI_FBC_TET_COVER = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 x.
     moi_fbc_split K L K1 K2 /\ x IN UNIONS K
     ==> ?R. R IN K /\ aff_dim R = &3 /\ x IN R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fbc_split]) THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS K` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `q:real^N->bool`] MOI_FBC_CMWB3_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `R:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The closure of a side is the union of its tetrahedra.                     *)

let MOI_FBC_SIDE_UNIONS = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fbc_split K L K1 K2
     ==> closure K1 =
         UNIONS {R | R IN K /\ aff_dim R = &3 /\ R DIFF UNIONS L SUBSET K1} /\
         closure K1 DIFF UNIONS L = K1 /\
         closure K1 SUBSET UNIONS K`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SPLIT_FACTS) THEN
  ABBREV_TAC `T1 = {R:real^N->bool | R IN K /\ aff_dim R = &3 /\
                                      R DIFF UNIONS L SUBSET K1}` THEN
  SUBGOAL_THEN `UNIONS (T1:(real^N->bool)->bool) SUBSET UNIONS K` ASSUME_TAC THENL
   [EXPAND_TAC "T1" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS (T1:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[moi_fbc_split]; EXPAND_TAC "T1" THEN SET_TAC[]];
      EXPAND_TAC "T1" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K1:real^N->bool) SUBSET UNIONS T1` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS K DIFF UNIONS L` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `x:real^N`]
      MOI_FBC_TET_COVER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
      MOI_FBC_TET_SIDE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `R:real^N->bool` THEN
      EXPAND_TAC "T1" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN
      UNDISCH_TAC `R DIFF UNIONS L SUBSET (K2:real^N->bool)` THEN
      UNDISCH_TAC `(x:real^N) IN K1` THEN UNDISCH_TAC `(x:real^N) IN R` THEN
      UNDISCH_TAC `(x:real^N) IN UNIONS K DIFF UNIONS L` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS T1 SUBSET closure (K1:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "T1" THEN REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `R:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
      MOI_FBC_TET_SIDE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `compact (R:real^N->bool) /\ convex R` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `R = closure (relative_interior R:real^N->bool)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED;
                   COMPACT_IMP_CLOSED];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure K1 = UNIONS (T1:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF] THEN X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [EXPAND_TAC "T1" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN SET_TAC[];
    UNDISCH_TAC `(K1:real^N->bool) SUBSET UNIONS T1` THEN
    UNDISCH_TAC `K1 UNION K2:real^N->bool = UNIONS K DIFF UNIONS L` THEN
    SET_TAC[]]);;

(* The two closures meet in UNIONS L and cover UNIONS K.                     *)

let MOI_FBC_SIDES_MEET = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fbc_split K L K1 K2
     ==> closure K1 INTER closure K2 = UNIONS L /\
         closure K1 UNION closure K2 = UNIONS K /\
         closure K1 INTER K2 = {} /\ K1 INTER closure K2 = {}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SIDE_UNIONS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SIDE_UNIONS o
    MATCH_MP MOI_FBC_SPLIT_SYM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fbc_split]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET_INTER] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `closure K1 DIFF UNIONS L = (K1:real^N->bool)` THEN
      UNDISCH_TAC `closure K2 DIFF UNIONS L = (K2:real^N->bool)` THEN
      UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN SET_TAC[];
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[UNION_SUBSET] THEN
    CONJ_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `x:real^N`]
      MOI_FBC_TET_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
      MOI_FBC_TET_SIDE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[IN_UNION] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    EXISTS_TAC `R:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    UNDISCH_TAC `closure K1 DIFF UNIONS L = (K1:real^N->bool)` THEN
    UNDISCH_TAC `K1 UNION K2:real^N->bool = UNIONS K DIFF UNIONS L` THEN
    UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN SET_TAC[];
    UNDISCH_TAC `closure K2 DIFF UNIONS L = (K2:real^N->bool)` THEN
    UNDISCH_TAC `K1 UNION K2:real^N->bool = UNIONS K DIFF UNIONS L` THEN
    UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN SET_TAC[]]);;

(* Near a point, K is covered by the tetrahedra through the point.          *)

let MOI_FBC_LOCAL_TETS = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 x.
     moi_fbc_split K L K1 K2 /\ x IN UNIONS K
     ==> ?e. &0 < e /\
             !y. y IN UNIONS K /\ dist(x,y) < e
                 ==> ?R. R IN K /\ aff_dim R = &3 /\ x IN R /\ y IN R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SPLIT_FACTS) THEN
  SUBGOAL_THEN
   `closed (UNIONS {R:real^N->bool | R IN K /\ aff_dim R = &3 /\ ~(x IN R)})`
  MP_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[moi_fbc_split]; SET_TAC[]];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `y:real^N`]
    MOI_FBC_TET_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `R:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `ball(x:real^N,e) SUBSET
               (:real^N) DIFF UNIONS {R | R IN K /\ aff_dim R = &3 /\ ~(x IN R)}` THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `R:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* A side is open in UNIONS K.                                               *)

let MOI_FBC_SIDE_OPEN = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fbc_split K L K1 K2 ==> open_in (subtopology euclidean (UNIONS K)) K1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SPLIT_FACTS) THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS K DIFF UNIONS L` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `x:real^N`]
    MOI_FBC_LOCAL_TETS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?e2. &0 < e2 /\ ball(x:real^N,e2) SUBSET (:real^N) DIFF UNIONS L`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open ((:real^N) DIFF UNIONS L)` MP_TAC THENL
     [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `min e1 e2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; REAL_LT_MIN] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `e1:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
    MOI_FBC_TET_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `~((y:real^N) IN UNIONS L)` MP_TAC THENL
     [UNDISCH_TAC `ball(x:real^N,e2) SUBSET (:real^N) DIFF UNIONS L` THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `R DIFF UNIONS L SUBSET (K1:real^N->bool)` THEN
      UNDISCH_TAC `(y:real^N) IN R` THEN SET_TAC[]];
    UNDISCH_TAC `R DIFF UNIONS L SUBSET (K2:real^N->bool)` THEN
    UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN
    UNDISCH_TAC `(x:real^N) IN K1` THEN UNDISCH_TAC `(x:real^N) IN R` THEN
    UNDISCH_TAC `(x:real^N) IN UNIONS K DIFF UNIONS L` THEN SET_TAC[]]);;

(* ========================================================================= *)
(* The side complex A = the simplices of K inside closure K1; its vertex     *)
(* links (equal to those of K off L, 2-cells bounded by the link of L on L,  *)
(* by MOI_S4O_SPHERE_PIECE); A is a combinatorial 3-manifold with boundary   *)
(* containing L, and its boundary off L lies in the boundary of K.           *)
(* ========================================================================= *)

(* Tetrahedra and the closures of the sides.                                 *)

let MOI_FBC_TET_CLOSURE_SIDE = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 R.
     moi_fbc_split K L K1 K2 /\ R IN K /\ aff_dim R = &3
     ==> (R DIFF UNIONS L SUBSET K1 ==> R SUBSET closure K1) /\
         (R SUBSET closure K1 \/ R SUBSET closure K2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!K1' K2'. moi_fbc_split K L K1' K2' /\ R DIFF UNIONS L SUBSET K1'
              ==> R SUBSET closure (K1':real^N->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SIDE_UNIONS) THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `R:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
    MOI_FBC_TET_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `R SUBSET closure (K1:real^N->bool)` (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `K2:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `R SUBSET closure (K2:real^N->bool)` (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `K1:real^N->bool` THEN
      ASM_SIMP_TAC[MOI_FBC_SPLIT_SYM];
      DISCH_TAC THEN
      UNDISCH_TAC `~(R DIFF UNIONS L SUBSET K1 /\
                     R DIFF UNIONS L SUBSET (K2:real^N->bool))` THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_FBC_SIDE_TET_AT = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fbc_split K L K1 K2 /\ w IN closure K1
     ==> ?R. R IN K /\ aff_dim R = &3 /\ w IN R /\ R SUBSET closure K1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SIDE_UNIONS) THEN
  UNDISCH_TAC `(w:real^N) IN closure K1` THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `R:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
    MOI_FBC_TET_CLOSURE_SIDE) THEN
  ASM_SIMP_TAC[]);;

(* The side complex.                                                         *)

let MOI_FBC_SIDE_COMPLEX = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fbc_split K L K1 K2
     ==> simplicial_subcomplex {q | q IN K /\ q SUBSET closure K1} K /\
         FINITE {q | q IN K /\ q SUBSET closure K1} /\
         lf_simplicial_complex {q | q IN K /\ q SUBSET closure K1} /\
         UNIONS {q | q IN K /\ q SUBSET closure K1} = closure K1 /\
         L SUBSET {q | q IN K /\ q SUBSET closure K1}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fbc_split]) THEN
  SUBGOAL_THEN `simplicial_subcomplex {q | q IN K /\ q SUBSET closure K1}
                                      (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; IN_ELIM_THM] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:real^N->bool`] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_FACE];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
    EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `x:real^N`]
      MOI_FBC_SIDE_TET_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `R:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `q:real^N->bool` THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS L:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* Links off L: all tetrahedra at a vertex off L lie on its side.             *)

let MOI_FBC_SIDE_LINK_OFF = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fbc_split K L K1 K2 /\ w IN closure K1 /\ ~(w IN UNIONS L)
     ==> simplicial_link {q | q IN K /\ q SUBSET closure K1} w =
         simplicial_link K w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fbc_split]) THEN
  SUBGOAL_THEN `(w:real^N) IN K1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`] MOI_FBC_SIDE_UNIONS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `closure K1 DIFF UNIONS L = (K1:real^N->bool)` THEN
    UNDISCH_TAC `(w:real^N) IN closure K1` THEN
    UNDISCH_TAC `~((w:real^N) IN UNIONS L)` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[simplicial_link; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N->bool` THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FBC_CMWB3_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
    MOI_FBC_TET_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))) THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [ALL_TAC;
    UNDISCH_TAC `R DIFF UNIONS L SUBSET (K2:real^N->bool)` THEN
    UNDISCH_TAC `K1 INTER K2:real^N->bool = {}` THEN
    UNDISCH_TAC `(w:real^N) IN K1` THEN
    UNDISCH_TAC `~((w:real^N) IN UNIONS L)` THEN
    UNDISCH_TAC `(t:real^N->bool) SUBSET R` THEN
    UNDISCH_TAC `(w:real^N) IN t` THEN SET_TAC[]] THEN
  SUBGOAL_THEN `(R:real^N->bool) SUBSET closure K1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
      MOI_FBC_TET_CLOSURE_SIDE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^N->bool) face_of R` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N->bool) SUBSET t` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    EXISTS_TAC `R:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[FACE_OF_TRANS]]]);;

(* Links of subcomplexes.                                                    *)

let MOI_FBC_LINK_SUBSET = prove
 (`!(c:(real^N->bool)->bool) d w.
     c SUBSET d ==> simplicial_link c w SUBSET simplicial_link d w`,
  REWRITE_TAC[simplicial_link; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

(* The link of a vertex of K is covered by its links in the two sides.       *)

let MOI_FBC_LINK_COVER = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fbc_split K L K1 K2 /\ {w} IN K
     ==> simplicial_link K w SUBSET
         simplicial_link {q | q IN K /\ q SUBSET closure K1} w UNION
         simplicial_link {q | q IN K /\ q SUBSET closure K2} w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fbc_split]) THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N->bool` THEN
  REWRITE_TAC[simplicial_link; IN_UNION; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FBC_CMWB3_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t:real^N->bool) face_of R` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N->bool) SUBSET R /\ x face_of R` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS; FACE_OF_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `R:real^N->bool`]
    MOI_FBC_TET_CLOSURE_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_TAC o CONJUNCT2) THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL
    [ASM SET_TAC[];
     EXISTS_TAC `R:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]));;

(* Points of L in the link of K lie in the link of L (fullness).             *)

let MOI_FBC_LINK_FULL = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fbc_split K L K1 K2 /\ {w} IN K /\ w IN UNIONS L
     ==> UNIONS L INTER UNIONS (simplicial_link K w) SUBSET
         UNIONS (simplicial_link L w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fbc_split]) THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN UNIONS (simplicial_link K w)` THEN
  REWRITE_TAC[IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `q INTER UNIONS L IN (L:(real^N->bool)->bool) /\
    t INTER UNIONS L IN L /\ (q INTER UNIONS L) SUBSET (t INTER UNIONS L)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(q:real^N->bool) SUBSET t` MP_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `q INTER UNIONS L:real^N->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
  EXISTS_TAC `t INTER UNIONS L:real^N->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
  MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
  EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

(* A tetrahedron of a side at w contributes a link triangle off L.          *)

let MOI_FBC_LINK_TRI = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w R.
     moi_fbc_split K L K1 K2 /\ {w} IN K /\ w IN UNIONS L /\
     R IN K /\ aff_dim R = &3 /\ w IN R /\ R SUBSET closure K1
     ==> ?e. e IN simplicial_link {q | q IN K /\ q SUBSET closure K1} w /\
             ~(e SUBSET UNIONS L) /\ e SUBSET R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fbc_split]) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w:real^N`; `R:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `(e:real^N->bool) IN K /\ ~(w IN e)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(e:real^N->bool) IN simplicial_link K w` THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) SUBSET R` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `R:real^N->bool`)) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(w:real^N) INSERT e` THEN
    REWRITE_TAC[HULL_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `R:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `R INTER UNIONS L = R:real^N->bool` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[INTER_SUBSET] THEN
      SUBGOAL_THEN `convex hull ((w:real^N) INSERT e) SUBSET R INTER UNIONS L`
      MP_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
       [UNDISCH_TAC `(e:real^N->bool) SUBSET UNIONS L` THEN
        UNDISCH_TAC `(e:real^N->bool) SUBSET R` THEN
        UNDISCH_TAC `(w:real^N) IN R` THEN UNDISCH_TAC `(w:real^N) IN UNIONS L` THEN
        SET_TAC[];
        MATCH_MP_TAC FACE_OF_IMP_CONVEX THEN EXISTS_TAC `R:real^N->bool` THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim (R:real^N->bool) <= &2` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]]);;

(* Links on L: the link of A at a vertex of L is the closure of one side of *)
(* the circle link_L inside the 2-sphere link_K (2D Schoenflies).            *)

let MOI_FBC_SIDE_LINK_ON = prove
 (`!(K:(real^N->bool)->bool) L K1 K2 w.
     moi_fbc_split K L K1 K2 /\ {w} IN K /\ w IN UNIONS L
     ==> pl_ball 2 (UNIONS (simplicial_link {q | q IN K /\ q SUBSET closure K1} w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SIDES_MEET) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fbc_split]) THEN
  SUBGOAL_THEN `pl_sphere 2 (UNIONS (simplicial_link K (w:real^N)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w:real^N`] MOI_FM3_CB_VERTEX_CLASSIFY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    UNDISCH_TAC `DISJOINT (UNIONS L) (complex_boundary (K:(real^N->bool)->bool))` THEN
    UNDISCH_TAC `(w:real^N) IN UNIONS L` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^N} IN L` ASSUME_TAC THENL
   [MP_TAC(CONJUNCT1(MATCH_MP (ISPEC `{w:real^N}` (ASSUME
      `!q:real^N->bool. q IN K ==> q INTER UNIONS L IN L /\ (q INTER UNIONS L) face_of q`))
      (ASSUME `{w:real^N} IN K`))) THEN
    SUBGOAL_THEN `{w:real^N} INTER UNIONS L = {w}` SUBST1_TAC THENL
     [UNDISCH_TAC `(w:real^N) IN UNIONS L` THEN SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (UNIONS (simplicial_link L (w:real^N)))` ASSUME_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold 2 (L:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `w:real^N`]
    MOI_FBC_LINK_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `w:real^N`]
    MOI_FBC_LINK_FULL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* tetrahedra at w on both sides *)
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `w:real^N`]
    MOI_FBC_SIDE_TET_AT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K2:real^N->bool`; `K1:real^N->bool`; `w:real^N`]
    MOI_FBC_SIDE_TET_AT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_FBC_SPLIT_SYM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R2:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`; `w:real^N`; `R1:real^N->bool`]
    MOI_FBC_LINK_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                 `K2:real^N->bool`; `K1:real^N->bool`; `w:real^N`; `R2:real^N->bool`]
    MOI_FBC_LINK_TRI) THEN
  ASM_SIMP_TAC[MOI_FBC_SPLIT_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real^N->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `A = {q:real^N->bool | q IN K /\ q SUBSET closure K1}` THEN
  ABBREV_TAC `B = {q:real^N->bool | q IN K /\ q SUBSET closure K2}` THEN
  SUBGOAL_THEN `(L:(real^N->bool)->bool) SUBSET A /\ A SUBSET K /\ B SUBSET K /\
                UNIONS A SUBSET closure K1 /\ UNIONS B SUBSET closure K2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    UNDISCH_TAC `UNIONS L SUBSET closure (K1:real^N->bool)` THEN
    UNDISCH_TAC `(L:(real^N->bool)->bool) SUBSET K` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_link L (w:real^N) SUBSET simplicial_link A w /\
                simplicial_link A w SUBSET simplicial_link K w /\
                simplicial_link B w SUBSET simplicial_link K w /\
                simplicial_link A w SUBSET A /\ simplicial_link B w SUBSET B /\
                simplicial_link L w SUBSET L /\ simplicial_link K w SUBSET K`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FBC_LINK_SUBSET] THEN
    REWRITE_TAC[simplicial_link] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (simplicial_link K (w:real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LINK_FINITE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `closed (UNIONS (simplicial_link A (w:real^N))) /\
    closed (UNIONS (simplicial_link B (w:real^N)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `simplicial_link K (w:real^N)` THEN ASM_REWRITE_TAC[] THEN
        NO_TAC) THEN
    X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    SUBGOAL_THEN `(q:real^N->bool) IN K` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (UNIONS (simplicial_link A (w:real^N)))
                            (UNIONS (simplicial_link L w))`
  MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[]] THEN
  SUBGOAL_THEN
   `UNIONS (simplicial_link A (w:real^N)) SUBSET closure K1 /\
    UNIONS (simplicial_link B w) SUBSET closure K2 /\
    UNIONS (simplicial_link A w) SUBSET UNIONS (simplicial_link K w) /\
    UNIONS (simplicial_link L w) SUBSET UNIONS (simplicial_link A w) /\
    UNIONS (simplicial_link L w) SUBSET UNIONS L /\
    UNIONS (simplicial_link K w) SUBSET
      UNIONS (simplicial_link A w) UNION UNIONS (simplicial_link B w) /\
    e1 SUBSET UNIONS (simplicial_link A w) /\
    e2 SUBSET UNIONS (simplicial_link K w)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS (A:(real^N->bool)->bool)` THEN
      ASM_SIMP_TAC[SUBSET_UNIONS];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS (B:(real^N->bool)->bool)` THEN
      ASM_SIMP_TAC[SUBSET_UNIONS];
      MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `simplicial_link K (w:real^N) SUBSET
                   simplicial_link A w UNION simplicial_link B w` THEN SET_TAC[];
      UNDISCH_TAC `(e1:real^N->bool) IN simplicial_link A w` THEN SET_TAC[];
      UNDISCH_TAC `(e2:real^N->bool) IN simplicial_link B w` THEN
      UNDISCH_TAC `simplicial_link B (w:real^N) SUBSET simplicial_link K w` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4O_SPHERE_PIECE THEN
  EXISTS_TAC `UNIONS (simplicial_link K (w:real^N))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS (simplicial_link B (w:real^N)) INTER
                UNIONS (simplicial_link A w)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!s t u:real^N->bool. s SUBSET t ==> s INTER u SUBSET t INTER u`) THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `UNIONS (simplicial_link K (w:real^N)) SUBSET
                   UNIONS (simplicial_link A w) UNION UNIONS (simplicial_link B w)` THEN
      SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS L INTER UNIONS (simplicial_link K (w:real^N))` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `closure K1 INTER closure K2 = UNIONS (L:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `UNIONS (simplicial_link A (w:real^N)) SUBSET closure K1` THEN
      UNDISCH_TAC `UNIONS (simplicial_link B (w:real^N)) SUBSET closure K2` THEN
      UNDISCH_TAC `UNIONS (simplicial_link A (w:real^N)) SUBSET
                   UNIONS (simplicial_link K w)` THEN
      SET_TAC[]];
    DISCH_TAC THEN UNDISCH_TAC `~(e1 SUBSET UNIONS (L:(real^N->bool)->bool))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS (simplicial_link A (w:real^N))` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS (simplicial_link L (w:real^N))` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN UNDISCH_TAC `~(e2 SUBSET UNIONS (L:(real^N->bool)->bool))` THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `closure K1 INTER closure K2 = UNIONS (L:(real^N->bool)->bool)`)) THEN
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS (simplicial_link K (w:real^N))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS (simplicial_link A (w:real^N))` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `R2:real^N->bool` THEN
      ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* The side complex is a combinatorial 3-manifold with boundary, L lies in   *)
(* its boundary, and its boundary off L lies in the boundary of K (interior  *)
(* points of A are interior in K: MOI_FCL_INTERIOR_OPEN_IN, the other side   *)
(* accumulates on L; MOI_FCL_BD_NOT_INTERIOR with the open side K1).  Then   *)
(* the abstract bicollar: BOUNDARY_COLLAR on both sides, restricted to L     *)
(* (MOI_FBC_COLLAR_RESTRICT) and glued (MOI_FBC_GLUE).                       *)
(* ========================================================================= *)

let MOI_FBC_SIDE_MANIFOLD = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fbc_split K L K1 K2
     ==> combinatorial_manifold_with_boundary 3 {q | q IN K /\ q SUBSET closure K1} /\
         UNIONS L SUBSET complex_boundary {q | q IN K /\ q SUBSET closure K1} /\
         complex_boundary {q | q IN K /\ q SUBSET closure K1} DIFF UNIONS L
           SUBSET complex_boundary K`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SIDE_COMPLEX) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SIDES_MEET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_FBC_SIDE_OPEN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fbc_split]) THEN
  SUBGOAL_THEN `closure K1 DIFF UNIONS L = (K1:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                   `K1:real^N->bool`; `K2:real^N->bool`] MOI_FBC_SIDE_UNIONS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 3
                  {q:real^N->bool | q IN K /\ q SUBSET closure K1}`
  ASSUME_TAC THENL
   [REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `{w:real^N} IN K /\ w IN closure K1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `{w:real^N} IN {q | q IN K /\ q SUBSET closure K1}` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(w:real^N) IN UNIONS L` THENL
     [DISJ2_TAC THEN MATCH_MP_TAC MOI_FBC_SIDE_LINK_ON THEN
      MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `K2:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `L:(real^N->bool)->bool`;
                     `K1:real^N->bool`; `K2:real^N->bool`; `w:real^N`]
        MOI_FBC_SIDE_LINK_OFF) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (K:(real^N->bool)->bool)` THEN
      REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `complex_boundary {q:real^N->bool | q IN K /\ q SUBSET closure K1} SUBSET closure K1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS {q:real^N->bool | q IN K /\ q SUBSET closure K1}` THEN
    CONJ_TAC THENL [REWRITE_TAC[complex_boundary] THEN SET_TAC[]; ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`;
                   `{q:real^N->bool | q IN K /\ q SUBSET closure K1}`]
      MOI_FCL_INTERIOR_OPEN_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `closure K1 UNION closure K2 = UNIONS (K:(real^N->bool)->bool)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`u:real^N->bool`; `K2:real^N->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `closure K1 DIFF
                 complex_boundary {q:real^N->bool | q IN K /\ q SUBSET closure K1} =
                 UNIONS K INTER u` THEN
    UNDISCH_TAC `closure K1 INTER K2:real^N->bool = {}` THEN
    UNDISCH_TAC `K1 UNION K2:real^N->bool = UNIONS K DIFF UNIONS L` THEN
    UNDISCH_TAC `UNIONS L SUBSET closure (K1:real^N->bool)` THEN
    UNDISCH_TAC `UNIONS L SUBSET closure (K2:real^N->bool)` THEN
    UNDISCH_TAC `(x:real^N) IN UNIONS L` THEN
    UNDISCH_TAC `~((x:real^N) IN
                   complex_boundary {q:real^N->bool | q IN K /\ q SUBSET closure K1})` THEN
    SET_TAC[];
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`;
                   `{q:real^N->bool | q IN K /\ q SUBSET closure K1}`;
                   `x:real^N`; `K1:real^N->bool`] MOI_FCL_BD_NOT_INTERIOR) THEN
    ASM_REWRITE_TAC[CLOSURE_SUBSET] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `closure K1 UNION closure K2 = UNIONS (K:(real^N->bool)->bool)` THEN
      SET_TAC[];
      UNDISCH_TAC `closure K1 DIFF UNIONS L = (K1:real^N->bool)` THEN
      UNDISCH_TAC `complex_boundary {q:real^N->bool | q IN K /\ q SUBSET closure K1}
                   SUBSET closure K1` THEN
      UNDISCH_TAC `(x:real^N) IN
                   complex_boundary {q:real^N->bool | q IN K /\ q SUBSET closure K1}` THEN
      UNDISCH_TAC `~((x:real^N) IN UNIONS L)` THEN SET_TAC[]]]);;

(* A collar of L in the closure of one side.                                 *)

let MOI_FBC_SIDE_COLLAR = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fbc_split K L K1 K2
     ==> ?w (p:real^(N,1)finite_sum->real^N) q.
           pl_homeomorphism (UNIONS L PCROSS interval[vec 0:real^1,vec 1],w) (p,q) /\
           w SUBSET closure K1 /\
           UNIONS L SUBSET (subtopology euclidean (closure K1)) interior_of w /\
           !x. x IN UNIONS L ==> p(pastecart x (vec 0)) = x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SIDE_COMPLEX) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SIDE_MANIFOLD) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SIDES_MEET) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fbc_split]) THEN
  ABBREV_TAC `A = {q:real^N->bool | q IN K /\ q SUBSET closure K1}` THEN
  MP_TAC(ISPECL [`A:(real^N->bool)->bool`; `UNIONS A:real^N->bool`]
    BOUNDARY_COLLAR) THEN
  ASM_REWRITE_TAC[OPEN_IN_REFL] THEN ANTS_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS A:real^N->bool` THEN
    CONJ_TAC THENL [REWRITE_TAC[complex_boundary] THEN SET_TAC[];
                    ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (X_CHOOSE_THEN
    `p:real^(N,1)finite_sum->real^N` (X_CHOOSE_THEN
    `q:real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `closed (complex_boundary (A:(real^N->bool)->bool)) /\
                closed (complex_boundary (K:(real^N->bool)->bool))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FCL_CB_CLOSED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`closure K1:real^N->bool`; `complex_boundary (A:(real^N->bool)->bool)`;
                 `UNIONS L:real^N->bool`; `w:real^N->bool`;
                 `p:real^(N,1)finite_sum->real^N`; `q:real^N->real^(N,1)finite_sum`]
    MOI_FBC_COLLAR_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `UNIONS K:real^N->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS A:real^N->bool` THEN
      CONJ_TAC THENL [REWRITE_TAC[complex_boundary] THEN SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `closure K1 UNION closure K2 = UNIONS (K:(real^N->bool)->bool)` THEN
      SET_TAC[];
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      SUBGOAL_THEN `complex_boundary A DIFF UNIONS L =
                    complex_boundary A INTER complex_boundary (K:(real^N->bool)->bool)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `complex_boundary A DIFF UNIONS L SUBSET
                     complex_boundary (K:(real^N->bool)->bool)` THEN
        UNDISCH_TAC `DISJOINT (UNIONS L) (complex_boundary (K:(real^N->bool)->bool))` THEN
        SET_TAC[];
        ASM_SIMP_TAC[CLOSED_INTER]];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_LF_COMPLEX THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q':real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (p:real^(N,1)finite_sum->real^N)
           (UNIONS L PCROSS interval[vec 0:real^1,vec 1])`;
    `p:real^(N,1)finite_sum->real^N`; `q':real^N->real^(N,1)finite_sum`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `w:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[]]);;

(* The abstract bicollar.                                                    *)

let MOI_FBC_SIDES_BICOLLAR = prove
 (`!(K:(real^N->bool)->bool) L K1 K2.
     moi_fbc_split K L K1 K2
     ==> ?w (p:real^(N,1)finite_sum->real^N) q.
           pl_homeomorphism (UNIONS L PCROSS interval[--vec 1:real^1,vec 1],w) (p,q) /\
           w SUBSET UNIONS K /\
           UNIONS L SUBSET (subtopology euclidean (UNIONS K)) interior_of w /\
           !x. x IN UNIONS L ==> p(pastecart x (vec 0)) = x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SPLIT_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FBC_SIDES_MEET) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FBC_SIDE_COLLAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^N->bool` (X_CHOOSE_THEN
    `p1:real^(N,1)finite_sum->real^N` (X_CHOOSE_THEN
    `q1:real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FBC_SIDE_COLLAR o MATCH_MP MOI_FBC_SPLIT_SYM) THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real^N->bool` (X_CHOOSE_THEN
    `p2:real^(N,1)finite_sum->real^N` (X_CHOOSE_THEN
    `q2:real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `UNIONS L SUBSET (w1:real^N->bool) /\ UNIONS L SUBSET (w2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
     [EXISTS_TAC `(subtopology euclidean (closure K1)) interior_of (w1:real^N->bool)`;
      EXISTS_TAC `(subtopology euclidean (closure K2)) interior_of (w2:real^N->bool)`] THEN
    ASM_REWRITE_TAC[INTERIOR_OF_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `w1:real^N->bool`; `w2:real^N->bool`;
                 `p1:real^(N,1)finite_sum->real^N`; `q1:real^N->real^(N,1)finite_sum`;
                 `p2:real^(N,1)finite_sum->real^N`; `q2:real^N->real^(N,1)finite_sum`]
    MOI_FBC_GLUE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOCALLY_POLYHEDRAL_LF_COMPLEX THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[SUBSET_INTER] THEN
      UNDISCH_TAC `closure K1 INTER closure K2 = UNIONS (L:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(w1:real^N->bool) SUBSET closure K1` THEN
      UNDISCH_TAC `(w2:real^N->bool) SUBSET closure K2` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^(N,1)finite_sum->real^N`
    (X_CHOOSE_THEN `q:real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`w1 UNION w2:real^N->bool`; `p:real^(N,1)finite_sum->real^N`;
                        `q:real^N->real^(N,1)finite_sum`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `closure K1 UNION closure K2 = UNIONS (K:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(w1:real^N->bool) SUBSET closure K1` THEN
    UNDISCH_TAC `(w2:real^N->bool) SUBSET closure K2` THEN SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(x:real^N) IN (subtopology euclidean (closure K1)) interior_of w1 /\
    x IN (subtopology euclidean (closure K2)) interior_of w2`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[interior_of; IN_ELIM_THM; OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t1:real^N->bool` (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `o1:real^N->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `t2:real^N->bool` (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `o2:real^N->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `UNIONS K INTER (o1 INTER o2):real^N->bool` THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `o1 INTER o2:real^N->bool` THEN ASM_SIMP_TAC[OPEN_INTER];
    SUBGOAL_THEN `(x:real^N) IN UNIONS K` MP_TAC THENL
     [ASM SET_TAC[]; UNDISCH_TAC `(x:real^N) IN t1` THEN UNDISCH_TAC `(x:real^N) IN t2` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    UNDISCH_TAC `closure K1 UNION closure K2 = UNIONS (K:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `(t1:real^N->bool) SUBSET w1` THEN
    UNDISCH_TAC `(t2:real^N->bool) SUBSET w2` THEN
    UNDISCH_TAC `t1 = closure K1 INTER (o1:real^N->bool)` THEN
    UNDISCH_TAC `t2 = closure K2 INTER (o2:real^N->bool)` THEN SET_TAC[]]);;

(* ========================================================================= *)
(* The second derived neighbourhood N of a connected two-sided closed        *)
(* surface subcomplex s of a finite combinatorial 3-manifold t with          *)
(* boundary, s missing the boundary, splits along the second derived of s    *)
(* (SURFACE_NBHD_SIDES, DERIVED_NBHD_COMBINATORIAL, fullness MOI_FRN_FULL);  *)
(* hence a bicollar of UNIONS s inside N, a neighbourhood in UNIONS t.       *)
(* ========================================================================= *)

let MOI_FBC_DERIVED_SPLIT = prove
 (`!(t:(real^N->bool)->bool) s.
     FINITE t /\ combinatorial_manifold_with_boundary 3 t /\
     simplicial_subcomplex s t /\ combinatorial_manifold 2 s /\
     connected (UNIONS s) /\ ~(UNIONS s = {}) /\
     DISJOINT (UNIONS s) (complex_boundary t) /\
     two_sided_in (UNIONS t) (UNIONS s)
     ==> ?K1 K2. moi_fbc_split (derived_nbhd_complex t s)
                   (barycentric_subdivision (barycentric_subdivision s)) K1 K2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (s:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v))`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_CB_VERTEX_CLASSIFY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    SUBGOAL_THEN `(v:real^N) IN UNIONS s` MP_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
      UNDISCH_TAC `DISJOINT (UNIONS s) (complex_boundary (t:(real^N->bool)->bool))` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    DERIVED_NBHD_COMBINATORIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    SURFACE_NBHD_SIDES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `barycentric_subdivision (s:(real^N->bool)->bool)`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `L = barycentric_subdivision (barycentric_subdivision
                    (s:(real^N->bool)->bool))` THEN
  SUBGOAL_THEN `UNIONS (L:(real^N->bool)->bool) = UNIONS s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* L is a subcomplex of the neighbourhood complex *)
  SUBGOAL_THEN `simplicial_subcomplex L (derived_nbhd_complex t (s:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
      REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
      SUBGOAL_THEN `!r:real^N->bool. r IN L ==> r IN barycentric_subdivision
                                     (barycentric_subdivision t)` ASSUME_TAC THENL
       [UNDISCH_TAC `simplicial_subcomplex (L:(real^N->bool)->bool)
                       (barycentric_subdivision (barycentric_subdivision t))` THEN
        SIMP_TAC[simplicial_subcomplex; SUBSET];
        ALL_TAC] THEN
      ASM_CASES_TAC `q:real^N->bool = {}` THENL
       [SUBGOAL_THEN `?r:real^N->bool. r IN L /\ ~(r = {})` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `~(UNIONS s:real^N->bool = {})` THEN
          REWRITE_TAC[GSYM(ASSUME `UNIONS (L:(real^N->bool)->bool) = UNIONS s`)] THEN
          SET_TAC[];
          ALL_TAC] THEN
        EXISTS_TAC `r:real^N->bool` THEN ASM_SIMP_TAC[EMPTY_FACE_OF] THEN
        SUBGOAL_THEN `(r:real^N->bool) SUBSET UNIONS s` MP_TAC THENL
         [REWRITE_TAC[GSYM(ASSUME `UNIONS (L:(real^N->bool)->bool) = UNIONS s`)] THEN
          ASM SET_TAC[];
          ASM SET_TAC[]];
        EXISTS_TAC `q:real^N->bool` THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
         [SUBGOAL_THEN `(q:real^N->bool) SUBSET UNIONS s` MP_TAC THENL
           [REWRITE_TAC[GSYM(ASSUME `UNIONS (L:(real^N->bool)->bool) = UNIONS s`)] THEN
            ASM SET_TAC[];
            ASM SET_TAC[]];
          MATCH_MP_TAC FACE_OF_REFL THEN MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
          EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]];
      MAP_EVERY X_GEN_TAC [`r:real^N->bool`; `f:real^N->bool`] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold 2 (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    MP_TAC(ISPEC `s:(real^N->bool)->bool` MOI_FC2_BARYCENTRIC_CM2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `barycentric_subdivision (s:(real^N->bool)->bool)`
      MOI_FC2_BARYCENTRIC_CM2) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q:real^N->bool. q IN derived_nbhd_complex t s
                     ==> q INTER UNIONS L IN L /\ (q INTER UNIONS L) face_of q`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `UNIONS (L:(real^N->bool)->bool) =
                  UNIONS (barycentric_subdivision s)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "L" THEN MATCH_MP_TAC MOI_FRN_FULL THEN
    EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `simplicial_subcomplex (derived_nbhd_complex t (s:(real^N->bool)->bool))
                   (barycentric_subdivision (barycentric_subdivision t))` THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (UNIONS (L:(real^N->bool)->bool))
             (complex_boundary (derived_nbhd_complex t s))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[derived_frontier; frontier_of] THEN
    UNDISCH_TAC `UNIONS s SUBSET
                 subtopology euclidean (UNIONS t) interior_of
                 derived_nbhd t (s:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `DISJOINT (UNIONS s) (complex_boundary (t:(real^N->bool)->bool))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `components (derived_nbhd t s DIFF UNIONS (s:(real^N->bool)->bool))
                HAS_SIZE 2`
  MP_TAC THENL [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:real^N->bool` (X_CHOOSE_THEN `K2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`K1:real^N->bool`; `K2:real^N->bool`] THEN
  REWRITE_TAC[moi_fbc_split] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

(* The bicollar of a connected surface inside its derived neighbourhood.     *)

let MOI_FBC_CONNECTED_BICOLLAR = prove
 (`!(t:(real^N->bool)->bool) s.
     FINITE t /\ combinatorial_manifold_with_boundary 3 t /\
     simplicial_subcomplex s t /\ combinatorial_manifold 2 s /\
     connected (UNIONS s) /\ ~(UNIONS s = {}) /\
     DISJOINT (UNIONS s) (complex_boundary t) /\
     two_sided_in (UNIONS t) (UNIONS s)
     ==> ?w (p:real^(N,1)finite_sum->real^N) q.
           pl_homeomorphism (UNIONS s PCROSS interval[--vec 1:real^1,vec 1],w) (p,q) /\
           w SUBSET derived_nbhd t s /\
           UNIONS s SUBSET (subtopology euclidean (UNIONS t)) interior_of w /\
           !x. x IN UNIONS s ==> p(pastecart x (vec 0)) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FBC_DERIVED_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:real^N->bool` (X_CHOOSE_THEN `K2:real^N->bool`
    (MP_TAC o MATCH_MP MOI_FBC_SIDES_BICOLLAR))) THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `barycentric_subdivision (s:(real^N->bool)->bool)`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real^(N,1)finite_sum->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^N->real^(N,1)finite_sum` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FBC_INTERIOR_TRANS THEN
  EXISTS_TAC `derived_nbhd t (s:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Fine subdivisions (the derived neighbourhood inside a given relative      *)
(* neighbourhood, DERIVED_NBHD_SMALL), disjoint unions of bicollars, and the *)
(* bicollar of a closed two-sided surface subcomplex with any number of      *)
(* components.                                                               *)
(* ========================================================================= *)

(* 2D invariance (pc_moi_s28_tria/trib) at M = N.                           *)

let MOI_FBC_SURF_INVARIANT = prove
 (inst [`:N`,`:M`] MOI_S28_SURF_INVARIANT_BODY,
  ACCEPT_TAC(INST_TYPE [`:N`,`:M`]
    (MP SURF_INVARIANT (CONJ (INST_TYPE [`:M`,`:N`] SURF_CHARTS) SURF_LOCAL))));;

(* Iterated barycentric subdivisions of a combinatorial surface.            *)

let MOI_FBC_ITER_CM2 = prove
 (`!(s:(real^N->bool)->bool) n.
     FINITE s /\ combinatorial_manifold 2 s
     ==> FINITE (ITER n barycentric_subdivision s) /\
         combinatorial_manifold 2 (ITER n barycentric_subdivision s)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FC2_BARYCENTRIC_CM2 THEN ASM_REWRITE_TAC[]);;

(* A connected surface subcomplex: a bicollar inside any relative           *)
(* neighbourhood.                                                            *)

let MOI_FBC_FINE_CONNECTED = prove
 (`!(c:(real^N->bool)->bool) s v.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     simplicial_subcomplex s c /\ combinatorial_manifold 2 s /\
     connected (UNIONS s) /\ ~(UNIONS s = {}) /\
     DISJOINT (UNIONS s) (complex_boundary c) /\
     two_sided_in (UNIONS c) (UNIONS s) /\
     open_in (subtopology euclidean (UNIONS c)) v /\ UNIONS s SUBSET v
     ==> ?w (p:real^(N,1)finite_sum->real^N) q.
           pl_homeomorphism (UNIONS s PCROSS interval[--vec 1:real^1,vec 1],w) (p,q) /\
           w SUBSET v /\
           UNIONS s SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
           !x. x IN UNIONS s ==> p(pastecart x (vec 0)) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool) /\ simplicial_complex c`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary; MOI_SIMPLICIAL_COMPLEX_LF];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (s:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; FINITE_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:(real^N->bool)->bool`; `v:real^N->bool`]
    DERIVED_NBHD_SMALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `n:num`] MOI_FCL_ITER_CMWB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:(real^N->bool)->bool`; `n:num`]
    MOI_FDN_ITER_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `n:num`] MOI_FBC_ITER_CM2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ITER n barycentric_subdivision (c:(real^N->bool)->bool)`;
                 `ITER n barycentric_subdivision (s:(real^N->bool)->bool)`]
    MOI_FBC_CONNECTED_BICOLLAR) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real^(N,1)finite_sum->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^N->real^(N,1)finite_sum` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Two bicollars with disjoint images give one on the union.                *)

let MOI_FBC_DISJOINT_GLUE = prove
 (`!(s1:real^N->bool) s2 w1 w2 (p1:real^(N,1)finite_sum->real^N) q1 p2 q2.
     compact s1 /\ compact s2 /\ DISJOINT s1 s2 /\ DISJOINT w1 w2 /\
     pl_homeomorphism (s1 PCROSS interval[--vec 1:real^1,vec 1],w1) (p1,q1) /\
     pl_homeomorphism (s2 PCROSS interval[--vec 1:real^1,vec 1],w2) (p2,q2)
     ==> ?p q. pl_homeomorphism ((s1 UNION s2) PCROSS interval[--vec 1:real^1,vec 1],
                                 w1 UNION w2) (p,q) /\
               (!z. z IN s1 PCROSS interval[--vec 1,vec 1] ==> p z = p1 z) /\
               (!z. z IN s2 PCROSS interval[--vec 1,vec 1] ==> p z = p2 z)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (MP_TAC o GEN_REWRITE_RULE I [pl_homeomorphism])
                     (MP_TAC o GEN_REWRITE_RULE I [pl_homeomorphism])))))) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `h1 = (s1:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
  ABBREV_TAC `h2 = (s2:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
  ABBREV_TAC `p = \z:real^(N,1)finite_sum.
                    if fstcart z IN s1 then (p1:real^(N,1)finite_sum->real^N) z
                    else p2 z` THEN
  SUBGOAL_THEN
   `(!z. z IN h1 ==> (p:real^(N,1)finite_sum->real^N) z = p1 z) /\
    (!z. z IN h2 ==> p z = p2 z) /\
    compact (h1:real^(N,1)finite_sum->bool) /\ compact (h2:real^(N,1)finite_sum->bool) /\
    (s1 UNION s2) PCROSS interval[--vec 1:real^1,vec 1] = h1 UNION h2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "h1"; "h2"] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                PCROSS_UNION] THEN
    SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; ASSUME `compact (s1:real^N->bool)`;
             ASSUME `compact (s2:real^N->bool)`] THEN
    UNDISCH_TAC `DISJOINT (s1:real^N->bool) s2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (h1 UNION h2:real^(N,1)finite_sum->bool)
                          (p:real^(N,1)finite_sum->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_UNION THEN
    ASM_SIMP_TAC[CLOSED_SUBSET; SUBSET_UNION; COMPACT_IMP_CLOSED] THEN
    CONJ_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THENL
     [EXISTS_TAC `p1:real^(N,1)finite_sum->real^N`;
      EXISTS_TAC `p2:real^(N,1)finite_sum->real^N`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h1 UNION h2:real^(N,1)finite_sum->bool`;
                 `p:real^(N,1)finite_sum->real^N`] MOI_FCL_PLH_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_UNION] THEN
    MAP_EVERY X_GEN_TAC [`z1:real^(N,1)finite_sum`; `z2:real^(N,1)finite_sum`] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN
    UNDISCH_TAC `(p:real^(N,1)finite_sum->real^N) z1 = p z2` THEN
    ASM_SIMP_TAC[] THENL
     [DISCH_THEN(MP_TAC o AP_TERM `q1:real^N->real^(N,1)finite_sum`) THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `(p1:real^(N,1)finite_sum->real^N) z1 IN w1 /\
                    (p2:real^(N,1)finite_sum->real^N) z2 IN w2` MP_TAC THENL
       [ASM SET_TAC[];
        UNDISCH_TAC `DISJOINT (w1:real^N->bool) w2` THEN SET_TAC[]];
      SUBGOAL_THEN `(p2:real^(N,1)finite_sum->real^N) z1 IN w2 /\
                    (p1:real^(N,1)finite_sum->real^N) z2 IN w1` MP_TAC THENL
       [ASM SET_TAC[];
        UNDISCH_TAC `DISJOINT (w1:real^N->bool) w2` THEN SET_TAC[]];
      DISCH_THEN(MP_TAC o AP_TERM `q2:real^N->real^(N,1)finite_sum`) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:real^N->real^(N,1)finite_sum`) THEN
  MAP_EVERY EXISTS_TAC [`p:real^(N,1)finite_sum->real^N`;
                        `q:real^N->real^(N,1)finite_sum`] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `IMAGE (p:real^(N,1)finite_sum->real^N) (h1 UNION h2) = w1 UNION w2`
  (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[IMAGE_UNION] THEN BINOP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (p1:real^(N,1)finite_sum->real^N) h1` THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (p2:real^(N,1)finite_sum->real^N) h2` THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]]]);;

(* Finitely many bicollars with pairwise disjoint images.                   *)

let MOI_FBC_DISJOINT_UNIONS = prove
 (`!(s:A->bool) f. DISJOINT s (UNIONS f) <=> !t. t IN f ==> DISJOINT s t`,
  SET_TAC[]);;

let MOI_FBC_FAMILY_GLUE = prove
 (`!(W:(real^N->bool)->real^N->bool)
    (P:(real^N->bool)->real^(N,1)finite_sum->real^N)
    (Q:(real^N->bool)->real^N->real^(N,1)finite_sum) ff.
     FINITE ff /\
     (!C. C IN ff ==> compact C /\
                     pl_homeomorphism (C PCROSS interval[--vec 1:real^1,vec 1],W C)
                                      (P C,Q C)) /\
     (!C D. C IN ff /\ D IN ff /\ ~(C = D) ==> DISJOINT C D /\ DISJOINT (W C) (W D))
     ==> ?p q. pl_homeomorphism (UNIONS ff PCROSS interval[--vec 1:real^1,vec 1],
                                 UNIONS (IMAGE W ff)) (p,q) /\
               !C z. C IN ff /\ z IN C PCROSS interval[--vec 1,vec 1] ==> p z = P C z`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> a ==> b /\ c ==> d`] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY; UNIONS_0; IMAGE_CLAUSES; PCROSS_EMPTY] THEN
    MAP_EVERY EXISTS_TAC [`\z:real^(N,1)finite_sum. vec 0:real^N`;
                          `\y:real^N. vec 0:real^(N,1)finite_sum`] THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism; pl_map_on; NOT_IN_EMPTY;
                IMAGE_CLAUSES; CONTINUOUS_ON_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real^N->bool`; `ff:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)
    (LABEL_TAC "disj")) THEN
  REMOVE_THEN "ih" MP_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "disj" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p':real^(N,1)finite_sum->real^N`
    (X_CHOOSE_THEN `q':real^N->real^(N,1)finite_sum`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "agree")))) THEN
  MP_TAC(ISPECL [`C:real^N->bool`; `UNIONS ff:real^N->bool`;
                 `(W:(real^N->bool)->real^N->bool) C`;
                 `UNIONS (IMAGE (W:(real^N->bool)->real^N->bool) ff)`;
                 `(P:(real^N->bool)->real^(N,1)finite_sum->real^N) C`;
                 `(Q:(real^N->bool)->real^N->real^(N,1)finite_sum) C`;
                 `p':real^(N,1)finite_sum->real^N`; `q':real^N->real^(N,1)finite_sum`]
    MOI_FBC_DISJOINT_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_FBC_DISJOINT_UNIONS; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[];
      X_GEN_TAC `D:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "disj" (MP_TAC o SPECL [`C:real^N->bool`; `D:real^N->bool`]) THEN
      REWRITE_TAC[IN_INSERT] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `D:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "disj" (MP_TAC o SPECL [`C:real^N->bool`; `D:real^N->bool`]) THEN
      REWRITE_TAC[IN_INSERT] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^(N,1)finite_sum->real^N`
    (X_CHOOSE_THEN `q:real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`p:real^(N,1)finite_sum->real^N`;
                        `q:real^N->real^(N,1)finite_sum`] THEN
  ASM_REWRITE_TAC[UNIONS_INSERT; IMAGE_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`D:real^N->bool`; `z:real^(N,1)finite_sum`] THEN
  REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
   [ASM_SIMP_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(p':real^(N,1)finite_sum->real^N) z` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `p':real^(N,1)finite_sum->real^N`)) (concl th) &&
        can (find_term ((=) `p:real^(N,1)finite_sum->real^N`)) (concl th))) THEN
      SUBGOAL_THEN `(D:real^N->bool) PCROSS interval[--vec 1:real^1,vec 1] SUBSET
                    UNIONS ff PCROSS interval[--vec 1,vec 1]` MP_TAC THENL
       [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[];
        UNDISCH_TAC `(z:real^(N,1)finite_sum) IN D PCROSS interval[--vec 1,vec 1]` THEN
        SET_TAC[]];
      USE_THEN "agree" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* Pairwise disjoint compact sets have pairwise disjoint open neighbourhoods. *)

let MOI_FBC_SEPARATE = prove
 (`!ff:(real^N->bool)->bool.
     FINITE ff /\ (!C. C IN ff ==> compact C) /\
     (!C D. C IN ff /\ D IN ff /\ ~(C = D) ==> DISJOINT C D)
     ==> ?O. (!C. C IN ff ==> open (O C) /\ C SUBSET O C) /\
             (!C D. C IN ff /\ D IN ff /\ ~(C = D) ==> DISJOINT (O C) (O D))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!C:real^N->bool. C IN ff
        ==> ?d. &0 < d /\
                !x y. x IN C /\ y IN UNIONS (ff DELETE C) ==> d <= dist(x,y)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SEPARATE_COMPACT_CLOSED THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; COMPACT_IMP_CLOSED];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_DELETE; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:real^N` THEN
      MATCH_MP_TAC(TAUT `(p ==> ~q) ==> ~(p /\ q)`) THEN DISCH_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `D:real^N->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`C:real^N->bool`; `D:real^N->bool`] o
        check (fun th -> is_forall(concl th) &&
          can (find_term (fun tm -> try fst(dest_const tm) = "DISJOINT"
                                    with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])] THEN
  DISCH_THEN(X_CHOOSE_TAC `d:(real^N->bool)->real`) THEN
  EXISTS_TAC `\C:real^N->bool. UNIONS {ball(x:real^N,d C / &2) | x | x IN C}` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `C:real^N->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC; OPEN_BALL];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
      SUBGOAL_THEN `&0 < (d:(real^N->bool)->real) C` MP_TAC THENL
       [ASM_MESON_TAC[]; REAL_ARITH_TAC]];
    MAP_EVERY X_GEN_TAC [`C:real^N->bool`; `D:real^N->bool`] THEN STRIP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS;
                EXISTS_IN_GSPEC; IN_BALL] THEN
    X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(d:(real^N->bool)->real) C <= dist(x:real^N,y) /\
                  (d:(real^N->bool)->real) D <= dist(y:real^N,x)`
    MP_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(C:real^N->bool) IN ff`) o
          check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `d:(real^N->bool)->real`)) (concl th))) THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
        ASM_REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN EXISTS_TAC `D:real^N->bool` THEN
        ASM_MESON_TAC[];
        FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(D:real^N->bool) IN ff`) o
          check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `d:(real^N->bool)->real`)) (concl th))) THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
        ASM_REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN EXISTS_TAC `C:real^N->bool` THEN
        ASM_MESON_TAC[]];
      UNDISCH_TAC `dist(x:real^N,z) < d(C:real^N->bool) / &2` THEN
      UNDISCH_TAC `dist(y:real^N,z) < d(D:real^N->bool) / &2` THEN
      CONV_TAC NORM_ARITH]]);;

(* A finite union of convex sets has finitely many components.               *)

let MOI_FBC_FINITE_COMPONENTS = prove
 (`!K:(real^N->bool)->bool.
     FINITE K /\ (!s. s IN K ==> convex s) ==> FINITE (components (UNIONS K))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\s. connected_component (UNIONS K) (CHOICE s))
                    {s:real^N->bool | s IN K /\ ~(s = {})}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT] THEN
  REWRITE_TAC[SUBSET; components; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `c:real^N->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS K` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET connected_component (UNIONS K) x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_SIMP_TAC[CONVEX_CONNECTED] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
  UNDISCH_TAC `(s:real^N->bool) SUBSET connected_component (UNIONS K) x` THEN
  MP_TAC(ISPEC `s:real^N->bool` CHOICE_DEF) THEN ASM SET_TAC[]);;

(* A two-sided closed surface subcomplex, any number of components.         *)

let MOI_FBC_SUBCOMPLEX_BICOLLAR = prove
 (`!(c:(real^N->bool)->bool) s v.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     simplicial_subcomplex s c /\ combinatorial_manifold 2 s /\
     DISJOINT (UNIONS s) (complex_boundary c) /\
     two_sided_in (UNIONS c) (UNIONS s) /\
     open_in (subtopology euclidean (UNIONS c)) v /\ UNIONS s SUBSET v
     ==> ?w (p:real^(N,1)finite_sum->real^N) q.
           pl_homeomorphism (UNIONS s PCROSS interval[--vec 1:real^1,vec 1],w) (p,q) /\
           w SUBSET v /\
           UNIONS s SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
           !x. x IN UNIONS s ==> p(pastecart x (vec 0)) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (s:(real^N->bool)->bool) /\ lf_simplicial_complex s`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; FINITE_SUBSET; combinatorial_manifold];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS (s:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[MOI_FM3_LF_COMPACT]; ALL_TAC] THEN
  ABBREV_TAC `ff = components (UNIONS (s:(real^N->bool)->bool))` THEN
  SUBGOAL_THEN
   `FINITE (ff:(real^N->bool)->bool) /\ UNIONS ff = UNIONS s /\
    (!C. C IN ff ==> compact C /\ connected C /\ ~(C = {}) /\ C SUBSET UNIONS s) /\
    (!C D. C IN ff /\ D IN ff /\ ~(C = D) ==> DISJOINT C D)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ff" THEN REWRITE_TAC[GSYM UNIONS_COMPONENTS] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FBC_FINITE_COMPONENTS THEN ASM_MESON_TAC[MOI_FM3_LF_CONVEX];
      X_GEN_TAC `C:real^N->bool` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[IN_COMPONENTS_SUBSET] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_IN_COMPACT THEN
        EXISTS_TAC `UNIONS (s:(real^N->bool)->bool)` THEN
        ASM_SIMP_TAC[CLOSED_IN_COMPONENT];
        ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
        ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]];
      MESON_TAC[COMPONENTS_NONOVERLAP; DISJOINT]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `ff:(real^N->bool)->bool` MOI_FBC_SEPARATE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:(real^N->bool)->real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!C:real^N->bool. C IN ff
      ==> ?w (p:real^(N,1)finite_sum->real^N) q.
            pl_homeomorphism (C PCROSS interval[--vec 1:real^1,vec 1],w) (p,q) /\
            w SUBSET v INTER O C /\
            C SUBSET (subtopology euclidean (UNIONS c)) interior_of w /\
            !x. x IN C ==> p(pastecart x (vec 0)) = x`
  MP_TAC THENL
   [X_GEN_TAC `C:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `C:real^N->bool`] MOI_FCL_CM2_COMPONENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                   `{t:real^N->bool | t IN s /\ t SUBSET C}`;
                   `v INTER (O:(real^N->bool)->real^N->bool) C`]
      MOI_FBC_FINE_CONNECTED) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[simplicial_subcomplex; IN_ELIM_THM] THEN CONJ_TAC THENL
         [UNDISCH_TAC `simplicial_subcomplex (s:(real^N->bool)->bool) c` THEN
          REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
          MAP_EVERY X_GEN_TAC [`q:real^N->bool`; `f:real^N->bool`] THEN STRIP_TAC THEN
          CONJ_TAC THENL
           [ASM_MESON_TAC[simplicial_subcomplex];
            ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]]];
        ASM_SIMP_TAC[];
        ASM_SIMP_TAC[];
        UNDISCH_TAC `DISJOINT (UNIONS s) (complex_boundary (c:(real^N->bool)->bool))` THEN
        SUBGOAL_THEN `(C:real^N->bool) SUBSET UNIONS s` MP_TAC THENL
         [ASM_SIMP_TAC[]; SET_TAC[]];
        UNDISCH_TAC `two_sided_in (UNIONS c) (UNIONS (s:(real^N->bool)->bool))` THEN
        REWRITE_TAC[two_sided_in] THEN
        SUBGOAL_THEN `components (C:real^N->bool) = {C}` SUBST1_TAC THENL
         [ASM_SIMP_TAC[COMPONENTS_EQ_SING]; ALL_TAC] THEN
        REWRITE_TAC[IN_SING] THEN DISCH_THEN(MP_TAC o SPEC `C:real^N->bool`) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]];
        MATCH_MP_TAC OPEN_IN_INTER_OPEN THEN ASM_SIMP_TAC[];
        REWRITE_TAC[SUBSET_INTER] THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS (s:(real^N->bool)->bool)` THEN
        ASM_SIMP_TAC[]];
      SIMP_TAC[]];
    DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:(real^N->bool)->real^N->bool`
   (X_CHOOSE_THEN `P:(real^N->bool)->real^(N,1)finite_sum->real^N`
   (X_CHOOSE_THEN `Q:(real^N->bool)->real^N->real^(N,1)finite_sum`
    (LABEL_TAC "comp")))) THEN
  MP_TAC(ISPECL [`W:(real^N->bool)->real^N->bool`;
                 `P:(real^N->bool)->real^(N,1)finite_sum->real^N`;
                 `Q:(real^N->bool)->real^N->real^(N,1)finite_sum`;
                 `ff:(real^N->bool)->bool`] MOI_FBC_FAMILY_GLUE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`C:real^N->bool`; `D:real^N->bool`] THEN STRIP_TAC THEN
    USE_THEN "comp" (MP_TAC o C MATCH_MP (ASSUME `(C:real^N->bool) IN ff`)) THEN
    USE_THEN "comp" (MP_TAC o C MATCH_MP (ASSUME `(D:real^N->bool) IN ff`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`C:real^N->bool`; `D:real^N->bool`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `O:(real^N->bool)->real^N->bool`)) (concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "DISJOINT"
                                  with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^(N,1)finite_sum->real^N`
    (X_CHOOSE_THEN `q:real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`UNIONS (IMAGE (W:(real^N->bool)->real^N->bool) ff)`;
                        `p:real^(N,1)finite_sum->real^N`;
                        `q:real^N->real^(N,1)finite_sum`] THEN
  UNDISCH_TAC `pl_homeomorphism (UNIONS ff PCROSS interval[--vec 1,vec 1],
                UNIONS (IMAGE (W:(real^N->bool)->real^N->bool) ff))
               (p:real^(N,1)finite_sum->real^N,q)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `C:real^N->bool` THEN
    DISCH_TAC THEN USE_THEN "comp" (MP_TAC o C MATCH_MP (ASSUME `(C:real^N->bool) IN ff`)) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `UNIONS ff = UNIONS (s:(real^N->bool)->bool)`)) THEN
    REWRITE_TAC[UNIONS_SUBSET] THEN X_GEN_TAC `C:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(subtopology euclidean (UNIONS c)) interior_of
                ((W:(real^N->bool)->real^N->bool) C)` THEN
    CONJ_TAC THENL
     [USE_THEN "comp" (MP_TAC o C MATCH_MP (ASSUME `(C:real^N->bool) IN ff`)) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC INTERIOR_OF_MONO THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?C:real^N->bool. C IN ff /\ x IN C` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(P:(real^N->bool)->real^(N,1)finite_sum->real^N) C
                  (pastecart x (vec 0))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
      REAL_ARITH_TAC;
      USE_THEN "comp" (MP_TAC o C MATCH_MP (ASSUME `(C:real^N->bool) IN ff`)) THEN ASM_SIMP_TAC[]]]);;

(* ========================================================================= *)
(* SURFACE_BICOLLAR.  A simultaneous subdivision                             *)
(* (SIMPLICIAL_COMPLEX_REFINE_POLYTOPES of pc_moi_polytope) makes s a        *)
(* subcomplex; the manifold properties pass to the subdivisions through the  *)
(* identity map (COMBINATORIAL_WB_PL_INVARIANT, 2D invariance).              *)
(* ========================================================================= *)

let MOI_FBC_CM2_CMWB2 = prove
 (`!c:(real^N->bool)->bool.
     combinatorial_manifold 2 c ==> combinatorial_manifold_with_boundary 2 c`,
  REWRITE_TAC[combinatorial_manifold; combinatorial_manifold_with_boundary] THEN
  MESON_TAC[]);;

let SURFACE_BICOLLAR = prove
 (MOI_FND_BICOLLAR,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool) /\ simplicial_complex c /\
                lf_simplicial_complex (s:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary; combinatorial_manifold;
                  MOI_SIMPLICIAL_COMPLEX_LF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_POLYTOPE]; ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `FINITE (t:(real^N->bool)->bool) /\ lf_simplicial_complex t`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  ABBREV_TAC `s' = {r:real^N->bool | r IN t /\ ?k. k IN s /\ r SUBSET k}` THEN
  SUBGOAL_THEN `simplicial_subcomplex s' (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN REWRITE_TAC[simplicial_subcomplex; IN_ELIM_THM] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`r:real^N->bool`; `f:real^N->bool`] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_FACE];
      EXISTS_TAC `k:real^N->bool` THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS s' = UNIONS (s:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN SET_TAC[];
      REWRITE_TAC[UNIONS_SUBSET] THEN X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "UNIONS"
                                  with Failure _ -> false)) (concl th) &&
        can (find_term ((=) `s:(real^N->bool)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM SUBST1_TAC THEN REWRITE_TAC[UNIONS_SUBSET] THEN
      X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE `!x:real^N->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
      EXPAND_TAC "s'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `k:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (s':(real^N->bool)->bool) /\ simplicial_complex s'`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `FINITE (s':(real^N->bool)->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[simplicial_subcomplex];
      ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
      MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
      EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* t is a combinatorial 3-manifold with the same boundary *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:(real^N->bool)->bool`;
                 `\x:real^N. x`; `\x:real^N. x`] COMBINATORIAL_WB_PL_INVARIANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID] THEN
    REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_LF_COMPLEX THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_ID] THEN STRIP_TAC] THEN
  (* s' is a combinatorial surface *)
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `s':(real^N->bool)->bool`;
                 `\x:real^N. x`; `\x:real^N. x`] MOI_FBC_SURF_INVARIANT) THEN
  ASM_SIMP_TAC[MOI_FBC_CM2_CMWB2; HOMEOMORPHISM_ID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s':(real^N->bool)->bool`; `v:real^N->bool`]
    MOI_FBC_SUBCOMPLEX_BICOLLAR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `complex_boundary (t:(real^N->bool)->bool)`)) THEN
    ASM SET_TAC[];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* SURFACE_BICOLLAR_R3 from the corrected 26.6: a big 3-simplex around the   *)
(* surface (scaled CHOOSE_SURROUNDING_SIMPLEX_FULL), two-sidedness in real^3 *)
(* (TWO_SIDED_R3 of pc_moi_fnd_collar) restricted to the simplex, and        *)
(* SURFACE_BICOLLAR for the face complex of the simplex.                     *)
(* ========================================================================= *)

(* A full-dimensional simplex whose interior contains a given bounded set.  *)

let MOI_FBC_BIG_SIMPLEX = prove
 (`!s:real^N->bool.
     bounded s ==> ?k. &(dimindex(:N)) simplex k /\ s SUBSET interior k`,
  GEN_TAC THEN REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `vec 0:real^N` CHOOSE_SURROUNDING_SIMPLEX_FULL) THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR] o
    check (fun th -> try fst(dest_const(rator(rand(concl th)))) = "interior"
                     with Failure _ -> false)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\x:real^N. ((r + &1) / e) % x) k0` THEN
  SUBGOAL_THEN `&0 < (r + &1) / e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) SIMPLEX_LINEAR_IMAGE_EQ o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[LINEAR_SCALING; VECTOR_MUL_LCANCEL] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  EXISTS_TAC `inv((r + &1) / e) % (z:real^N)` THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(r + &1) / e * inv((r + &1) / e) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_MUL_LID]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
    try fst(dest_const(rator(lhand(concl th)))) = "ball" with Failure _ -> false)) THEN
  REWRITE_TAC[IN_BALL; DIST_0; NORM_MUL; REAL_ABS_INV] THEN
  SUBGOAL_THEN `norm(z:real^N) < r + &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(y:real^N) <= r` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `dist(y:real^N,z) < &1` THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(abs((r + &1) / e)) * norm(z:real^N) = (e * norm z) / (r + &1)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < r ==> &0 < r + &1`] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]);;

(* Two-sidedness in real^N passes to any subspace with the surface in its   *)
(* interior.                                                                 *)

let MOI_FBC_TWO_SIDED_SUBSPACE = prove
 (`!(y:real^N->bool) s.
     two_sided_in (:real^N) s /\ s SUBSET interior y ==> two_sided_in y s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[two_sided_in; SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool`) THEN ASM_REWRITE_TAC[GSYM OPEN_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET s` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `v INTER interior y:real^N->bool` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_SUBSET THEN ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN
    MP_TAC(ISPEC `y:real^N->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ASM SET_TAC[];
    X_GEN_TAC `w:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `k SUBSET (subtopology euclidean y) interior_of (w:real^N->bool)` THEN
    REWRITE_TAC[SUBSET; interior_of; IN_ELIM_THM; OPEN_IN_OPEN; GSYM OPEN_IN] THEN
    DISCH_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `oo:real^N->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `oo INTER interior y:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN
    MP_TAC(ISPEC `y:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]]);;

(* SURFACE_BICOLLAR_R3.                                                      *)

let SURFACE_BICOLLAR_R3 = prove
 (MOI_FND_BICOLLAR_R3,
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`s:(real^3->bool)->bool`; `u:real^3->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `s:(real^3->bool)->bool`
    (MATCH_MP TWO_SIDED_R3 (ASSUME `MOISE_266_STATEMENT`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (s:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS (s:(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[MOI_FM3_LF_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPEC `UNIONS s:real^3->bool` MOI_FBC_BIG_SIMPLEX) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; DIMINDEX_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`&3:int`; `k:real^3->bool`] MOI_FMB_FACE_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (k:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k = k DIFF interior (k:real^3->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `relative_interior k = interior (k:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
      REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN
      ASM_MESON_TAC[AFF_DIM_SIMPLEX];
      ALL_TAC] THEN
    ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{f:real^3->bool | f face_of k}`; `s:(real^3->bool)->bool`;
                 `u INTER interior k:real^3->bool`] SURFACE_BICOLLAR) THEN
  ASM_SIMP_TAC[MOI_FMB_FACE_COMPLEX_CMWB; MOI_FMB_FACE_COMPLEX_CB] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_POLYTOPE_FACES THEN ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      MP_TAC(ISPEC `k:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      MATCH_MP_TAC MOI_FBC_TWO_SIDED_SUBSPACE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_SUBSET THEN ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN
      MP_TAC(ISPEC `k:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^3->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real^(3,1)finite_sum->real^3` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^3->real^(3,1)finite_sum` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `UNIONS s SUBSET (subtopology euclidean k) interior_of (w:real^3->bool)` THEN
  REWRITE_TAC[SUBSET; interior_of; IN_ELIM_THM; OPEN_IN_OPEN] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[IN_INTERIOR] THEN
  SUBGOAL_THEN `open (oo INTER interior k:real^3->bool) /\ x IN oo INTER interior k`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> concl th = `open (oo INTER interior k:real^3->bool)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `k:real^3->bool` INTERIOR_SUBSET) THEN
  ASM SET_TAC[]);;


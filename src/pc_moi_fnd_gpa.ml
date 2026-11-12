(* ========================================================================= *)
(* pc_moi_fnd_gpa: general position of PL maps of polyhedra of dimension     *)
(* at most 2 into real^3 (Moise GTM 47, 26.4 proof (a)-(b) p.193, 26.6       *)
(* proof (2)-(5) p.194, 33.1 Lemma 10 p.235).  Main theorem                  *)
(* GENERAL_POSITION_MAP_3 (the term MOI_FND_GP_MAP_3 of pc_moi_fnd_stmt.ml). *)
(*                                                                           *)
(* Route.  The map f is uniformly continuous on the compact polyhedron.     *)
(* Iterated derived subdivisions whose new vertices are generic points      *)
(* near the barycentres (stellar steps over maximal simplices, pc_moi_cone   *)
(* lemmas) give fine subdivisions; inside the fixed polyhedron UNIONS k0    *)
(* the new vertices avoid finitely many proper affine subspaces, which keeps *)
(* the images of all small simplices there in general position.  The last  *)
(* step makes k0 full.  The values at the free vertices are then moved      *)
(* generically within e/2, and f' is the simplexwise affine interpolation.  *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_real.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_fnd_dn.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A. General position algebra in real^3.                                    *)
(* ------------------------------------------------------------------------- *)

(* The dimension formula for the affine hulls of two sets that meet.        *)

let MOI_FGP_AFF_DIM_HULLS_UNION = prove
 (`!s t:real^N->bool.
        ~(affine hull s INTER affine hull t = {})
        ==> aff_dim (s UNION t) =
            (aff_dim s + aff_dim t) -
            aff_dim (affine hull s INTER affine hull t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`affine hull s:real^N->bool`; `affine hull t:real^N->bool`]
    AFF_DIM_UNION) THEN
  ASM_REWRITE_TAC[AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM AFF_DIM_AFFINE_HULL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM AFF_DIM_AFFINE_HULL] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC HULL_UNION);;

(* Full affine hull from the dimension count.                               *)

let MOI_FGP_AFF_DIM_3_UNIV = prove
 (`!s:real^3->bool. aff_dim s = &3 <=> affine hull s = (:real^3)`,
  REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3]);;

(* Every set is in general position with the whole space.                   *)

let MOI_FGP_GP_UNIV = prove
 (`!q:real^3->bool. affine_gp_3 (:real^3) q`,
  GEN_TAC THEN REWRITE_TAC[affine_gp_3] THEN
  ASM_CASES_TAC `q:real^3->bool = {}` THEN
  ASM_REWRITE_TAC[DISJOINT_EMPTY] THEN DISJ2_TAC THEN
  REWRITE_TAC[AFF_DIM_UNIV; DIMINDEX_3; AFFINE_HULL_UNIV; INTER_UNIV;
              AFF_DIM_AFFINE_HULL] THEN
  MP_TAC(ISPEC `q:real^3->bool` AFF_DIM_POS_LE) THEN ASM_REWRITE_TAC[] THEN
  INT_ARITH_TAC);;

(* If s meets q in general position, the affine hull of s and q is all of  *)
(* real^3.                                                                    *)

let MOI_FGP_GP_MEET_UNIV = prove
 (`!s q:real^3->bool.
        affine_gp_3 s q /\ ~(s INTER q = {})
        ==> affine hull (s UNION q) = (:real^3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[affine_gp_3; DISJOINT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM MOI_FGP_AFF_DIM_3_UNIV] THEN
  SUBGOAL_THEN `~(affine hull s INTER affine hull q:real^3->bool = {})`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `s:real^3->bool`] HULL_SUBSET) THEN
    MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `q:real^3->bool`] HULL_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FGP_AFF_DIM_HULLS_UNION] THEN ASM_ARITH_TAC);;

(* The general position step: adding a point p of a convex set P (in        *)
(* general position with q) to a convex set s0 (in general position with q) *)
(* keeps general position, provided p avoids the affine hull of s0 and q   *)
(* unless that hull already contains the affine hull of P.                  *)

let MOI_FGP_GP_ADD_IN = prove
 (`!(s0:real^3->bool) q p P.
        convex P /\ s0 SUBSET P /\ p IN P /\ affine_gp_3 P q /\
        affine hull P SUBSET affine hull (s0 UNION q)
        ==> affine_gp_3 (convex hull (p INSERT s0)) q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[affine_gp_3] THEN
  ASM_CASES_TAC `DISJOINT (convex hull (p INSERT s0)) (q:real^3->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `convex hull (p INSERT s0) SUBSET (P:real^3->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(P INTER q:real^3->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `~DISJOINT (convex hull (p INSERT s0)) (q:real^3->bool)` THEN
    UNDISCH_TAC `convex hull (p INSERT s0) SUBSET (P:real^3->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull (P UNION q) = (:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FGP_GP_MEET_UNIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `affine hull (s0 UNION q) = (:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_UNIV] THEN
    UNDISCH_TAC `affine hull (P UNION q) = (:real^3)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[AFFINE_AFFINE_HULL; UNION_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `affine hull P:real^3->bool` THEN
      ASM_REWRITE_TAC[HULL_SUBSET];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `s0 UNION q:real^3->bool` THEN
      REWRITE_TAC[HULL_SUBSET] THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `S = convex hull ((p:real^3) INSERT s0)` THEN
  SUBGOAL_THEN `affine hull (S UNION q) = (:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_UNIV] THEN
    UNDISCH_TAC `affine hull (s0 UNION q) = (:real^3)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC HULL_MONO THEN
    MATCH_MP_TAC(SET_RULE
     `(s:real^3->bool) SUBSET t ==> s UNION q SUBSET t UNION q`) THEN
    EXPAND_TAC "S" THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(p:real^3) INSERT s0` THEN
    REWRITE_TAC[HULL_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(affine hull S INTER affine hull q:real^3->bool = {})`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `S:real^3->bool`]
      HULL_SUBSET) THEN
    MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `q:real^3->bool`]
      HULL_SUBSET) THEN
    UNDISCH_TAC `~DISJOINT (S:real^3->bool) q` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `q:real^3->bool`]
    MOI_FGP_AFF_DIM_HULLS_UNION) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `affine hull (S UNION q) = (:real^3)` THEN
  REWRITE_TAC[GSYM MOI_FGP_AFF_DIM_3_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPEC `affine hull S INTER affine hull q:real^3->bool`
    AFF_DIM_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_FGP_GP_ADD_OUT = prove
 (`!(s0:real^3->bool) q p.
        convex s0 /\ affine_gp_3 s0 q /\ ~(p IN affine hull (s0 UNION q))
        ==> affine_gp_3 (convex hull (p INSERT s0)) q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[affine_gp_3] THEN DISJ1_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `q SUBSET affine hull (s0 UNION q:real^3->bool) /\
                s0 SUBSET affine hull (s0 UNION q)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `s0 UNION q:real^3->bool` THEN
    REWRITE_TAC[HULL_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `s0:real^3->bool = {}` THENL
   [UNDISCH_TAC `(x:real^3) IN convex hull (p INSERT s0)` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull s0 = s0:real^3->bool` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_HULL_EQ]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^3) IN convex hull (p INSERT s0)` THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT; IN_ELIM_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `v:real`; `b:real^3`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `u = &0` THENL
   [SUBGOAL_THEN `x:real^3 = b` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `v = &1` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `affine hull (s0 UNION q) = (:real^3)` MP_TAC THENL
     [MATCH_MP_TAC MOI_FGP_GP_MEET_UNIV THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `~((p:real^3) IN affine hull (s0 UNION q))` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `p:real^3 = inv u % x + (&1 - inv u) % b` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `v = &1 - u` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `s0 UNION q:real^3->bool` AFFINE_AFFINE_HULL) THEN
  REWRITE_TAC[affine] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; REAL_ARITH_TAC]);;

let MOI_FGP_GP_ADD = prove
 (`!(s0:real^3->bool) q p P.
        convex s0 /\ convex P /\ s0 SUBSET P /\ p IN P /\
        affine_gp_3 s0 q /\ affine_gp_3 P q /\
        (p IN affine hull (s0 UNION q)
         ==> affine hull P SUBSET affine hull (s0 UNION q))
        ==> affine_gp_3 (convex hull (p INSERT s0)) q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(p:real^3) IN affine hull (s0 UNION q)` THENL
   [MATCH_MP_TAC MOI_FGP_GP_ADD_IN THEN EXISTS_TAC `P:real^3->bool` THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_FGP_GP_ADD_OUT THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* B. Generic points: a nonempty relatively open subset of an affine hull   *)
(* is not covered by finitely many affine sets not containing the hull.     *)
(* ------------------------------------------------------------------------- *)

let MOI_FGP_AVOID_AFFINE = prove
 (`!fs (t:real^N->bool).
        FINITE fs /\ (!a. a IN fs ==> affine a /\ ~(affine hull t SUBSET a))
        ==> !u. open_in (subtopology euclidean (affine hull t)) u /\
                ~(u = {})
                ==> ?x. x IN u /\ !a. a IN fs ==> ~(x IN a)`,
  GEN_TAC THEN GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  UNDISCH_TAC `FINITE (fs:(real^N->bool)->bool)` THEN
  SPEC_TAC(`fs:(real^N->bool)->bool`,`fs:(real^N->bool)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY; GSYM MEMBER_NOT_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `fs:(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "rest")) THEN
  X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
  USE_THEN "rest" (fun th -> REMOVE_THEN "ih" (MP_TAC o C MP th)) THEN
  DISCH_THEN(MP_TAC o SPEC `u DIFF a:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `u DIFF a:real^N->bool =
                    u INTER (affine hull t DIFF a)` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
        REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN SET_TAC[];
        MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN ASM_SIMP_TAC[CLOSED_AFFINE]];
      DISCH_TAC THEN
      UNDISCH_TAC `~(affine hull t SUBSET (a:real^N->bool))` THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`u:real^N->bool`; `t:real^N->bool`] AFFINE_HULL_OPEN_IN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    REWRITE_TAC[IN_DIFF] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* C1. Injective affine maps on a simplex keep the vertices affinely         *)
(* independent.                                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_FGP_AFFINE_HULL_AFFINE_IMAGE = prove
 (`!(l:real^M->real^N) y s.
        linear l
        ==> affine hull (IMAGE (\x. l x + y) s) =
            IMAGE (\x. l x + y) (affine hull s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t. IMAGE (\x. (l:real^M->real^N) x + y) t =
                    IMAGE (\x. y + x) (IMAGE l t)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    REWRITE_TAC[VECTOR_ADD_SYM];
    ASM_SIMP_TAC[AFFINE_HULL_TRANSLATION; AFFINE_HULL_LINEAR_IMAGE]]);;

let MOI_FGP_INJ_AFFINE_INDEPENDENT = prove
 (`!(f:real^M->real^N) l y v.
        linear l /\ ~affine_dependent v /\
        (!x. x IN convex hull v ==> f x = l x + y) /\
        (!x x'. x IN convex hull v /\ x' IN convex hull v /\ f x = f x'
                ==> x = x')
        ==> ~affine_dependent (IMAGE f v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN v ==> (x:real^M) IN convex hull v` ASSUME_TAC THENL
   [MESON_TAC[HULL_INC]; ALL_TAC] THEN
  UNDISCH_TAC `affine_dependent (IMAGE (f:real^M->real^N) v)` THEN
  REWRITE_TAC[affine_dependent; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `IMAGE (f:real^M->real^N) v DELETE f x0 =
    IMAGE (\x. l x + y) (v DELETE x0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DELETE; IN_IMAGE] THEN
    X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `w:real^M` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      EXISTS_TAC `w:real^M` THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `w:real^M` STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL
       [EXISTS_TAC `w:real^M` THEN ASM_SIMP_TAC[];
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  UNDISCH_TAC
   `(f:real^M->real^N) x0 IN affine hull (IMAGE f v DELETE f x0)` THEN
  ASM_SIMP_TAC[MOI_FGP_AFFINE_HULL_AFFINE_IMAGE; IN_IMAGE; NOT_EXISTS_THM] THEN
  X_GEN_TAC `z:real^M` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(z:real^M = x0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~affine_dependent (v:real^M->bool)` THEN
    REWRITE_TAC[affine_dependent] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^M->real^N) (z - x0) = vec 0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_SUB] THEN
    UNDISCH_TAC `(l:real^M->real^N) x0 + y = l z + y` THEN
    CONV_TAC VECTOR_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `?b:real^M. b IN relative_interior (convex hull v)`
  MP_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; CONVEX_CONVEX_HULL] THEN
    REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR; AFFINE_HULL_CONVEX_HULL] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `d:real^M = z - x0` THEN
  SUBGOAL_THEN `&0 < norm(d:real^M)` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `c = e / (&2 * norm(d:real^M))` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c * norm(d:real^M) = e / &2` ASSUME_TAC THENL
   [MP_TAC(ASSUME `&0 < norm(d:real^M)`) THEN EXPAND_TAC "c" THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^M) + c % d IN convex hull v` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_INTER; IN_BALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[NORM_ARITH `dist(b:real^M,b + x) = norm x`; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "d" THEN MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
      REWRITE_TAC[AFFINE_AFFINE_HULL] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(z:real^M) IN affine hull (v DELETE x0)` THEN
        SPEC_TAC(`z:real^M`,`z:real^M`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
        MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^M) + c % d = b` MP_TAC THENL
   [UNDISCH_TAC
     `!x x'. x IN convex hull v /\ x' IN convex hull v /\
             (f:real^M->real^N) x = f x' ==> x = x'` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `b + c % d:real^M = b <=> c % d = vec 0`] THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0; DE_MORGAN_THM] THEN
  REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* C2. The stellar step with an explicit centre: if l0 subdivides the       *)
(* complex l with a maximal simplex t removed, then coning the part of l0   *)
(* in the relative frontier of t from any b in the relative interior of t   *)
(* subdivides l (the proof of MOI_CON_EXTEND_STEP_CONE of pc_moi_cone, with *)
(* the centre a parameter and without the relative part).                   *)
(* ------------------------------------------------------------------------- *)

let moi_fgp_stellar = new_definition
 `moi_fgp_stellar (l0:(real^N->bool)->bool) t (b:real^N) =
    l0 UNION {convex hull (b INSERT s) |
              s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}`;;

let MOI_FGP_STELLAR = prove
 (`!(l:(real^N->bool)->bool) t l0 b.
     simplicial_complex l /\ t IN l /\ (!u. u IN l /\ t SUBSET u ==> u = t) /\
     simplicial_complex l0 /\ UNIONS l0 = UNIONS (l DELETE t) /\
     (!s. s IN l0 ==> ?t'. t' IN l DELETE t /\ s SUBSET t') /\
     (!t'. t' IN l DELETE t ==> ?e. e SUBSET l0 /\ t' = UNIONS e) /\
     b IN relative_interior t /\ ~(relative_frontier t = {})
     ==> simplicial_complex (moi_fgp_stellar l0 t b) /\
         UNIONS (moi_fgp_stellar l0 t b) = UNIONS l /\
         (!s. s IN moi_fgp_stellar l0 t b ==> ?t'. t' IN l /\ s SUBSET t') /\
         (!t'. t' IN l ==> ?e. e SUBSET moi_fgp_stellar l0 t b /\
                               t' = UNIONS e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_fgp_stellar] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_CON_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
  SUBGOAL_THEN `convex (t:real^N->bool) /\ closed t /\ compact t`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l0:(real^N->bool)->bool`; `t:real^N->bool`; `n:int`]
    MOI_CON_RF_SUBCOMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC
     `!t':real^N->bool. t' IN l DELETE t ==> ?e. e SUBSET l0 /\ t' = UNIONS e`
    THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    MATCH_MP_TAC MOI_CON_SC_FACE THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`{s:real^N->bool | s IN l0 /\ s SUBSET relative_frontier t}`;
    `t:real^N->bool`; `n:int`; `b:real^N`] MOI_CON_CONE_OVER_RF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u:real^N->bool. u IN l0 ==> u INTER t SUBSET relative_frontier t`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
    UNDISCH_TAC
     `!s:real^N->bool. s IN l0 ==> ?t'. t' IN l DELETE t /\ s SUBSET t'` THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:real^N->bool`;
                   `w:real^N->bool`] MOI_CON_INTER_MAXIMAL_RF) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(u:real^N->bool) SUBSET w` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s u:real^N->bool.
        s IN {s | s IN l0 /\ s SUBSET relative_frontier t} /\ u IN l0
        ==> convex hull (b INSERT s) INTER u = s INTER u`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_CON_CONE_INTER_OUTSIDE THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_CON_SC_CONVEX THEN
      EXISTS_TAC `l0:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CON_GLUE_CONE THEN ASM_REWRITE_TAC[SUBSET_RESTRICT];
    SUBGOAL_THEN `UNIONS l = t UNION UNIONS (l DELETE (t:real^N->bool))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `(t:real^N->bool) IN l` THEN SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`{s:real^N->bool | s IN l0 /\ s SUBSET relative_frontier t}`;
      `l0:(real^N->bool)->bool`] SUBSET_UNIONS) THEN
    REWRITE_TAC[SUBSET_RESTRICT] THEN
    UNDISCH_TAC `UNIONS l0 = UNIONS (l DELETE (t:real^N->bool))` THEN
    UNDISCH_TAC
     `UNIONS ({s | s IN l0 /\ s SUBSET relative_frontier t} UNION
       {convex hull ((b:real^N) INSERT s) |
        s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}) = t` THEN
    REWRITE_TAC[UNIONS_UNION] THEN
    SPEC_TAC(`UNIONS {convex hull ((b:real^N) INSERT s) |
                      s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}`,
             `C:real^N->bool`) THEN
    SPEC_TAC(`UNIONS {s:real^N->bool | s IN l0 /\
                                      s SUBSET relative_frontier t}`,
             `Ks:real^N->bool`) THEN
    SPEC_TAC(`UNIONS (l DELETE (t:real^N->bool))`, `X:real^N->bool`) THEN
    SPEC_TAC(`UNIONS l0:real^N->bool`, `A:real^N->bool`) THEN SET_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [UNDISCH_TAC
       `!s:real^N->bool. s IN l0 ==> ?t'. t' IN l DELETE t /\ s SUBSET t'` THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN MESON_TAC[];
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `UNIONS ({s | s IN l0 /\ s SUBSET relative_frontier t} UNION
         {convex hull ((b:real^N) INSERT s) |
          s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}) = t` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
      ASM_REWRITE_TAC[IN_UNION]];
    X_GEN_TAC `t':real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `t':real^N->bool = t` THENL
     [EXISTS_TAC
       `{s:real^N->bool | s IN l0 /\ s SUBSET relative_frontier t} UNION
        {convex hull ((b:real^N) INSERT s) |
         s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      UNDISCH_TAC
       `!t':real^N->bool. t' IN l DELETE t ==> ?e. e SUBSET l0 /\ t' = UNIONS e`
      THEN DISCH_THEN(MP_TAC o SPEC `t':real^N->bool`) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN MATCH_MP_TAC MONO_EXISTS THEN
      SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* D1. Carriers in a subcomplex, barycentre distances, affine images.       *)
(* ------------------------------------------------------------------------- *)

(* A convex set inside a simplex of k whose relative interior meets the      *)
(* polyhedron of the subcomplex k0 lies in a single simplex of k0.          *)

let MOI_FGP_CARRIER = prove
 (`!(k:(real^M->bool)->bool) k0 r u x.
        simplicial_complex k /\ simplicial_subcomplex k0 k /\
        r IN k /\ u SUBSET r /\ x IN relative_interior u /\ x IN UNIONS k0
        ==> ?r0. r0 IN k0 /\ u SUBSET r0`,
  REWRITE_TAC[simplicial_subcomplex; IN_UNIONS] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `t:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `r INTER t:real^M->bool` THEN
  REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
  EXISTS_TAC `r:real^M->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
  EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[IN_INTER] THEN
  ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]);;

let MOI_FGP_CARRIER_SUBSET = prove
 (`!(k:(real^M->bool)->bool) k0 r u.
        simplicial_complex k /\ simplicial_subcomplex k0 k /\
        r IN k /\ u SUBSET r /\ convex u /\ ~(u = {}) /\ u SUBSET UNIONS k0
        ==> ?r0. r0 IN k0 /\ u SUBSET r0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x:real^M. x IN relative_interior u` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FGP_CARRIER THEN
  MAP_EVERY EXISTS_TAC [`k:(real^M->bool)->bool`; `r:real^M->bool`;
                        `x:real^M`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]);;

(* Points of a simplex of dimension at most 2 are within 2/3 of its         *)
(* diameter from the barycentre.                                             *)

let MOI_FGP_BARYCENTRE_DIST = prove
 (`!n (t:real^N->bool) y.
        n simplex t /\ aff_dim t <= &2 /\ y IN t
        ==> dist(simplex_barycentre t,y) <= &2 / &3 * diameter t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(t:real^N->bool) = n` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  UNDISCH_TAC `n simplex (t:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE (c:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(c:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(y:real^N) IN t` THEN ASM_REWRITE_TAC[CONVEX_HULL_EMPTY] THEN
    REWRITE_TAC[NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(c:real^N->bool) <= 3 /\ 1 <= CARD c` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; CARD_EQ_0]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`CARD(c:real^N->bool) - 1`; `c:real^N->bool`; `y:real^N`]
    MOI_BAR_BARYCENTRE_HULL_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_BAR_SIMPLEX_BARYCENTRE_HULL; DIAMETER_CONVEX_HULL] THEN
  REWRITE_TAC[dist; NORM_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN `CARD(c:real^N->bool) - 1 = 0 \/ CARD c - 1 = 1 \/
                  CARD c - 1 = 2`
    STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    MATCH_MP_TAC DIAMETER_POS_LE THEN ASM_SIMP_TAC[FINITE_IMP_BOUNDED]]);;

let MOI_FGP_CONVEX_AFFINE_IMAGE = prove
 (`!(l:real^M->real^N) c s.
        linear l /\ convex s ==> convex (IMAGE (\x. l x + c) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\x. (l:real^M->real^N) x + c) s =
                IMAGE (\x. c + x) (IMAGE l s)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN REWRITE_TAC[VECTOR_ADD_SYM];
    MATCH_MP_TAC CONVEX_TRANSLATION THEN
    MATCH_MP_TAC CONVEX_LINEAR_IMAGE THEN ASM_REWRITE_TAC[]]);;

let MOI_FGP_AFFINE_PREIMAGE = prove
 (`!(l:real^M->real^N) c a.
        linear l /\ affine a ==> affine {x | l x + c IN a}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[affine; IN_ELIM_THM] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `x':real^M`; `u:real`; `v:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(l:real^M->real^N) (u % x + v % x') + c =
    u % (l x + c) + v % (l x' + c)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
    SUBGOAL_THEN `v = &1 - u` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* D2. Derived subdivisions with generic centres.  moi_fgp_dsub k0 sc f l l' *)
(* says that l' subdivides l, has mesh at most 3/4 of l relative to every   *)
(* containing simplex, every nonempty simplex has a vertex in the relative  *)
(* interior of a containing simplex of l (fullness), and the f-images of    *)
(* its simplices inside UNIONS k0 are in general position with sc.          *)
(* ------------------------------------------------------------------------- *)

let moi_fgp_dsub = new_definition
 `moi_fgp_dsub (k0:(real^M->bool)->bool) (sc:(real^3->bool)->bool)
               (f:real^M->real^3) l l' <=>
    simplicial_complex l' /\ UNIONS l' = UNIONS l /\
    (!v. v IN l' ==> ?u. u IN l /\ v SUBSET u) /\
    (!u. u IN l ==> ?e. e SUBSET l' /\ u = UNIONS e) /\
    (!v u. v IN l' /\ u IN l /\ v SUBSET u
           ==> diameter v <= &3 / &4 * diameter u) /\
    (!v. v IN l' /\ ~(v = {})
         ==> ?x u. x extreme_point_of v /\ u IN l /\ v SUBSET u /\
                   x IN relative_interior u) /\
    (!v q. v IN l' /\ v SUBSET UNIONS k0 /\ q IN sc
           ==> affine_gp_3 (IMAGE f v) q)`;;

(* Adding the empty simplex and an isolated vertex to a complex.            *)

let MOI_FGP_SC_INSERT_ISOLATED = prove
 (`!(l0:(real^N->bool)->bool) a.
        simplicial_complex l0 /\ ~(a IN UNIONS l0)
        ==> simplicial_complex ({} INSERT {a} INSERT l0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT] THEN
  CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `-- &1:int` THEN REWRITE_TAC[SIMPLEX_EMPTY];
      EXISTS_TAC `&0:int` THEN REWRITE_TAC[SIMPLEX_SING]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`g:real^N->bool`; `s:real^N->bool`] THEN
    REWRITE_TAC[IN_INSERT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN STRIP_TAC THENL
     [ASM_MESON_TAC[FACE_OF_EMPTY];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
      REWRITE_TAC[SET_RULE `s SUBSET {a:real^N} <=> s = {} \/ s = {a}`] THEN
      MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN l0 ==> {a} INTER s = {} /\ s INTER {a} = {}`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[INTER_EMPTY; EMPTY_FACE_OF; INTER_IDEMPOT; FACE_OF_REFL;
               CONVEX_SING]);;

(* ------------------------------------------------------------------------- *)
(* D3. The derived subdivision step at an isolated vertex.                  *)
(* ------------------------------------------------------------------------- *)

let MOI_FGP_DSUB_ISOLATED = prove
 (`!(k0:(real^M->bool)->bool) (sc:(real^3->bool)->bool) (f:real^M->real^3)
    c l0 a.
        simplicial_complex c /\ {a} IN c /\
        (!u. u IN c /\ {a} SUBSET u ==> u = {a}) /\
        (!u q. u IN c /\ u SUBSET UNIONS k0 /\ q IN sc
               ==> affine_gp_3 (IMAGE f u) q) /\
        moi_fgp_dsub k0 sc f (c DELETE {a}) l0
        ==> moi_fgp_dsub k0 sc f c ({} INSERT {a} INSERT l0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fgp_dsub] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((a:real^M) IN UNIONS l0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^M->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~(w:real^M->bool = {a})` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `!u:real^M->bool. u IN c /\ {a} SUBSET u ==> u = {a}` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[SING_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^M->bool. u IN c ==> &0 <= diameter u` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DIAMETER_POS_LE THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC MOI_CON_SC_COMPACT THEN
    EXISTS_TAC `c:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FGP_SC_INSERT_ISOLATED THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[UNIONS_INSERT; UNION_EMPTY] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{a:real^M} IN c` THEN
    SPEC_TAC(`{a:real^M}`,`t:real^M->bool`) THEN SET_TAC[];
    REWRITE_TAC[FORALL_IN_INSERT] THEN CONJ_TAC THENL
     [EXISTS_TAC `{a:real^M}` THEN ASM_REWRITE_TAC[EMPTY_SUBSET];
      CONJ_TAC THENL
       [EXISTS_TAC `{a:real^M}` THEN ASM_REWRITE_TAC[SUBSET_REFL];
        X_GEN_TAC `v:real^M->bool` THEN DISCH_TAC THEN
        UNDISCH_TAC
         `!v:real^M->bool. v IN l0 ==> ?u. u IN c DELETE {a} /\ v SUBSET u` THEN
        DISCH_THEN(MP_TAC o SPEC `v:real^M->bool`) THEN
        ASM_REWRITE_TAC[IN_DELETE] THEN MESON_TAC[]]];
    X_GEN_TAC `u:real^M->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `u = {a:real^M}` THENL
     [EXISTS_TAC `{{a:real^M}}` THEN ASM_REWRITE_TAC[UNIONS_1] THEN SET_TAC[];
      UNDISCH_TAC
       `!u:real^M->bool. u IN c DELETE {a}
                         ==> ?e. e SUBSET l0 /\ u = UNIONS e` THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^M->bool`) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN MATCH_MP_TAC MONO_EXISTS THEN
      SET_TAC[]];
    REWRITE_TAC[IN_INSERT] THEN
    MAP_EVERY X_GEN_TAC [`v:real^M->bool`; `u:real^M->bool`] THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[DIAMETER_EMPTY] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[DIAMETER_SING] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_CASES_TAC `u = {a:real^M}` THENL
       [SUBGOAL_THEN `v:real^M->bool = {} \/ v = {a}` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `(v:real^M->bool) SUBSET u` THEN ASM_REWRITE_TAC[] THEN
          SET_TAC[];
          ASM_REWRITE_TAC[DIAMETER_EMPTY] THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `u:real^M->bool`) THEN
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          ASM_REWRITE_TAC[DIAMETER_SING] THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `u:real^M->bool`) THEN
          ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
        UNDISCH_TAC
         `!v u:real^M->bool.
            v IN l0 /\ u IN c DELETE {a} /\ v SUBSET u
            ==> diameter v <= &3 / &4 * diameter u` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE]]];
    REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `v:real^M->bool` THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `~(v:real^M->bool = {})` THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`a:real^M`; `{a:real^M}`] THEN
      ASM_REWRITE_TAC[EXTREME_POINT_OF_SING; RELATIVE_INTERIOR_SING; IN_SING;
                      SUBSET_REFL];
      UNDISCH_TAC
       `!v:real^M->bool.
          v IN l0 /\ ~(v = {})
          ==> ?x u. x extreme_point_of v /\ u IN c DELETE {a} /\
                    v SUBSET u /\ x IN relative_interior u` THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^M->bool`) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN MESON_TAC[]];
    REWRITE_TAC[IN_INSERT] THEN
    MAP_EVERY X_GEN_TAC [`v:real^M->bool`; `q:real^3->bool`] THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; affine_gp_3; DISJOINT_EMPTY];
      UNDISCH_TAC
       `!u q. u IN c /\ u SUBSET UNIONS k0 /\ q IN sc
              ==> affine_gp_3 (IMAGE (f:real^M->real^3) u) q` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(v:real^M->bool) SUBSET UNIONS k0` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC
       `!v q. v IN l0 /\ v SUBSET UNIONS k0 /\ q IN sc
              ==> affine_gp_3 (IMAGE (f:real^M->real^3) v) q` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* D4. The derived subdivision step at a maximal simplex t of dimension at  *)
(* least 1, coning from a centre b: mesh, fullness and general position.    *)
(* ------------------------------------------------------------------------- *)

let MOI_FGP_STELLAR_MESH = prove
 (`!(c:(real^N->bool)->bool) t l0 b.
        simplicial_complex c /\ t IN c /\
        (!u. u IN c /\ t SUBSET u ==> u = t) /\
        (!u. u IN c ==> aff_dim u <= &2) /\
        (!v. v IN l0 ==> ?u. u IN c DELETE t /\ v SUBSET u) /\
        (!v u. v IN l0 /\ u IN c DELETE t /\ v SUBSET u
               ==> diameter v <= &3 / &4 * diameter u) /\
        b IN relative_interior t /\
        dist(b,simplex_barycentre t) <= diameter t / &12
        ==> !v u. v IN moi_fgp_stellar l0 t b /\ u IN c /\ v SUBSET u
                  ==> diameter v <= &3 / &4 * diameter u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_CON_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
  SUBGOAL_THEN `bounded (t:real^N->bool) /\ convex t /\ closed t`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED;
                  SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^N->bool. u IN c ==> bounded u` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_CON_SC_COMPACT; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier t SUBSET (t:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N->bool. v IN l0 /\ v SUBSET t
                     ==> diameter v <= &3 / &4 * diameter t`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC
     `!v:real^N->bool. v IN l0 ==> ?u. u IN c DELETE t /\ v SUBSET u` THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N->bool`) THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(t INTER w:real^N->bool) IN c` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_CON_SC_FACE THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_MESON_TAC[MOI_CON_SC_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(t INTER w:real^N->bool = t)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(w:real^N->bool = t)` THEN
      REWRITE_TAC[] THEN
      UNDISCH_TAC `!u:real^N->bool. u IN c /\ t SUBSET u ==> u = t` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `t INTER w:real^N->bool = t` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 / &4 * diameter (t INTER w:real^N->bool)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC
       `!v u:real^N->bool.
          v IN l0 /\ u IN c DELETE t /\ v SUBSET u
          ==> diameter v <= &3 / &4 * diameter u` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE; SUBSET_INTER];
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC DIAMETER_SUBSET THEN ASM_REWRITE_TAC[INTER_SUBSET]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN t ==> dist(b,y) <= &3 / &4 * diameter t`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`n:int`; `t:real^N->bool`; `y:real^N`]
      MOI_FGP_BARYCENTRE_DIST) THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`b:real^N`; `simplex_barycentre t:real^N`; `y:real^N`]
      DIST_TRIANGLE) THEN
    UNDISCH_TAC `dist(b:real^N,simplex_barycentre t) <= diameter t / &12` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= diameter(t:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DIAMETER_POS_LE]; ALL_TAC] THEN
  REWRITE_TAC[moi_fgp_stellar; IN_UNION; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`v:real^N->bool`; `u:real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN STRIP_TAC THENL
   [ASM_CASES_TAC `u:real^N->bool = t` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC
       `!v:real^N->bool. v IN l0 /\ v SUBSET t
                         ==> diameter v <= &3 / &4 * diameter t` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC
       `!v u:real^N->bool.
          v IN l0 /\ u IN c DELETE t /\ v SUBSET u
          ==> diameter v <= &3 / &4 * diameter u` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(b:real^N) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET t` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^N->bool) SUBSET u` ASSUME_TAC THENL
   [SUBGOAL_THEN `(b:real^N) IN u` ASSUME_TAC THENL
     [UNDISCH_TAC `convex hull ((b:real^N) INSERT s) SUBSET u` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`;
                   `t:real^N->bool`] MOI_CON_SC_INTER) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `u INTER t:real^N->bool = t` THENL
     [UNDISCH_TAC `u INTER t:real^N->bool = t` THEN SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`u INTER t:real^N->bool`; `t:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(b:real^N) IN relative_interior t` THEN
    UNDISCH_TAC `(b:real^N) IN u` THEN UNDISCH_TAC `(b:real^N) IN t` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &4 * diameter(t:real^N->bool)`
  THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC DIAMETER_SUBSET THEN ASM_SIMP_TAC[]]] THEN
  REWRITE_TAC[DIAMETER_CONVEX_HULL] THEN MATCH_MP_TAC DIAMETER_LE THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; IN_INSERT] THEN
  SUBGOAL_THEN `bounded(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[GSYM dist] THEN
    UNDISCH_TAC `!y:real^N. y IN t ==> dist(b,y) <= &3 / &4 * diameter t` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
    ASM_REWRITE_TAC[GSYM dist] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    UNDISCH_TAC `!y:real^N. y IN t ==> dist(b,y) <= &3 / &4 * diameter t` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `diameter(s:real^N->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC
       `!v:real^N->bool. v IN l0 /\ v SUBSET t
                         ==> diameter v <= &3 / &4 * diameter t` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let MOI_FGP_STELLAR_TOP = prove
 (`!(c:(real^N->bool)->bool) t l0 b.
        simplicial_complex l0 /\ t IN c /\ convex t /\ closed t /\
        (!v. v IN l0 /\ ~(v = {})
             ==> ?x u. x extreme_point_of v /\ u IN c DELETE t /\
                       v SUBSET u /\ x IN relative_interior u) /\
        b IN relative_interior t
        ==> !v. v IN moi_fgp_stellar l0 t b /\ ~(v = {})
                ==> ?x u. x extreme_point_of v /\ u IN c /\ v SUBSET u /\
                          x IN relative_interior u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[moi_fgp_stellar; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `v:real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN STRIP_TAC THENL
   [UNDISCH_TAC
     `!v:real^N->bool.
        v IN l0 /\ ~(v = {})
        ==> ?x u. x extreme_point_of v /\ u IN c DELETE t /\
                  v SUBSET u /\ x IN relative_interior u` THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N->bool`) THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`b:real^N`; `t:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(b:real^N) IN t /\ (s:real^N->bool) SUBSET t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; SUBSET_TRANS]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC HULL_MINIMAL THEN ASM SET_TAC[]] THEN
  MP_TAC(ISPECL [`l0:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_CON_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[simplex; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:int`; `w:real^N->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ONCE_REWRITE_TAC[GSYM HULL_INSERT] THEN
  MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL_INSERT THEN
  CONJ_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  UNDISCH_TAC `convex hull w SUBSET relative_frontier (t:real^N->bool)` THEN
  UNDISCH_TAC `(b:real^N) IN relative_interior t` THEN
  REWRITE_TAC[relative_frontier] THEN SET_TAC[]);;

let MOI_FGP_STELLAR_GP = prove
 (`!(k:(real^M->bool)->bool) k0 (sc:(real^3->bool)->bool) (f:real^M->real^3)
    c t l0 b.
        simplicial_complex k /\ simplicial_subcomplex k0 k /\
        (!r. r IN k0 ==> ?l y. linear l /\ !x. x IN r ==> f x = l x + y) /\
        (!u. u IN c ==> ?r. r IN k /\ u SUBSET r) /\
        (!u q. u IN c /\ u SUBSET UNIONS k0 /\ q IN sc
               ==> affine_gp_3 (IMAGE f u) q) /\
        t IN c /\ convex t /\ closed t /\
        (!v. v IN l0 ==> convex v) /\
        (!v q. v IN l0 /\ v SUBSET UNIONS k0 /\ q IN sc
               ==> affine_gp_3 (IMAGE f v) q) /\
        b IN relative_interior t /\
        (t SUBSET UNIONS k0
         ==> !s q. s IN l0 /\ s SUBSET relative_frontier t /\ q IN sc /\
                   f b IN affine hull (IMAGE f s UNION q)
                   ==> affine hull (IMAGE f t) SUBSET
                       affine hull (IMAGE f s UNION q))
        ==> !v q. v IN moi_fgp_stellar l0 t b /\ v SUBSET UNIONS k0 /\
                  q IN sc
                  ==> affine_gp_3 (IMAGE f v) q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[moi_fgp_stellar; IN_UNION; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`v:real^M->bool`; `q:real^3->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN STRIP_TAC THENL
   [UNDISCH_TAC
     `!v q. v IN l0 /\ v SUBSET UNIONS k0 /\ q IN sc
            ==> affine_gp_3 (IMAGE (f:real^M->real^3) v) q` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(b:real^M) IN t /\ (s:real^M->bool) SUBSET t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^M) IN UNIONS k0 /\ s SUBSET UNIONS k0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `convex hull ((b:real^M) INSERT s) SUBSET UNIONS k0` THEN
    MP_TAC(ISPECL [`convex:(real^M->bool)->bool`; `(b:real^M) INSERT s`]
      HULL_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r0:real^M->bool. r0 IN k0 /\ t SUBSET r0` STRIP_ASSUME_TAC
  THENL
   [UNDISCH_TAC `!u:real^M->bool. u IN c ==> ?r. r IN k /\ u SUBSET r` THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^M->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FGP_CARRIER THEN
    MAP_EVERY EXISTS_TAC [`k:(real^M->bool)->bool`; `r:real^M->bool`;
                          `b:real^M`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t SUBSET UNIONS (k0:(real^M->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real^M->bool) SUBSET r0` THEN
    UNDISCH_TAC `(r0:real^M->bool) IN k0` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `!r:real^M->bool. r IN k0
         ==> ?l y. linear l /\ !x. x IN r ==> (f:real^M->real^3) x = l x + y` THEN
  DISCH_THEN(MP_TAC o SPEC `r0:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^M->real^3`
    (X_CHOOSE_THEN `Y:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x:real^M. x IN t ==> f x = (L:real^M->real^3) x + Y`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull ((b:real^M) INSERT s) SUBSET t` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^M->bool. w SUBSET t
                     ==> IMAGE (f:real^M->real^3) w = IMAGE (\x. L x + Y) w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> (f:real^M->real^3) x = g x) ==> IMAGE f s = IMAGE g s`)
    THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^M->real^3) (convex hull (b INSERT s)) =
    convex hull (f b INSERT IMAGE f s)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[MOI_REAL_AFFINE_IMAGE_CONVEX_HULL] THEN
    REWRITE_TAC[IMAGE_CLAUSES] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FGP_GP_ADD THEN
  EXISTS_TAC `IMAGE (f:real^M->real^3) t` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC MOI_FGP_CONVEX_AFFINE_IMAGE THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[SUBSET_REFL] THEN MATCH_MP_TAC MOI_FGP_CONVEX_AFFINE_IMAGE THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC
     `!v q. v IN l0 /\ v SUBSET UNIONS k0 /\ q IN sc
            ==> affine_gp_3 (IMAGE (f:real^M->real^3) v) q` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC
     `!u q. u IN c /\ u SUBSET UNIONS k0 /\ q IN sc
            ==> affine_gp_3 (IMAGE (f:real^M->real^3) u) q` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    UNDISCH_TAC
     `t SUBSET UNIONS k0
      ==> !s q. s IN l0 /\ s SUBSET relative_frontier t /\ q IN sc /\
                (f:real^M->real^3) b IN affine hull (IMAGE f s UNION q)
                ==> affine hull (IMAGE f t) SUBSET
                    affine hull (IMAGE f s UNION q)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_FGP_DSUB_STELLAR = prove
 (`!(k:(real^M->bool)->bool) k0 (sc:(real^3->bool)->bool) (f:real^M->real^3)
    c t l0 b.
        simplicial_complex k /\ simplicial_subcomplex k0 k /\
        (!r. r IN k0 ==> ?l y. linear l /\ !x. x IN r ==> f x = l x + y) /\
        simplicial_complex c /\ (!u. u IN c ==> ?r. r IN k /\ u SUBSET r) /\
        (!u. u IN c ==> aff_dim u <= &2) /\
        (!u q. u IN c /\ u SUBSET UNIONS k0 /\ q IN sc
               ==> affine_gp_3 (IMAGE f u) q) /\
        t IN c /\ (!u. u IN c /\ t SUBSET u ==> u = t) /\
        ~(relative_frontier t = {}) /\
        moi_fgp_dsub k0 sc f (c DELETE t) l0 /\
        b IN relative_interior t /\
        dist(b,simplex_barycentre t) <= diameter t / &12 /\
        (t SUBSET UNIONS k0
         ==> !s q. s IN l0 /\ s SUBSET relative_frontier t /\ q IN sc /\
                   f b IN affine hull (IMAGE f s UNION q)
                   ==> affine hull (IMAGE f t) SUBSET
                       affine hull (IMAGE f s UNION q))
        ==> moi_fgp_dsub k0 sc f c (moi_fgp_stellar l0 t b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_fgp_dsub k0 sc (f:real^M->real^3) (c DELETE t) l0` THEN
  REWRITE_TAC[moi_fgp_dsub] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^M->bool)->bool`; `t:real^M->bool`]
    MOI_CON_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
  SUBGOAL_THEN `convex (t:real^M->bool) /\ closed t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^M->bool)->bool`; `t:real^M->bool`;
                 `l0:(real^M->bool)->bool`; `b:real^M`] MOI_FGP_STELLAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FGP_STELLAR_MESH THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FGP_STELLAR_TOP THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FGP_STELLAR_GP THEN
    MAP_EVERY EXISTS_TAC [`k:(real^M->bool)->bool`; `c:(real^M->bool)->bool`]
    THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_CON_SC_CONVEX]]);;

(* ------------------------------------------------------------------------- *)
(* D5. Choice of a generic centre near the barycentre; the induction.      *)
(* ------------------------------------------------------------------------- *)

let MOI_FGP_CHOOSE_CENTRE = prove
 (`!(k:(real^M->bool)->bool) k0 (sc:(real^3->bool)->bool) (f:real^M->real^3)
    c t (l0:(real^M->bool)->bool).
        simplicial_complex k /\ simplicial_subcomplex k0 k /\
        (!r. r IN k0 ==> ?l y. linear l /\ !x. x IN r ==> f x = l x + y) /\
        FINITE sc /\ FINITE l0 /\
        simplicial_complex c /\ (!u. u IN c ==> ?r. r IN k /\ u SUBSET r) /\
        t IN c /\ ~(relative_frontier t = {})
        ==> ?b. b IN relative_interior t /\
                dist(b,simplex_barycentre t) <= diameter t / &12 /\
                (t SUBSET UNIONS k0
                 ==> !s q. s IN l0 /\ s SUBSET relative_frontier t /\
                           q IN sc /\ f b IN affine hull (IMAGE f s UNION q)
                           ==> affine hull (IMAGE f t) SUBSET
                               affine hull (IMAGE f s UNION q))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^M->bool)->bool`; `t:real^M->bool`]
    MOI_CON_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
  SUBGOAL_THEN `convex (t:real^M->bool) /\ bounded t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT;
                  COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real^M->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(relative_frontier {}:real^M->bool = {})` THEN
    REWRITE_TAC[RELATIVE_FRONTIER_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < diameter(t:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN
    ASM_SIMP_TAC[DIAMETER_POS_LE; DIAMETER_EQ_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^M` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `~(relative_frontier {a:real^M} = {})` THEN
    REWRITE_TAC[RELATIVE_FRONTIER_EQ_EMPTY; AFFINE_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (t:real^M->bool) IN relative_interior t`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `t SUBSET UNIONS (k0:(real^M->bool)->bool)` THENL
   [ALL_TAC;
    EXISTS_TAC `simplex_barycentre (t:real^M->bool)` THEN
    ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `?r0:real^M->bool. r0 IN k0 /\ t SUBSET r0` STRIP_ASSUME_TAC
  THENL
   [UNDISCH_TAC `!u:real^M->bool. u IN c ==> ?r. r IN k /\ u SUBSET r` THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^M->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FGP_CARRIER_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`k:(real^M->bool)->bool`; `r:real^M->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `!r:real^M->bool. r IN k0
         ==> ?l y. linear l /\ !x. x IN r ==> (f:real^M->real^3) x = l x + y` THEN
  DISCH_THEN(MP_TAC o SPEC `r0:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^M->real^3`
    (X_CHOOSE_THEN `Y:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x:real^M. x IN t ==> f x = (L:real^M->real^3) x + Y`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (\p:(real^M->bool)#(real^3->bool).
       if affine hull (IMAGE (f:real^M->real^3) t) SUBSET
          affine hull (IMAGE f (FST p) UNION SND p)
       then {}
       else {x:real^M | (L:real^M->real^3) x + Y IN
                        affine hull (IMAGE f (FST p) UNION SND p)})
           (l0 CROSS sc)`;
    `t:real^M->bool`] MOI_FGP_AVOID_AFFINE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_CROSS] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
    MAP_EVERY X_GEN_TAC [`s:real^M->bool`; `q:real^3->bool`] THEN
    STRIP_TAC THEN COND_CASES_TAC THENL
     [REWRITE_TAC[AFFINE_EMPTY; SUBSET_EMPTY; AFFINE_HULL_EQ_EMPTY] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FGP_AFFINE_PREIMAGE THEN
      ASM_REWRITE_TAC[AFFINE_AFFINE_HULL];
      ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC
     `~(affine hull (IMAGE (f:real^M->real^3) t) SUBSET
        affine hull (IMAGE f s UNION q))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[AFFINE_AFFINE_HULL; SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC
     `affine hull t SUBSET
      {x:real^M | (L:real^M->real^3) x + Y IN
                  affine hull (IMAGE (f:real^M->real^3) s UNION q)}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[HULL_INC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
   `relative_interior t INTER
    ball(simplex_barycentre t,diameter t / &12):real^M->bool`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER_OPEN THEN
      REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR; OPEN_BALL];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `simplex_barycentre (t:real^M->bool)` THEN
      ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_BALL; FORALL_IN_IMAGE; FORALL_PAIR_THM;
              IN_CROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `b:real^M` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^M->bool`; `q:real^3->bool`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC
   `affine hull (IMAGE (f:real^M->real^3) t) SUBSET
    affine hull (IMAGE f s UNION q)` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^M->bool`; `q:real^3->bool`]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `(b:real^M) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_FGP_MAXIMAL_EXISTS = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ (?s. s IN c /\ ~(s = {}))
        ==> ?t. t IN c /\ ~(t = {}) /\ !u. u IN c /\ t SUBSET u ==> u = t`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `{u:real^N->bool | u IN c /\ ~(u = {})} = {}` MP_TAC THENL
   [MATCH_MP_TAC FINITE_TRANSITIVITY_CHAIN THEN
    EXISTS_TAC `(PSUBSET):(real^N->bool)->(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; PSUBSET_IRREFL] THEN
    CONJ_TAC THENL [MESON_TAC[PSUBSET_TRANS]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^N->bool` THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N->bool` o
      REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(y:real^N->bool = {})` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N->bool) SUBSET y` THEN
      UNDISCH_TAC `~(x:real^N->bool = {})` THEN SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `y:real^N->bool` THEN ASM_REWRITE_TAC[PSUBSET] THEN
    ASM_MESON_TAC[];
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o
      ONCE_REWRITE_RULE[EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY]]);;

let MOI_FGP_DSUB_TRIVIAL = prove
 (`!(k0:(real^M->bool)->bool) (sc:(real^3->bool)->bool) (f:real^M->real^3) c.
        simplicial_complex c /\ (!u. u IN c ==> u = {})
        ==> moi_fgp_dsub k0 sc f c c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_fgp_dsub] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[SUBSET_REFL];
    X_GEN_TAC `u:real^M->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `{u:real^M->bool}` THEN ASM_REWRITE_TAC[UNIONS_1] THEN
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `v:real^M->bool = {} /\ u:real^M->bool = {}` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[DIAMETER_EMPTY] THEN REAL_ARITH_TAC];
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `v:real^M->bool = {}` SUBST1_TAC THENL
     [ASM_MESON_TAC[];
      REWRITE_TAC[IMAGE_CLAUSES; affine_gp_3; DISJOINT_EMPTY]]]);;

let MOI_FGP_DERIVED = prove
 (`!(k:(real^M->bool)->bool) k0 (sc:(real^3->bool)->bool) (f:real^M->real^3)
    c.
        simplicial_complex k /\ simplicial_subcomplex k0 k /\
        (!r. r IN k0 ==> ?l y. linear l /\ !x. x IN r ==> f x = l x + y) /\
        FINITE sc /\
        simplicial_complex c /\ (!u. u IN c ==> ?r. r IN k /\ u SUBSET r) /\
        (!u. u IN c ==> aff_dim u <= &2) /\
        (!u q. u IN c /\ u SUBSET UNIONS k0 /\ q IN sc
               ==> affine_gp_3 (IMAGE f u) q)
        ==> ?c'. moi_fgp_dsub k0 sc f c c'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  SPEC_TAC(`c:(real^M->bool)->bool`,`c:(real^M->bool)->bool`) THEN
  SUBGOAL_THEN
   `!n c. CARD (c:(real^M->bool)->bool) = n /\
          simplicial_complex c /\ (!u. u IN c ==> ?r. r IN k /\ u SUBSET r) /\
          (!u. u IN c ==> aff_dim u <= &2) /\
          (!u q. u IN c /\ u SUBSET UNIONS k0 /\ q IN sc
                 ==> affine_gp_3 (IMAGE (f:real^M->real^3) u) q)
          ==> ?c'. moi_fgp_dsub k0 sc f c c'`
   (fun th -> GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC th THEN
              EXISTS_TAC `CARD(c:(real^M->bool)->bool)` THEN
              ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  X_GEN_TAC `c:(real^M->bool)->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `!u:real^M->bool. u IN c ==> u = {}` THENL
   [EXISTS_TAC `c:(real^M->bool)->bool` THEN
    MATCH_MP_TAC MOI_FGP_DSUB_TRIVIAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (c:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPEC `c:(real^M->bool)->bool` MOI_FGP_MAXIMAL_EXISTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `simplicial_complex (c DELETE (t:real^M->bool))` ASSUME_TAC
  THENL
   [MATCH_MP_TAC MOI_CON_SC_DELETE_MAXIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?l0. moi_fgp_dsub k0 sc (f:real^M->real^3) (c DELETE t) l0`
  STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "ih" (MP_TAC o SPEC `CARD (c DELETE (t:real^M->bool))`) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[CARD_DELETE] THEN
      SUBGOAL_THEN `~(CARD (c:(real^M->bool)->bool) = 0)` MP_TAC THENL
       [ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[]; ASM_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `c DELETE (t:real^M->bool)`) THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `relative_frontier t:real^M->bool = {}` THENL
   [SUBGOAL_THEN `?a:real^M. t = {a}` (X_CHOOSE_THEN `a:real^M` SUBST_ALL_TAC)
    THENL
     [MP_TAC(ISPEC `t:real^M->bool` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[RELATIVE_FRONTIER_EQ_EMPTY]; ALL_TAC] THEN
      SUBGOAL_THEN `bounded (t:real^M->bool)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[MOI_CON_SC_COMPACT; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `{} INSERT {a:real^M} INSERT l0` THEN
    MATCH_MP_TAC MOI_FGP_DSUB_ISOLATED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `k0:(real^M->bool)->bool`;
                 `sc:(real^3->bool)->bool`; `f:real^M->real^3`;
                 `c:(real^M->bool)->bool`; `t:real^M->bool`;
                 `l0:(real^M->bool)->bool`] MOI_FGP_CHOOSE_CENTRE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_fgp_dsub k0 sc (f:real^M->real^3) (c DELETE t) l0` THEN
    REWRITE_TAC[moi_fgp_dsub] THEN MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `moi_fgp_stellar l0 t (b:real^M)` THEN
  MATCH_MP_TAC MOI_FGP_DSUB_STELLAR THEN
  EXISTS_TAC `k:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* E1. Iterated generic derived subdivisions: fine subdivisions of k whose  *)
(* simplices inside UNIONS k0 have images in general position.             *)
(* ------------------------------------------------------------------------- *)

let MOI_FGP_ITER = prove
 (`!(k:(real^M->bool)->bool) k0 (sc:(real^3->bool)->bool) (f:real^M->real^3)
    D.
        simplicial_complex k /\ simplicial_subcomplex k0 k /\
        (!r. r IN k ==> aff_dim r <= &2) /\
        (!r. r IN k0 ==> (?l y. linear l /\ !x. x IN r ==> f x = l x + y) /\
                         (!q. q IN sc ==> affine_gp_3 (IMAGE f r) q)) /\
        FINITE sc /\ (!r. r IN k ==> diameter r <= D)
        ==> !n. ?c. simplicial_complex c /\ UNIONS c = UNIONS k /\
                    (!u. u IN c ==> ?r. r IN k /\ u SUBSET r) /\
                    (!r. r IN k ==> ?e. e SUBSET c /\ r = UNIONS e) /\
                    (!u. u IN c ==> aff_dim u <= &2 /\
                                    diameter u <= (&3 / &4) pow n * D) /\
                    (!u q. u IN c /\ u SUBSET UNIONS k0 /\ q IN sc
                           ==> affine_gp_3 (IMAGE f u) q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [EXISTS_TAC `k:(real^M->bool)->bool` THEN
    ASM_SIMP_TAC[real_pow; REAL_MUL_LID] THEN REPEAT CONJ_TAC THENL
     [MESON_TAC[SUBSET_REFL];
      X_GEN_TAC `r:real^M->bool` THEN DISCH_TAC THEN
      EXISTS_TAC `{r:real^M->bool}` THEN ASM_REWRITE_TAC[UNIONS_1] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`u:real^M->bool`; `q:real^3->bool`] THEN
    STRIP_TAC THEN ASM_CASES_TAC `u:real^M->bool = {}` THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; affine_gp_3; DISJOINT_EMPTY]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `k0:(real^M->bool)->bool`;
                   `u:real^M->bool`; `u:real^M->bool`]
      MOI_FGP_CARRIER_SUBSET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_MESON_TAC[MOI_CON_SC_CONVEX];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real^M->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(u:real^M->bool) IN k0` ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_subcomplex k0 (k:(real^M->bool)->bool)` THEN
      REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `r0:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `u:real^M->bool`;
                     `r0:real^M->bool`] MOI_CON_SC_INTER) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `u INTER r0:real^M->bool = u` (fun th -> SIMP_TAC[th]) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `k0:(real^M->bool)->bool`;
                 `sc:(real^3->bool)->bool`; `f:real^M->real^3`;
                 `c:(real^M->bool)->bool`] MOI_FGP_DERIVED) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':(real^M->bool)->bool` MP_TAC) THEN
  REWRITE_TAC[moi_fgp_dsub] THEN STRIP_TAC THEN
  EXISTS_TAC `c':(real^M->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS];
    X_GEN_TAC `r:real^M->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `{v:real^M->bool | v IN c' /\ v SUBSET r}` THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC; SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    UNDISCH_TAC `!r:real^M->bool. r IN k ==> ?e. e SUBSET c /\ r = UNIONS e` THEN
    DISCH_THEN(MP_TAC o SPEC `r:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(x:real^M) IN r` THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `!u:real^M->bool. u IN c ==> ?e. e SUBSET c' /\ u = UNIONS e` THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^M->bool`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e':(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(x:real^M) IN u` THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^M->bool) SUBSET u /\ u SUBSET UNIONS e`
      MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `r:real^M->bool = UNIONS e` THEN SET_TAC[];
    X_GEN_TAC `v:real^M->bool` THEN DISCH_TAC THEN
    UNDISCH_TAC `!v:real^M->bool. v IN c' ==> ?u. u IN c /\ v SUBSET u` THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim(u:real^M->bool)` THEN
      ASM_SIMP_TAC[AFF_DIM_SUBSET];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 / &4 * diameter(u:real^M->bool)` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* E2. Adding one generic point to an affinely independent set of at most   *)
(* two points in general position keeps general position.                  *)
(* ------------------------------------------------------------------------- *)

let MOI_FGP_ADD_VERTEX = prove
 (`!(A:real^3->bool) p (sc:(real^3->bool)->bool) X.
        FINITE A /\ CARD A <= 2 /\ ~affine_dependent A /\
        (!q. q IN sc ==> ?n. n simplex q) /\
        (!q. q IN sc ==> affine_gp_3 (convex hull A) q) /\
        A SUBSET X /\ (!q. q IN sc ==> {x | x extreme_point_of q} SUBSET X) /\
        (!Y. Y SUBSET X /\ ~(affine hull Y = (:real^3))
             ==> ~(p IN affine hull Y))
        ==> ~(p IN A) /\ ~affine_dependent (p INSERT A) /\
            (!q. q IN sc ==> affine_gp_3 (convex hull (p INSERT A)) q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((p:real^3) IN affine hull A)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MOI_FGP_AFF_DIM_3_UNIV] THEN
    MP_TAC(ISPEC `A:real^3->bool` AFF_DIM_LE_CARD) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `CARD(A:real^3->bool) <= 2` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[HULL_INSERT] THEN
  MATCH_MP_TAC MOI_FGP_GP_ADD THEN EXISTS_TAC `(:real^3)` THEN
  REWRITE_TAC[CONVEX_CONVEX_HULL; CONVEX_UNIV; SUBSET_UNIV; IN_UNIV;
              MOI_FGP_GP_UNIV; AFFINE_HULL_UNIV] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `affine hull (convex hull A UNION q) =
    affine hull (A UNION {x:real^3 | x extreme_point_of q})`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[HULL_UNION] THEN REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN
    SUBGOAL_THEN
     `affine hull q = affine hull (convex hull {x:real^3 | x extreme_point_of q})`
     (fun th -> REWRITE_TAC[th; AFFINE_HULL_CONVEX_HULL]) THEN
    AP_TERM_TAC THEN ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC
   `affine hull (A UNION {x:real^3 | x extreme_point_of q}) = (:real^3)` THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `A UNION {x:real^3 | x extreme_point_of q}` o
    check (fun th -> is_forall (concl th) &&
                     can (find_term ((=) `(:real^3)`)) (concl th))) THEN
  ASM_SIMP_TAC[UNION_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* E3. Generic perturbation of the values at the free vertices.             *)
(* ------------------------------------------------------------------------- *)

let MOI_FGP_PERTURB_STEP_V = prove
 (`!(g:real^M->real^3) w p v (sc:(real^3->bool)->bool) X.
        FINITE v /\ CARD v <= 3 /\ w IN v /\
        ~affine_dependent (IMAGE g (v DELETE w)) /\
        (!x y. x IN v DELETE w /\ y IN v DELETE w /\ g x = g y ==> x = y) /\
        (!q. q IN sc ==> affine_gp_3 (convex hull (IMAGE g (v DELETE w))) q) /\
        (!q. q IN sc ==> ?n. n simplex q) /\
        IMAGE g (v DELETE w) SUBSET X /\
        (!q. q IN sc ==> {x | x extreme_point_of q} SUBSET X) /\
        (!Y. Y SUBSET X /\ ~(affine hull Y = (:real^3))
             ==> ~(p IN affine hull Y))
        ==> ~affine_dependent (IMAGE (\x. if x = w then p else g x) v) /\
            (!x y. x IN v /\ y IN v /\
                   (if x = w then p else g x) = (if y = w then p else g y)
                   ==> x = y) /\
            (!q. q IN sc
                 ==> affine_gp_3
                      (convex hull (IMAGE (\x. if x = w then p else g x) v)) q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (\x. if x = w then p else (g:real^M->real^3) x) v =
    p INSERT IMAGE g (v DELETE w)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INSERT; IN_DELETE] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `x:real^M = w` THEN ASM_MESON_TAC[];
      STRIP_TAC THENL
       [EXISTS_TAC `w:real^M` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `x:real^M` THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (g:real^M->real^3) (v DELETE w)`; `p:real^3`;
                 `sc:(real^3->bool)->bool`; `X:real^3->bool`]
    MOI_FGP_ADD_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DELETE] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(v DELETE (w:real^M))` THEN
    ASM_SIMP_TAC[CARD_IMAGE_LE; FINITE_DELETE; CARD_DELETE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:real^M = w` THEN ASM_CASES_TAC `y:real^M = w` THEN
  ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `(if x = w then p else (g:real^M->real^3) x) =
                 (if y = w then p else g y)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((p:real^3) IN IMAGE (g:real^M->real^3) (v DELETE w))` THEN
    REWRITE_TAC[IN_IMAGE; IN_DELETE] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `(if x = w then p else (g:real^M->real^3) x) =
                 (if y = w then p else g y)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((p:real^3) IN IMAGE (g:real^M->real^3) (v DELETE w))` THEN
    REWRITE_TAC[IN_IMAGE; IN_DELETE] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `(if x = w then p else (g:real^M->real^3) x) =
                 (if y = w then p else g y)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE]]);;

let MOI_FGP_PERTURB = prove
 (`!(vs:(real^M->bool)->bool) fx (f:real^M->real^3) (sc:(real^3->bool)->bool)
    e.
        FINITE vs /\ (!v. v IN vs ==> FINITE v /\ ~(v = {}) /\ CARD v <= 3) /\
        (!v w. v IN vs /\ ~(w = {}) /\ w SUBSET v ==> w IN vs) /\
        FINITE sc /\ (!q. q IN sc ==> ?n. n simplex q) /\ &0 < e /\
        (!v. v IN vs /\ v SUBSET fx
             ==> ~affine_dependent (IMAGE f v) /\
                 (!x y. x IN v /\ y IN v /\ f x = f y ==> x = y) /\
                 (!q. q IN sc ==> affine_gp_3 (convex hull (IMAGE f v)) q))
        ==> ?g. (!x. x IN fx ==> g x = f x) /\ (!x. dist(g x,f x) < e) /\
                (!v. v IN vs
                     ==> ~affine_dependent (IMAGE g v) /\
                         (!x y. x IN v /\ y IN v /\ g x = g y ==> x = y) /\
                         (!q. q IN sc
                              ==> affine_gp_3 (convex hull (IMAGE g v)) q))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `Vs = UNIONS {{x:real^3 | x extreme_point_of q} | q IN sc}` THEN
  SUBGOAL_THEN `FINITE (Vs:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Vs" THEN REWRITE_TAC[FINITE_UNIONS] THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[SIMPLEX_EXTREME_POINTS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q:real^3->bool. q IN sc ==> {x | x extreme_point_of q} SUBSET Vs`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN EXPAND_TAC "Vs" THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN s ==> a SUBSET UNIONS s`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `q:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (UNIONS vs:real^M->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_UNIONS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. FINITE P
        ==> P SUBSET UNIONS vs DIFF fx
            ==> ?g. (!x. ~(x IN P) ==> g x = (f:real^M->real^3) x) /\
                    (!x. dist(g x,f x) < e) /\
                    (!v. v IN vs /\ v SUBSET fx UNION P
                         ==> ~affine_dependent (IMAGE g v) /\
                             (!x y. x IN v /\ y IN v /\ g x = g y ==> x = y) /\
                             (!q. q IN sc
                                  ==> affine_gp_3 (convex hull (IMAGE g v)) q))`
  MP_TAC THENL
   [MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `f:real^M->real^3` THEN
      REWRITE_TAC[DIST_REFL; UNION_EMPTY; NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`w:real^M`; `P:real^M->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
    DISCH_TAC THEN
    REMOVE_THEN "ih" MP_TAC THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^3` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `X = IMAGE (g:real^M->real^3) (UNIONS vs) UNION Vs` THEN
    SUBGOAL_THEN `FINITE (X:real^3->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "X" THEN ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`{affine hull Y | Y | Y SUBSET X /\ ~(affine hull Y = (:real^3))}`;
      `(:real^3)`] MOI_FGP_AVOID_AFFINE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `IMAGE (\Y. affine hull Y) {Y:real^3->bool | Y SUBSET X}` THEN
        ASM_SIMP_TAC[FINITE_IMAGE; FINITE_POWERSET] THEN SET_TAC[];
        REWRITE_TAC[FORALL_IN_GSPEC; AFFINE_HULL_UNIV] THEN
        REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
        REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_UNIV] THEN MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `ball((f:real^M->real^3) w,e)`) THEN
    REWRITE_TAC[AFFINE_HULL_UNIV; SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
    ASM_REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\x:real^M. if x = w then p else (g:real^M->real^3) x` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[];
      X_GEN_TAC `x:real^M` THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[DIST_SYM];
      ALL_TAC] THEN
    X_GEN_TAC `v:real^M->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(w:real^M) IN v` THENL
     [ALL_TAC;
      SUBGOAL_THEN
       `!x:real^M. x IN v ==> (if x = w then p else (g:real^M->real^3) x) = g x`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `IMAGE (\x:real^M. if x = w then p else (g:real^M->real^3) x) v =
        IMAGE g v`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `(!x. x IN s ==> (f:real^M->real^3) x = g x)
          ==> IMAGE f s = IMAGE g s`) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(v:real^M->bool) SUBSET fx UNION P` ASSUME_TAC THENL
       [UNDISCH_TAC `(v:real^M->bool) SUBSET fx UNION w INSERT P` THEN
        UNDISCH_TAC `~((w:real^M) IN v)` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC
       `!v:real^M->bool.
          v IN vs /\ v SUBSET fx UNION P
          ==> ~affine_dependent (IMAGE (g:real^M->real^3) v) /\
              (!x y. x IN v /\ y IN v /\ g x = g y ==> x = y) /\
              (!q. q IN sc ==> affine_gp_3 (convex hull (IMAGE g v)) q)` THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `(if x = w then p else (g:real^M->real^3) x) =
        (if y = w then p else g y)` THEN
      ASM_SIMP_TAC[]] THEN
    SUBGOAL_THEN `(v:real^M->bool) SUBSET UNIONS vs` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^M->real^3`; `w:real^M`; `p:real^3`;
                   `v:real^M->bool`; `sc:(real^3->bool)->bool`;
                   `X:real^3->bool`] MOI_FGP_PERTURB_STEP_V) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN
       `IMAGE (g:real^M->real^3) (v DELETE w) SUBSET X /\
        (!q:real^3->bool. q IN sc ==> {x | x extreme_point_of q} SUBSET X)`
      STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "X" THEN CONJ_TAC THENL
         [MATCH_MP_TAC(SET_RULE
           `(s:real^3->bool) SUBSET a ==> s SUBSET a UNION b`) THEN
          MATCH_MP_TAC IMAGE_SUBSET THEN
          UNDISCH_TAC `(v:real^M->bool) SUBSET UNIONS vs` THEN SET_TAC[];
          REPEAT STRIP_TAC THEN
          MATCH_MP_TAC(SET_RULE
           `(s:real^3->bool) SUBSET b ==> s SUBSET a UNION b`) THEN
          ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `v DELETE (w:real^M) = {}` THENL
       [ASM_REWRITE_TAC[IMAGE_CLAUSES; AFFINE_INDEPENDENT_EMPTY; NOT_IN_EMPTY;
                        CONVEX_HULL_EMPTY; affine_gp_3; DISJOINT_EMPTY];
        ALL_TAC] THEN
      SUBGOAL_THEN `(v DELETE (w:real^M)) IN vs /\
                    v DELETE w SUBSET fx UNION P`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `v:real^M->bool` THEN
          ASM_REWRITE_TAC[DELETE_SUBSET];
          UNDISCH_TAC `(v:real^M->bool) SUBSET fx UNION w INSERT P` THEN
          SET_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC
       `!v:real^M->bool.
          v IN vs /\ v SUBSET fx UNION P
          ==> ~affine_dependent (IMAGE (g:real^M->real^3) v) /\
              (!x y. x IN v /\ y IN v /\ g x = g y ==> x = y) /\
              (!q. q IN sc ==> affine_gp_3 (convex hull (IMAGE g v)) q)` THEN
      DISCH_THEN(MP_TAC o SPEC `v DELETE (w:real^M)`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `UNIONS vs DIFF fx:real^M->bool`) THEN
  ASM_SIMP_TAC[FINITE_DIFF; SUBSET_REFL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^M->real^3` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[];
    X_GEN_TAC `v:real^M->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* F1. A fine subdivision of k in general position on UNIONS k0, with k0    *)
(* full: a simplex whose vertices lie in UNIONS k0 lies in a simplex of k0. *)
(* ------------------------------------------------------------------------- *)

let MOI_FGP_FINE_SUBDIVISION = prove
 (`!(k:(real^M->bool)->bool) k0 (sc:(real^3->bool)->bool) (f:real^M->real^3)
    d.
        simplicial_complex k /\ simplicial_subcomplex k0 k /\
        (!r. r IN k ==> aff_dim r <= &2) /\
        (!r. r IN k0 ==> (?l y. linear l /\ !x. x IN r ==> f x = l x + y) /\
                         (!q. q IN sc ==> affine_gp_3 (IMAGE f r) q)) /\
        FINITE sc /\ &0 < d
        ==> ?k'. simplicial_complex k' /\ subdivides k' k /\
                 (!t. t IN k' ==> diameter t < d /\ aff_dim t <= &2) /\
                 (!t. t IN k' /\ ~(t = {}) /\
                      {x | x extreme_point_of t} SUBSET UNIONS k0
                      ==> ?r0. r0 IN k0 /\ t SUBSET r0) /\
                 (!t q. t IN k' /\ t SUBSET UNIONS k0 /\ q IN sc
                        ==> affine_gp_3 (IMAGE f t) q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (UNIONS k:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_MESON_TAC[simplicial_complex; MOI_CON_SC_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `?D. &0 <= D /\ !r:real^M->bool. r IN k ==> diameter r <= D`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `diameter (UNIONS k:real^M->bool)` THEN
    SUBGOAL_THEN `bounded (UNIONS k:real^M->bool)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
    ASM_SIMP_TAC[DIAMETER_POS_LE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIAMETER_SUBSET THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(r:real^M->bool) IN k` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&3 / &4`; `d / (D + &1)`] REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `&0 <= (&3 / &4) pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &4) pow n * D < d` ASSUME_TAC THENL
   [UNDISCH_TAC `(&3 / &4) pow n < d / (D + &1)` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= D ==> &0 < D + &1`] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&3 / &4) pow n * D` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `k0:(real^M->bool)->bool`;
                 `sc:(real^3->bool)->bool`; `f:real^M->real^3`; `D:real`]
    MOI_FGP_ITER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool` STRIP_ASSUME_TAC o
    SPEC `n:num`) THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `k0:(real^M->bool)->bool`;
                 `sc:(real^3->bool)->bool`; `f:real^M->real^3`;
                 `c:(real^M->bool)->bool`] MOI_FGP_DERIVED) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k':(real^M->bool)->bool` MP_TAC) THEN
  REWRITE_TAC[moi_fgp_dsub] THEN STRIP_TAC THEN
  EXISTS_TAC `k':(real^M->bool)->bool` THEN
  SUBGOAL_THEN `!t:real^M->bool. t IN k' ==> ?r. r IN k /\ t SUBSET r`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!r:real^M->bool. r IN k ==> ?e. e SUBSET k' /\ UNIONS e = r`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^M->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `{v:real^M->bool | v IN k' /\ v SUBSET r}` THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    UNDISCH_TAC `!r:real^M->bool. r IN k ==> ?e. e SUBSET c /\ r = UNIONS e` THEN
    DISCH_THEN(MP_TAC o SPEC `r:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(x:real^M) IN r` THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `!u:real^M->bool. u IN c ==> ?e. e SUBSET k' /\ u = UNIONS e` THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^M->bool`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e':(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(x:real^M) IN u` THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^M->bool) SUBSET u /\ u SUBSET UNIONS e`
      MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `r:real^M->bool = UNIONS e` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[subdivides] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN
    UNDISCH_TAC `!v:real^M->bool. v IN k' ==> ?u. u IN c /\ v SUBSET u` THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `&3 / &4 * diameter(u:real^M->bool)` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(&3 / &4) pow n * D` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ x <= a ==> &3 / &4 * x <= a`) THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim(u:real^M->bool)` THEN
      ASM_SIMP_TAC[AFF_DIM_SUBSET]];
    X_GEN_TAC `t:real^M->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC
     `!v:real^M->bool.
        v IN k' /\ ~(v = {})
        ==> ?x u. x extreme_point_of v /\ u IN c /\ v SUBSET u /\
                  x IN relative_interior u` THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^M` (X_CHOOSE_THEN `u:real^M->bool`
      STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `!u:real^M->bool. u IN c ==> ?r. r IN k /\ u SUBSET r` THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^M->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `k0:(real^M->bool)->bool`;
                   `r:real^M->bool`; `u:real^M->bool`; `x:real^M`]
      MOI_FGP_CARRIER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `{x:real^M | x extreme_point_of t} SUBSET UNIONS k0` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* F2. An affine map whose values on an affinely independent vertex set are *)
(* affinely independent and distinct is injective on the convex hull.       *)
(* ------------------------------------------------------------------------- *)

let MOI_FGP_AFFINE_INJ_ON_HULL = prove
 (`!(g:real^M->real^N) l y v.
        linear l /\ (!w. w IN v ==> l w + y = g w) /\
        ~affine_dependent (IMAGE g v) /\
        (!x x'. x IN v /\ x' IN v /\ g x = g x' ==> x = x')
        ==> !x x'. x IN convex hull v /\ x' IN convex hull v /\
                   l x + y = l x' + y ==> x = x'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^M->real^N`; `\w:real^M. w`; `v:real^M->bool`]
    MOI_REAL_AFFINE_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^M`
    (X_CHOOSE_THEN `y':real^M` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`(l':real^N->real^M) o (l:real^M->real^N)`; `\w:real^M. w`;
                 `(l':real^N->real^M) y + y'`; `vec 0:real^M`;
                 `v:real^M->bool`] MOI_REAL_AFFINE_EQ_ON_CONVEX_HULL) THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE; LINEAR_ID; o_THM; VECTOR_ADD_RID] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(l':real^N->real^M) (g(w:real^M)) + y' = w` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^M->real^N) w = l w + y` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_ADD; VECTOR_ADD_ASSOC];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(l:real^M->real^N) x = l x'` ASSUME_TAC THENL
   [UNDISCH_TAC `(l:real^M->real^N) x + y = l x' + y` THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* G. GENERAL_POSITION_MAP_3: general position of PL maps of polyhedra of    *)
(* dimension at most 2 into real^3 (the term MOI_FND_GP_MAP_3 of             *)
(* pc_moi_fnd_stmt.ml).                                                      *)
(* ------------------------------------------------------------------------- *)

let GENERAL_POSITION_MAP_3 = prove
 (`!(k:(real^M->bool)->bool) (k0:(real^M->bool)->bool) (s:(real^3->bool)->bool)
   (f:real^M->real^3) e.
     simplicial_complex k /\ simplicial_subcomplex k0 k /\
     (!r. r IN k ==> aff_dim r <= &2) /\
     simplicial_complex s /\ pl_map_on (UNIONS k) f /\
     (!r. r IN k0
          ==> (?l y. linear l /\ !x. x IN r ==> f x = l x + y) /\
              (!x y. x IN r /\ y IN r /\ f x = f y ==> x = y) /\
              (!q. q IN s ==> affine_gp_3 (IMAGE f r) q)) /\
     &0 < e
     ==> ?k' f'. simplicial_complex k' /\ subdivides k' k /\
                 (!x. x IN UNIONS k0 ==> f' x = f x) /\
                 (!x. x IN UNIONS k ==> dist(f' x,f x) < e) /\
                 (!r. r IN k'
                      ==> (?l y. linear l /\ !x. x IN r ==> f' x = l x + y) /\
                          (!x y. x IN r /\ y IN r /\ f' x = f' y ==> x = y)) /\
                 (!r q. r IN k' /\ q IN s ==> affine_gp_3 (IMAGE f' r) q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (UNIONS k:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_MESON_TAC[simplicial_complex; MOI_CON_SC_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real^3) uniformly_continuous_on UNIONS k` MP_TAC
  THENL
   [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN
    ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE (s:(real^3->bool)->bool) /\
                (!q:real^3->bool. q IN s ==> ?n. n simplex q)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `k0:(real^M->bool)->bool`;
                 `s:(real^3->bool)->bool`; `f:real^M->real^3`; `d:real`]
    MOI_FGP_FINE_SUBDIVISION) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k':(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE (k':(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS k' = UNIONS (k:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[subdivides]; ALL_TAC] THEN
  ABBREV_TAC `vs = moi_real_vertex_sets (k':(real^M->bool)->bool)` THEN
  SUBGOAL_THEN
   `FINITE (vs:(real^M->bool)->bool) /\
    (!v. v IN vs ==> FINITE v /\ ~(v = {}) /\ CARD v <= 3) /\
    (!v w. v IN vs /\ ~(w = {}) /\ w SUBSET v ==> w IN vs) /\
    (!v. v IN vs ==> ~affine_dependent v /\ convex hull v IN k')`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "vs" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_REAL_VERTEX_SETS_FINITE THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^M->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k':(real^M->bool)->bool`; `2`]
        MOI_REAL_VERTEX_SETS_CARD) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(v:real^M->bool) IN moi_real_vertex_sets k'` THEN
      REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN
      MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE; ARITH_RULE `2 + 1 = 3`];
      MP_TAC(ISPEC `k':(real^M->bool)->bool`
        MOI_REAL_VERTEX_SETS_ABSTRACT_COMPLEX) THEN
      ASM_REWRITE_TAC[abstract_complex] THEN MESON_TAC[];
      REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vs:(real^M->bool)->bool`; `UNIONS k0:real^M->bool`;
                 `f:real^M->real^3`; `s:(real^3->bool)->bool`; `e / &2`]
    MOI_FGP_PERTURB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_HALF] THEN
    X_GEN_TAC `v:real^M->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?r0:real^M->bool. r0 IN k0 /\ convex hull v SUBSET r0`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC
       `!t:real^M->bool.
          t IN k' /\ ~(t = {}) /\ {x | x extreme_point_of t} SUBSET UNIONS k0
          ==> ?r0. r0 IN k0 /\ t SUBSET r0` THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `!r:real^M->bool. r IN k0
          ==> (?l y. linear l /\ !x. x IN r ==> (f:real^M->real^3) x = l x + y) /\
              (!x y. x IN r /\ y IN r /\ f x = f y ==> x = y) /\
              (!q. q IN s ==> affine_gp_3 (IMAGE f r) q)` THEN
    DISCH_THEN(MP_TAC o SPEC `r0:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `L:real^M->real^3` (X_CHOOSE_THEN `Y:real^3`
        STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `!x:real^M. x IN convex hull v ==> f x = (L:real^M->real^3) x + Y`
    ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^M->bool) SUBSET convex hull v` ASSUME_TAC THENL
     [REWRITE_TAC[HULL_SUBSET]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FGP_INJ_AFFINE_INDEPENDENT THEN
      MAP_EVERY EXISTS_TAC [`L:real^M->real^3`; `Y:real^3`] THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[SUBSET];
      ASM_MESON_TAC[SUBSET];
      X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `convex hull (IMAGE (f:real^M->real^3) v) = IMAGE f (convex hull v)`
      SUBST1_TAC THENL
       [SUBGOAL_THEN
         `!w:real^M->bool. w SUBSET convex hull v
                           ==> IMAGE (f:real^M->real^3) w =
                               IMAGE (\x. L x + Y) w`
        ASSUME_TAC THENL
         [REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
           `(!x. x IN s ==> (f:real^M->real^3) x = g x)
            ==> IMAGE f s = IMAGE g s`) THEN
          ASM_MESON_TAC[SUBSET];
          ALL_TAC] THEN
        ASM_SIMP_TAC[SUBSET_REFL; MOI_REAL_AFFINE_IMAGE_CONVEX_HULL];
        ALL_TAC] THEN
      UNDISCH_TAC
       `!t q. t IN k' /\ t SUBSET UNIONS k0 /\ q IN s
              ==> affine_gp_3 (IMAGE (f:real^M->real^3) t) q` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `convex hull v SUBSET (r0:real^M->bool)` THEN
      UNDISCH_TAC `(r0:real^M->bool) IN k0` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\x:real^M. x`; `g:real^M->real^3`;
                 `vs:(real^M->bool)->bool`] MOI_REAL_SIMPLEXWISE_AFFINE) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "vs" THEN MATCH_MP_TAC MOI_REAL_VERTEX_SETS_REALIZES THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_ID] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^3` (LABEL_TAC "h")) THEN
  SUBGOAL_THEN
   `!t:real^M->bool. t IN k' /\ ~(t = {}) ==> ?v. v IN vs /\ t = convex hull v`
  ASSUME_TAC THENL
   [EXPAND_TAC "vs" THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_REAL_SIMPLEX_VERTICES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k':(real^M->bool)->bool`; `h:real^M->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    UNDISCH_TAC `(x:real^M) IN UNIONS k0` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real^M->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(r0:real^M->bool) IN k` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `?t:real^M->bool. t IN k' /\ t SUBSET r0 /\ x IN t`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `subdivides k' (k:(real^M->bool)->bool)` THEN
      REWRITE_TAC[subdivides] THEN
      DISCH_THEN(MP_TAC o SPEC `r0:real^M->bool` o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `dd:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(x:real^M) IN r0` THEN
      UNDISCH_TAC `UNIONS dd = (r0:real^M->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(t:real^M->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC
     `!t:real^M->bool. t IN k' /\ ~(t = {})
                       ==> ?v. v IN vs /\ t = convex hull v` THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^M->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^M->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "h" (MP_TAC o SPEC `v:real^M->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC
     `!r:real^M->bool. r IN k0
          ==> (?l y. linear l /\ !x. x IN r ==> (f:real^M->real^3) x = l x + y) /\
              (!x y. x IN r /\ y IN r /\ f x = f y ==> x = y) /\
              (!q. q IN s ==> affine_gp_3 (IMAGE f r) q)` THEN
    DISCH_THEN(MP_TAC o SPEC `r0:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `L:real^M->real^3` (X_CHOOSE_THEN `Y:real^3`
        STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`l:real^M->real^3`; `L:real^M->real^3`; `y:real^3`;
                   `Y:real^3`; `v:real^M->bool`]
      MOI_REAL_AFFINE_EQ_ON_CONVEX_HULL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(w:real^M) IN r0` ASSUME_TAC THENL
       [UNDISCH_TAC `(t:real^M->bool) SUBSET r0` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE `(w:real^M) IN s ==> s SUBSET r ==> w IN r`) THEN
        ASM_SIMP_TAC[HULL_INC];
        ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^M->real^3) w = f w` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    SUBGOAL_THEN `(x:real^M) IN convex hull v` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?t:real^M->bool. t IN k' /\ x IN t` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_UNIONS]; ALL_TAC] THEN
    SUBGOAL_THEN `~(t:real^M->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?v:real^M->bool. v IN vs /\ t = convex hull v`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "h" (MP_TAC o SPEC `v:real^M->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `IMAGE (h:real^M->real^3) (convex hull v) = convex hull (IMAGE (g:real^M->real^3) v)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\x:real^M. x`; `g:real^M->real^3`; `h:real^M->real^3`;
                     `l:real^M->real^3`; `y:real^3`; `v:real^M->bool`]
        MOI_REAL_IMAGE_SIMPLEX) THEN
      ASM_REWRITE_TAC[IMAGE_ID];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^M->real^3) x IN ball(f x,e)` MP_TAC THENL
     [SUBGOAL_THEN `(h:real^M->real^3) x IN convex hull (IMAGE (g:real^M->real^3) v)`
      MP_TAC THENL
       [UNDISCH_TAC
         `IMAGE (h:real^M->real^3) (convex hull v) = convex hull (IMAGE (g:real^M->real^3) v)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      SPEC_TAC(`(h:real^M->real^3) x`,`z:real^3`) THEN
      REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[CONVEX_BALL; SUBSET; FORALL_IN_IMAGE; IN_BALL] THEN
      X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(w:real^M) IN t` ASSUME_TAC THENL
       [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
      SUBGOAL_THEN `dist((f:real^M->real^3) w,f x) < e / &2` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[IN_UNIONS];
          ASM_MESON_TAC[IN_UNIONS];
          MATCH_MP_TAC REAL_LET_TRANS THEN
          EXISTS_TAC `diameter(t:real^M->bool)` THEN
          CONJ_TAC THENL
           [REWRITE_TAC[dist] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
            ASM_REWRITE_TAC[] THEN
            ASM_MESON_TAC[MOI_CON_SC_COMPACT; COMPACT_IMP_BOUNDED];
            ASM_MESON_TAC[]]];
        ALL_TAC] THEN
      SUBGOAL_THEN `dist((g:real^M->real^3) w,f w) < e / &2` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONV_TAC NORM_ARITH;
      REWRITE_TAC[IN_BALL] THEN CONV_TAC NORM_ARITH];
    X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `t:real^M->bool = {}` THENL
     [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN MESON_TAC[LINEAR_ZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN `?v:real^M->bool. v IN vs /\ t = convex hull v`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "h" (MP_TAC o SPEC `v:real^M->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`l:real^M->real^3`; `y:real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `x':real^M`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `~affine_dependent (IMAGE (g:real^M->real^3) v) /\
      (!x x'. x IN v /\ x' IN v /\ g x = g x' ==> x = x')`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^M->real^3`; `l:real^M->real^3`; `y:real^3`;
                   `v:real^M->bool`] MOI_FGP_AFFINE_INJ_ON_HULL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real^M->bool`; `q:real^3->bool`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `t:real^M->bool = {}` THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; affine_gp_3; DISJOINT_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN `?v:real^M->bool. v IN vs /\ t = convex hull v`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "h" (MP_TAC o SPEC `v:real^M->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`\x:real^M. x`; `g:real^M->real^3`; `h:real^M->real^3`;
                   `l:real^M->real^3`; `y:real^3`; `v:real^M->bool`]
      MOI_REAL_IMAGE_SIMPLEX) THEN
    ASM_REWRITE_TAC[IMAGE_ID] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[]]);;


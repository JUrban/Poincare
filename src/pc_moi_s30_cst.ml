(* ========================================================================= *)
(* pc_moi_s30_cst: Moise GTM 47, pp.217-218, the two cases of 30.7.          *)
(* Main theorems: S307_OUTSIDE = MOI_S30_307_OUTSIDE, S307_INSIDE =          *)
(* MOI_S30_307_INSIDE (pc_moi_s3032_stmt.ml).                                *)
(*  1.  the common step: SPLIT_DISK_R3 along the essential rim gives a      *)
(*      single PL 2-sphere M' (chi 2; two non-spherical components would    *)
(*      have chi at most 0 each), so the new 3-manifold is a PL ball.       *)
(*  2.  OUTSIDE: the ball contains s1, contradicting SHELL_CORE_ESSENTIAL.  *)
(*  3.  INSIDE tools: the handle sphere, the region lemma, product         *)
(*      neighbourhoods and local sides at the bicollar of M'.               *)
(*  4.  INSIDE: x is the ball X' with the handle bounded by the annulus and *)
(*      the two disks (HANDLE_SOLID_TORUS).                                 *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_fnd_euler.ml";;
needs "src/pc_moi_s35_ext.ml";;
needs "src/pc_moi_fnd_bicol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. The common step.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Euler characteristic of a union of complexes with disjoint spaces. *)

let MOI_S3CS_EULER_SPLIT = prove
 (`!m1 m2:(real^N->bool)->bool.
     FINITE m1 /\ FINITE m2 /\ DISJOINT (UNIONS m1) (UNIONS m2)
     ==> complex_euler (m1 UNION m2) = complex_euler m1 + complex_euler m2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COMPLEX_EULER_UNION] THEN
  MATCH_MP_TAC(REAL_ARITH `z = &0 ==> a + b - z = a + b`) THEN
  REWRITE_TAC[complex_euler] THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `{s | s IN (m1:(real^N->bool)->bool) INTER m2 /\ aff_dim s = &k} = {}`
    (fun th -> REWRITE_TAC[th; CARD_CLAUSES; REAL_MUL_RZERO]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `s:real^N->bool = {}` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `DISJOINT (UNIONS (m1:(real^N->bool)->bool)) (UNIONS m2)` THEN
    MAP_EVERY UNDISCH_TAC [`(s:real^N->bool) IN m1`; `(s:real^N->bool) IN m2`] THEN
    SET_TAC[];
    UNDISCH_TAC `aff_dim ({}:real^N->bool) = &k` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC]);;

(* A connected closed surface that is not a sphere has chi at most 0 (it is *)
(* even by BOUNDS and EULER_EVEN, at most 2, and 2 only for spheres).       *)

let MOI_S3CS_NONSPHERE_EULER = prove
 (mk_imp(list_mk_conj [moi_n3 MOI_FND_SURFACE_SPHERE; moi_std_csq MOI_S30_BOUNDS;
                       moi_n3 MOI_S30_EULER_EVEN],
  `!m:(real^3->bool)->bool.
     FINITE m /\ combinatorial_manifold 2 m /\ connected (UNIONS m) /\
     ~(UNIONS m = {}) /\ ~pl_sphere 2 (UNIONS m)
     ==> complex_euler m <= &0`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ss") (CONJUNCTS_THEN2 (LABEL_TAC "bd")
    (LABEL_TAC "ev"))) THEN
  GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "ss" (MP_TAC o SPEC `m:(real^3->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "bd" (MP_TAC o SPEC `m:(real^3->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "ev" (MP_TAC o SPEC `x:(real^3->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPEC `x:(real^3->bool)->bool` MOI_STD_EULER_INTEGER) THEN
  ABBREV_TAC `k = complex_euler (x:(real^3->bool)->bool)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `k < &1` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`complex_euler (m:(real^3->bool)->bool) <= &2`;
      `~(complex_euler (m:(real^3->bool)->bool) = &2)`;
      `complex_euler (m:(real^3->bool)->bool) = &2 * k`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real`; `&1`] REAL_LT_INTEGERS) THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED] THEN
  UNDISCH_TAC `complex_euler (m:(real^3->bool)->bool) = &2 * k` THEN REAL_ARITH_TAC);;

(* The surface obtained by splitting along the essential rim is one sphere. *)

let MOI_S3CS_SPHERE_STEP = prove
 (mk_imp(list_mk_conj [moi_n3 MOI_FND_SURFACE_SPHERE; moi_std_csq MOI_S30_SPLIT_ESSENTIAL;
                       moi_std_csq MOI_S30_BOUNDS; moi_n3 MOI_S30_EULER_EVEN],
  `!(m:(real^3->bool)->bool) a j j1 j2 d1 d2 (m':(real^3->bool)->bool).
     FINITE m /\ combinatorial_manifold 2 m /\ connected (UNIONS m) /\
     pl_annulus_with_ends a j1 j2 /\ a SUBSET UNIONS m /\
     pl_sphere 1 j /\ j SUBSET a DIFF (j1 UNION j2) /\
     pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
     DISJOINT d1 d2 /\ d1 INTER UNIONS m = j1 /\ d2 INTER UNIONS m = j2 /\
     FINITE m' /\ combinatorial_manifold 2 m' /\
     UNIONS m' = (UNIONS m DIFF a) UNION d1 UNION d2 /\
     ~(?z. homotopic_with (\f. T)
             (subtopology euclidean j,subtopology euclidean (UNIONS m))
             (\x. x) (\x. z)) /\
     complex_euler m' = &2
     ==> pl_sphere 2 (UNIONS m')`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ss") (CONJUNCTS_THEN2 (LABEL_TAC "se")
      (CONJUNCTS_THEN2 (LABEL_TAC "bd") (LABEL_TAC "ev")))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "se" (MP_TAC o SPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j:real^3->bool`;
    `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
    `m':(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `m1:(real^3->bool)->bool` (X_CHOOSE_THEN `m2:(real^3->bool)->bool`
      STRIP_ASSUME_TAC))) THENL
   [USE_THEN "ss" (MP_TAC o SPEC `m':(real^3->bool)->bool`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`2`; `d1:real^3->bool`; `j1:real^3->bool`]
        MOI_S5C_CELL_INTERIOR_NONEMPTY) THEN
      ASM_REWRITE_TAC[ARITH] THEN SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `complex_euler (m1:(real^3->bool)->bool) <= &0 /\
                complex_euler (m2:(real^3->bool)->bool) <= &0` MP_TAC THENL
   [USE_THEN "ss" (fun ss -> USE_THEN "bd" (fun bd -> USE_THEN "ev" (fun ev ->
      CONJ_TAC THEN MATCH_MP_TAC (MP MOI_S3CS_NONSPHERE_EULER (CONJ ss (CONJ bd ev)))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m1:(real^3->bool)->bool`; `m2:(real^3->bool)->bool`]
    MOI_S3CS_EULER_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `complex_euler (m':(real^3->bool)->bool) = &2` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 2. OUTSIDE.  The ball X' = x UNION N(d) contains s1 and lies             *)
(* in s2, so the spine of s1 is null-homotopic in s2.                        *)
(* ------------------------------------------------------------------------- *)

(* The disk data of the case hypotheses. *)

let MOI_S3CS_RIM = prove
 (`!(s:real^3->bool) d (f:real^3->real^3) g.
     &2 simplex s /\ pl_homeomorphism (s,d) (f,g)
     ==> pl_cell_with_boundary 2 d (IMAGE f (relative_frontier s)) /\
         pl_sphere 1 (IMAGE f (relative_frontier s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 d (IMAGE (f:real^3->real^3) (relative_frontier s))`
  ASSUME_TAC THENL
   [REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5E_CELL_SPHERE1 THEN
    EXISTS_TAC `d:real^3->bool` THEN ASM_REWRITE_TAC[]]);;

(* A solid torus is nonempty and has a spine. *)

let MOI_S3CS_SOLID_TORUS_SPINE = prove
 (`!s:real^N->bool. solid_torus s ==> ~(s = {}) /\ ?j. spine j s /\ j SUBSET s`,
  GEN_TAC THEN REWRITE_TAC[solid_torus; homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->real^(2,2)finite_sum`
    (X_CHOOSE_TAC `h:real^(2,2)finite_sum->real^N`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o ONCE_REWRITE_RULE[HOMEOMORPHISM_SYM]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (h:real^(2,2)finite_sum->real^N)
                   (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) = s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; PCROSS_EQ_EMPTY; CBALL_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN
    REAL_ARITH_TAC;
    EXISTS_TAC `IMAGE (h:real^(2,2)finite_sum->real^N)
                  ({vec 0:real^2} PCROSS sphere(vec 0:real^2,&1))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[spine] THEN
      MAP_EVERY EXISTS_TAC [`h:real^(2,2)finite_sum->real^N`;
                            `k:real^N->real^(2,2)finite_sum`; `vec 0:real^2`] THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_01];
      UNDISCH_TAC `IMAGE (h:real^(2,2)finite_sum->real^N)
                     (cball(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) = s` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET_PCROSS; SUBSET_REFL; SING_SUBSET; CENTRE_IN_CBALL; REAL_POS]]]);;

let S307_OUTSIDE = prove
 (MOI_S30_307_OUTSIDE,
  REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sd") (CONJUNCTS_THEN2 (LABEL_TAC "m266")
    (CONJUNCTS_THEN2 (LABEL_TAC "sch") (CONJUNCTS_THEN2 (LABEL_TAC "ss")
    (CONJUNCTS_THEN2 (LABEL_TAC "se") (CONJUNCTS_THEN2 (LABEL_TAC "bd")
    (CONJUNCTS_THEN2 (LABEL_TAC "ev") (LABEL_TAC "core")))))))) THEN
  MAP_EVERY X_GEN_TAC [`s1:real^3->bool`; `s2:real^3->bool`; `m:(real^3->bool)->bool`;
    `x:(real^3->bool)->bool`; `s:real^3->bool`; `d:real^3->bool`;
    `f:real^3->real^3`; `g:real^3->real^3`] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `UNIONS (x:(real^3->bool)->bool) = UNIONS m UNION inside (UNIONS m)` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `d:real^3->bool`; `f:real^3->real^3`;
                 `g:real^3->real^3`] MOI_S3CS_RIM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `j = IMAGE (f:real^3->real^3) (relative_frontier s)` THEN
  (* split along d inside v = interior s2 *)
  USE_THEN "sd" (MP_TAC o SPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`;
    `j:real^3->bool`; `interior s2:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_INTERIOR]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3->bool` (X_CHOOSE_THEN `j1:real^3->bool`
    (X_CHOOSE_THEN `j2:real^3->bool` (X_CHOOSE_THEN `d1:real^3->bool`
      (X_CHOOSE_THEN `d2:real^3->bool` (X_CHOOSE_THEN `m':(real^3->bool)->bool`
        STRIP_ASSUME_TAC)))))) THEN
  UNDISCH_TAC `UNIONS (m':(real^3->bool)->bool) = (UNIONS m DIFF a) UNION d1 UNION d2` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  (* the new surface is a sphere *)
  SUBGOAL_THEN `pl_sphere 2 (UNIONS (m':(real^3->bool)->bool))` ASSUME_TAC THENL
   [USE_THEN "ss" (fun ss -> USE_THEN "se" (fun se -> USE_THEN "bd" (fun bd ->
      USE_THEN "ev" (fun ev ->
        MP_TAC(SPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j:real^3->bool`;
                      `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`;
                      `d2:real^3->bool`; `m':(real^3->bool)->bool`]
          (MP MOI_S3CS_SPHERE_STEP (CONJ ss (CONJ se (CONJ bd ev))))))))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_ADD_LID] THEN
      UNDISCH_TAC `(a:real^3->bool) SUBSET UNIONS m INTER interior s2` THEN SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* the new 3-manifold *)
  FIRST_X_ASSUM(MP_TAC o SPEC `x:(real^3->bool)->bool` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t &&
                             fst(dest_const t) = "combinatorial_manifold_with_boundary"))
        (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    can (find_term (fun t -> t = `interior (UNIONS (x':(real^3->bool)->bool))`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* X' is a ball *)
  SUBGOAL_THEN `compact (UNIONS (x':(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3D_X_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `s1:real^3->bool` MOI_S3CS_SOLID_TORUS_SPINE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `j0:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(interior (UNIONS (x':(real^3->bool)->bool)) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`UNIONS (x:(real^3->bool)->bool)`; `UNIONS (x':(real^3->bool)->bool)`]
      SUBSET_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(s1:real^3->bool) SUBSET interior (UNIONS (x:(real^3->bool)->bool))`;
      `~(s1:real^3->bool = {})`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (m':(real^3->bool)->bool)`; `UNIONS (x':(real^3->bool)->bool)`]
    MOI_S5C_FILL_CHAR) THEN
  ASM_SIMP_TAC[MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC; DIMINDEX_3; ARITH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN
  SUBGOAL_THEN `pl_ball 3 (UNIONS (x':(real^3->bool)->bool))` ASSUME_TAC THENL
   [USE_THEN "sch" (MP_TAC o SPEC `UNIONS (m':(real^3->bool)->bool)` o
      REWRITE_RULE[PL_SCHOENFLIES_3_STATEMENT]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `contractible (UNIONS (x':(real^3->bool)->bool))` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_ball 3 (UNIONS (x':(real^3->bool)->bool))` THEN
    REWRITE_TAC[pl_ball] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^3`
      (X_CHOOSE_THEN `q:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC(ISPECL [`k:real^3->bool`; `UNIONS (x':(real^3->bool)->bool)`]
      HOMEOMORPHIC_CONTRACTIBLE) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`p:real^3->real^3`; `q:real^3->real^3`] THEN
      UNDISCH_TAC `pl_homeomorphism (k,UNIONS (x':(real^3->bool)->bool))
                     ((p:real^3->real^3),q)` THEN
      SIMP_TAC[pl_homeomorphism];
      MATCH_MP_TAC CONVEX_IMP_CONTRACTIBLE THEN MATCH_MP_TAC SIMPLEX_IMP_CONVEX THEN
      EXISTS_TAC `&3:int` THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* the spine of s1 is null-homotopic in s2 *)
  USE_THEN "core" (MP_TAC o SPECL [`s1:real^3->bool`; `s2:real^3->bool`; `j0:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\y:real^3. y`; `j0:real^3->bool`; `UNIONS (x':(real^3->bool)->bool)`]
    NULLHOMOTOPIC_INTO_CONTRACTIBLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUS_ON_ID; IMAGE_ID] THEN
    MAP_EVERY UNDISCH_TAC
     [`(j0:real^3->bool) SUBSET s1`;
      `(s1:real^3->bool) SUBSET interior (UNIONS (x:(real^3->bool)->bool))`;
      `UNIONS (x:(real^3->bool)->bool) SUBSET UNIONS x'`] THEN
    MP_TAC(ISPEC `UNIONS (x:(real^3->bool)->bool)` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real^3`) THEN EXISTS_TAC `c:real^3` THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_RIGHT THEN
  EXISTS_TAC `UNIONS (x':(real^3->bool)->bool)` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`UNIONS (x:(real^3->bool)->bool) DIFF UNIONS x' UNION UNIONS x' DIFF UNIONS x
     SUBSET interior s2`;
    `UNIONS (x:(real^3->bool)->bool) SUBSET interior s2`] THEN
  MP_TAC(ISPEC `s2:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 3. INSIDE, the tools.  The handle sphere a UNION d1 UNION d2,             *)
(* the region lemma (an open bounded set with frontier in a sphere is its   *)
(* inside), and the local sides of a bicollared sphere (product             *)
(* neighbourhoods from MOI_FND_BICOLLAR_R3).                                 *)
(* ------------------------------------------------------------------------- *)

(* The annulus a capped by the disks d1 and d2 is a sphere. *)

let MOI_S3CS_SIGMA_SPHERE = prove
 (mk_imp(MOI_SCH3_DISK_UNION,
  `!(a:real^3->bool) j1 j2 d1 d2.
     pl_annulus_with_ends a j1 j2 /\ pl_cell_with_boundary 2 d1 j1 /\
     pl_cell_with_boundary 2 d2 j2 /\ DISJOINT d1 d2 /\
     d1 INTER a = j1 /\ d2 INTER a = j2
     ==> pl_sphere 2 (a UNION d1 UNION d2)`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `j1:real^3->bool`; `a:real^3->bool`; `j2:real^3->bool`]
    MOI_S5C_DISK_ANN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `a UNION d1 UNION d2 = (d1 UNION a) UNION (d2:real^3->bool)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_sphere")) (concl th))) THEN
  EXISTS_TAC `j2:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`DISJOINT (d1:real^3->bool) d2`; `(d2:real^3->bool) INTER a = j2`] THEN
  SET_TAC[]);;

(* A finite combinatorial 3-manifold with boundary and nonempty space has   *)
(* nonempty interior (it is pure).                                           *)

let MOI_S3CS_CMWB_INTERIOR = prove
 (`!x:(real^3->bool)->bool.
     FINITE x /\ combinatorial_manifold_with_boundary 3 x /\ ~(UNIONS x = {})
     ==> ~(interior (UNIONS x) = {})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?s0:real^3->bool. s0 IN x /\ ~(s0 = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(UNIONS (x:(real^3->bool)->bool) = {})` THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:(real^3->bool)->bool`; `s0:real^3->bool`] MOI_FBC_CMWB3_PURE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?n. n simplex (r:real^3->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(interior (r:real^3->bool) = {})` MP_TAC THENL
   [MP_TAC(ISPEC `r:real^3->bool` AFF_DIM_NONEMPTY_INTERIOR_EQ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:real^3->bool`; `UNIONS (x:(real^3->bool)->bool)`] SUBSET_INTERIOR) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(r:real^3->bool) IN x` THEN SET_TAC[];
    UNDISCH_TAC `interior (UNIONS (x:(real^3->bool)->bool)) = {}` THEN SET_TAC[]]);;

(* Product neighbourhoods of a bicollared locally connected compact set: an *)
(* open nn around p0 inside o0, split by s into two connected open pieces. *)

let MOI_S3CS_LOCAL_PRODUCT = prove
 (`!(s:real^3->bool) w (pc:real^(3,1)finite_sum->real^3) qc p0 o0.
     locally connected s /\ compact s /\
     homeomorphism (s PCROSS interval[--vec 1:real^1,vec 1],w) (pc,qc) /\
     s SUBSET interior w /\ (!x. x IN s ==> pc(pastecart x (vec 0)) = x) /\
     p0 IN s /\ open o0 /\ p0 IN o0
     ==> ?nn n1 n2. open nn /\ p0 IN nn /\ nn SUBSET o0 /\
                    open n1 /\ open n2 /\ connected n1 /\ connected n2 /\
                    DISJOINT n1 s /\ DISJOINT n2 s /\
                    n1 SUBSET nn /\ n2 SUBSET nn /\ nn SUBSET n1 UNION s UNION n2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  (* a radius *)
  SUBGOAL_THEN `?r. &0 < r /\ ball(p0:real^3,r) SUBSET o0 INTER interior w`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `o0 INTER interior w:real^3->bool` OPEN_CONTAINS_BALL) THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN
    DISCH_THEN(MP_TAC o SPEC `p0:real^3`) THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[SUBSET]; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (s INTER cball(p0:real^3,r / &2)) /\
                s INTER cball(p0,r / &2) SUBSET ball(p0,r)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_INTER_CLOSED; CLOSED_CBALL] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_CBALL; IN_BALL] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 < r`; `dist(p0:real^3,y) <= r / &2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the thickness *)
  MP_TAC(ISPECL [`s INTER cball(p0:real^3,r / &2)`; `(:real^3) DIFF ball(p0,r)`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_BALL] THEN
    UNDISCH_TAC `s INTER cball(p0:real^3,r / &2) SUBSET ball(p0,r)` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`pc:real^(3,1)finite_sum->real^3`;
                 `(s:real^3->bool) PCROSS interval[--vec 1:real^1,vec 1]`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `eta:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `ep = min (delta / &2) (&1 / &2)` THEN
  SUBGOAL_THEN `&0 < ep /\ ep < delta /\ ep <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ep" THEN UNDISCH_TAC `&0 < delta` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* a connected neighbourhood of p0 in s *)
  FIRST_ASSUM(MP_TAC o SPECL [`s INTER ball(p0:real^3,r / &2)`; `p0:real^3`] o
    GEN_REWRITE_RULE I [LOCALLY_CONNECTED]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL; IN_INTER; CENTRE_IN_BALL; REAL_HALF];
    DISCH_THEN(X_CHOOSE_THEN `bb:real^3->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `!x:real^3. x IN bb ==> x IN s /\ x IN s INTER cball(p0,r / &2)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p0:real^3`; `r / &2`] BALL_SUBSET_CBALL) THEN
    UNDISCH_TAC `(bb:real^3->bool) SUBSET s INTER ball(p0,r / &2)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the three intervals *)
  SUBGOAL_THEN
   `interval(--lift ep,lift ep) SUBSET interval[--vec 1:real^1,vec 1] /\
    interval(vec 0,lift ep) SUBSET interval(--lift ep,lift ep) /\
    interval(--lift ep,vec 0) SUBSET interval(--lift ep,lift ep) /\
    (vec 0:real^1) IN interval(--lift ep,lift ep) /\
    ~((vec 0:real^1) IN interval(vec 0,lift ep)) /\
    ~((vec 0:real^1) IN interval(--lift ep,vec 0)) /\
    (!t:real^1. t IN interval(--lift ep,lift ep)
         ==> t IN interval(vec 0,lift ep) \/ t = vec 0 \/
             t IN interval(--lift ep,vec 0)) /\
    (!t:real^1. t IN interval(--lift ep,lift ep) ==> norm t < delta)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERVAL_1; DROP_NEG; LIFT_DROP; DROP_VEC; NORM_1;
                GSYM DROP_EQ] THEN
    REPEAT CONJ_TAC THEN TRY(X_GEN_TAC `t:real^1`) THEN
    MAP_EVERY UNDISCH_TAC [`&0 < ep`; `ep < delta`; `ep <= &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the product pieces stay in the ball *)
  SUBGOAL_THEN `!x t. x IN bb /\ t IN interval(--lift ep,lift ep)
                      ==> (pc:real^(3,1)finite_sum->real^3) (pastecart x t) IN ball(p0,r)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real^1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN s /\ x IN s INTER cball(p0,r / &2)` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `dist((pc:real^(3,1)finite_sum->real^3)(pastecart x t),
                       pc(pastecart x (vec 0))) < eta`
    MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `delta:real`)) (concl th) &&
        can (find_term (fun t -> t = `eta:real`)) (concl th))) THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; DIST_PASTECART_CANCEL; DIST_0] THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `interval(--lift ep,lift ep) SUBSET interval[--vec 1:real^1,vec 1]` THEN
      MAP_EVERY UNDISCH_TAC [`(t:real^1) IN interval(--lift ep,lift ep)`;
                             `(vec 0:real^1) IN interval(--lift ep,lift ep)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`x:real^3`;
                                `(pc:real^(3,1)finite_sum->real^3)(pastecart x t)`] o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `eta:real`)) (concl th) &&
        not (can (find_term (fun t -> t = `delta:real`)) (concl th)))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_DIFF; IN_UNIV]; ALL_TAC] THEN
    MP_TAC(ISPECL [`x:real^3`; `(pc:real^(3,1)finite_sum->real^3)(pastecart x t)`]
      DIST_SYM) THEN
    UNDISCH_TAC `dist((pc:real^(3,1)finite_sum->real^3)(pastecart x t),x) < eta` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* images of open product pieces are open *)
  SUBGOAL_THEN
   `!tt:real^1->bool. open tt /\ tt SUBSET interval(--lift ep,lift ep)
        ==> open (IMAGE (pc:real^(3,1)finite_sum->real^3) (bb PCROSS tt)) /\
            IMAGE pc (bb PCROSS tt) SUBSET ball(p0,r)`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE (pc:real^(3,1)finite_sum->real^3) (bb PCROSS tt) SUBSET ball(p0,r)`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
      MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real^1`] THEN STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(t:real^1) IN tt` THEN
      UNDISCH_TAC `(tt:real^1->bool) SUBSET interval(--lift ep,lift ep)` THEN SET_TAC[];
      ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `interior w:real^3->bool` THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `w:real^3->bool` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`qc:real^3->real^(3,1)finite_sum`;
                            `(s:real^3->bool) PCROSS interval[--vec 1:real^1,vec 1]`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_PCROSS THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `interval(--lift ep,lift ep) SUBSET interval[--vec 1:real^1,vec 1]` THEN
      UNDISCH_TAC `(tt:real^1->bool) SUBSET interval(--lift ep,lift ep)` THEN SET_TAC[];
      UNDISCH_TAC `ball(p0:real^3,r) SUBSET o0 INTER interior w` THEN
      UNDISCH_TAC `IMAGE (pc:real^(3,1)finite_sum->real^3) (bb PCROSS tt) SUBSET ball(p0,r)` THEN
      SET_TAC[];
      REWRITE_TAC[INTERIOR_SUBSET]];
    ALL_TAC] THEN
  (* images of connected product pieces are connected *)
  SUBGOAL_THEN
   `!tt:real^1->bool. connected tt /\ tt SUBSET interval(--lift ep,lift ep)
        ==> connected (IMAGE (pc:real^(3,1)finite_sum->real^3) (bb PCROSS tt))`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(s:real^3->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PCROSS_MONO THEN CONJ_TAC THENL
       [UNDISCH_TAC `(bb:real^3->bool) SUBSET s INTER ball(p0,r / &2)` THEN SET_TAC[];
        UNDISCH_TAC `interval(--lift ep,lift ep) SUBSET interval[--vec 1:real^1,vec 1]` THEN
        UNDISCH_TAC `(tt:real^1->bool) SUBSET interval(--lift ep,lift ep)` THEN SET_TAC[]];
      MATCH_MP_TAC CONNECTED_PCROSS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* off the zero section the image misses s *)
  SUBGOAL_THEN `!x t. x IN bb /\ t IN interval(--lift ep,lift ep) /\
                      (pc:real^(3,1)finite_sum->real^3)(pastecart x t) IN s ==> t = vec 0`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real^1`] THEN STRIP_TAC THEN
    ABBREV_TAC `y = (pc:real^(3,1)finite_sum->real^3)(pastecart x t)` THEN
    SUBGOAL_THEN `(x:real^3) IN s /\ (t:real^1) IN interval[--vec 1,vec 1] /\
                  (vec 0:real^1) IN interval[--vec 1,vec 1]` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `interval(--lift ep,lift ep) SUBSET interval[--vec 1:real^1,vec 1]` THEN
      MAP_EVERY UNDISCH_TAC [`(t:real^1) IN interval(--lift ep,lift ep)`;
                             `(vec 0:real^1) IN interval(--lift ep,lift ep)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(qc:real^3->real^(3,1)finite_sum) y = pastecart x t` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
      ALL_TAC] THEN
    SUBGOAL_THEN `(qc:real^3->real^(3,1)finite_sum) y = pastecart y (vec 0)` MP_TAC THENL
     [SUBGOAL_THEN `(pc:real^(3,1)finite_sum->real^3) (pastecart y (vec 0)) = y`
        (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
      ASM_REWRITE_TAC[PASTECART_INJ] THEN MESON_TAC[]];
    ALL_TAC] THEN
  (* p0 is in the middle piece *)
  SUBGOAL_THEN `(p0:real^3) IN IMAGE (pc:real^(3,1)finite_sum->real^3)
                                 (bb PCROSS interval(--lift ep,lift ep))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `pastecart (p0:real^3) (vec 0:real^1)` THEN
    ASM_SIMP_TAC[PASTECART_IN_PCROSS];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (pc:real^(3,1)finite_sum->real^3) (bb PCROSS interval(--lift ep,lift ep))`;
    `IMAGE (pc:real^(3,1)finite_sum->real^3) (bb PCROSS interval(vec 0,lift ep))`;
    `IMAGE (pc:real^(3,1)finite_sum->real^3) (bb PCROSS interval(--lift ep,vec 0))`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `interval(--lift ep,lift ep)` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `open:(real^3->bool)->bool`))
                                 (concl th))) THEN
    REWRITE_TAC[OPEN_INTERVAL; SUBSET_REFL] THEN SIMP_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `interval(--lift ep,lift ep)` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `open:(real^3->bool)->bool`))
                                 (concl th))) THEN
    REWRITE_TAC[OPEN_INTERVAL; SUBSET_REFL] THEN
    UNDISCH_TAC `ball(p0:real^3,r) SUBSET o0 INTER interior w` THEN SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `interval(vec 0:real^1,lift ep)` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `open:(real^3->bool)->bool`))
                                 (concl th))) THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL] THEN SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `interval(--lift ep,vec 0:real^1)` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `open:(real^3->bool)->bool`))
                                 (concl th))) THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL] THEN SIMP_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `connected:(real^3->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[CONNECTED_INTERVAL];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `connected:(real^3->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[CONNECTED_INTERVAL];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; EXISTS_PASTECART;
                PASTECART_IN_PCROSS] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `t:real^1`
      STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    SUBGOAL_THEN `t:real^1 = vec 0` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `vec 0:real^1`)) (concl th) &&
        can (find_term (fun t -> t = `s:real^3->bool`)) (concl th))) THEN
      EXISTS_TAC `x:real^3` THEN UNDISCH_TAC `(y:real^3) IN s` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `interval(vec 0,lift ep) SUBSET interval(--lift ep,lift ep)` THEN
      UNDISCH_TAC `(t:real^1) IN interval(vec 0,lift ep)` THEN SET_TAC[];
      ASM_MESON_TAC[]];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; EXISTS_PASTECART;
                PASTECART_IN_PCROSS] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `t:real^1`
      STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    SUBGOAL_THEN `t:real^1 = vec 0` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `vec 0:real^1`)) (concl th) &&
        can (find_term (fun t -> t = `s:real^3->bool`)) (concl th))) THEN
      EXISTS_TAC `x:real^3` THEN UNDISCH_TAC `(y:real^3) IN s` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `interval(--lift ep,vec 0) SUBSET interval(--lift ep,lift ep)` THEN
      UNDISCH_TAC `(t:real^1) IN interval(--lift ep,vec 0)` THEN SET_TAC[];
      ASM_MESON_TAC[]];
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC PCROSS_MONO THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC PCROSS_MONO THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real^1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `t IN interval(vec 0,lift ep) \/ t = vec 0 \/
                  t IN interval(--lift ep,vec 0:real^1)` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `pastecart (x:real^3) (t:real^1)` THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
      REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ1_TAC THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ2_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `pastecart (x:real^3) (t:real^1)` THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS]]]);;

(* The set algebra of the local sides (half of it; the other half swaps the *)
(* two pieces).                                                              *)

let MOI_S3CS_SIDES_HALF = prove
 (`!(nn:real^N->bool) n1 n2 mm mm' im om im' om'.
     n1 SUBSET nn /\ n2 SUBSET nn /\ nn SUBSET n1 UNION mm' UNION n2 /\
     nn INTER mm = nn INTER mm' /\ DISJOINT n1 mm' /\ DISJOINT n2 mm' /\
     (n1 SUBSET im' \/ n1 SUBSET om') /\ (n2 SUBSET im' \/ n2 SUBSET om') /\
     (n1 SUBSET im \/ n1 SUBSET om) /\
     im INTER om = {} /\ im INTER mm = {} /\ om INTER mm = {} /\
     im' INTER om' = {} /\ im' INTER mm' = {} /\
     im' SUBSET mm UNION im /\
     ~(nn INTER im' = {}) /\ ~(nn INTER om = {})
     ==> n1 INTER im INTER om' = {}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2 (LABEL_TAC "c2")
   (CONJUNCTS_THEN2 (LABEL_TAC "c3") STRIP_ASSUME_TAC))))))))) THEN
  SUBGOAL_THEN `DISJOINT (n1:real^N->bool) mm /\ DISJOINT (n2:real^N->bool) mm`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "c1" DISJ_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "c3" DISJ_CASES_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REMOVE_THEN "c2" DISJ_CASES_TAC THENL
   [SUBGOAL_THEN `(n2:real^N->bool) SUBSET im` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(nn INTER om:real^N->bool = {})` THEN
    MAP_EVERY UNDISCH_TAC
     [`(n1:real^N->bool) SUBSET im`; `(n2:real^N->bool) SUBSET im`;
      `nn SUBSET n1 UNION mm' UNION (n2:real^N->bool)`;
      `nn INTER mm = nn INTER (mm':real^N->bool)`;
      `im INTER om:real^N->bool = {}`; `om INTER mm:real^N->bool = {}`] THEN
    SET_TAC[];
    UNDISCH_TAC `~(nn INTER im':real^N->bool = {})` THEN
    MAP_EVERY UNDISCH_TAC
     [`(n1:real^N->bool) SUBSET om'`; `(n2:real^N->bool) SUBSET om'`;
      `nn SUBSET n1 UNION mm' UNION (n2:real^N->bool)`;
      `im' INTER om':real^N->bool = {}`; `im' INTER mm':real^N->bool = {}`] THEN
    SET_TAC[]]);;

(* The local sides: near a point p of mm where mm and the bicollared sphere *)
(* mm' agree, the region inside mm and outside mm' is empty, provided the   *)
(* filled mm' lies in the filled mm and p is a limit of outside mm.         *)

let MOI_S3CS_LOCAL_SIDES = prove
 (`!(mm:real^3->bool) mm' w (pc:real^(3,1)finite_sum->real^3) qc p bo.
     closed mm /\ mm SUBSET closure (outside mm) /\
     mm' homeomorphic sphere(vec 0:real^3,&1) /\
     homeomorphism (mm' PCROSS interval[--vec 1:real^1,vec 1],w) (pc,qc) /\
     mm' SUBSET interior w /\ (!x. x IN mm' ==> pc(pastecart x (vec 0)) = x) /\
     mm' UNION inside mm' SUBSET mm UNION inside mm /\
     p IN mm /\ open bo /\ p IN bo /\ bo INTER mm = bo INTER mm'
     ==> ?nn. open nn /\ p IN nn /\ nn INTER inside mm INTER outside mm' = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `mm':real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (mm':real^3->bool) /\ locally connected (mm':real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`mm':real^3->bool`; `sphere(vec 0:real^3,&1)`]
        HOMEOMORPHIC_COMPACTNESS) THEN ASM_REWRITE_TAC[COMPACT_SPHERE];
      MP_TAC(ISPECL [`mm':real^3->bool`; `sphere(vec 0:real^3,&1)`]
        HOMEOMORPHIC_LOCAL_CONNECTEDNESS) THEN ASM_REWRITE_TAC[LOCALLY_CONNECTED_SPHERE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN mm'` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`mm':real^3->bool`; `w:real^3->bool`; `pc:real^(3,1)finite_sum->real^3`;
                 `qc:real^3->real^(3,1)finite_sum`; `p:real^3`; `bo:real^3->bool`]
    MOI_S3CS_LOCAL_PRODUCT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:real^3->bool` (X_CHOOSE_THEN `n1:real^3->bool`
    (X_CHOOSE_THEN `n2:real^3->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `nn:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `nn INTER mm = nn INTER (mm':real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `(nn:real^3->bool) SUBSET bo` THEN
    UNDISCH_TAC `bo INTER mm = bo INTER (mm':real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (mm:real^3->bool) n1 /\ DISJOINT (mm:real^3->bool) n2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`nn INTER mm = nn INTER (mm':real^3->bool)`; `(n1:real^3->bool) SUBSET nn`;
      `(n2:real^3->bool) SUBSET nn`; `DISJOINT (n1:real^3->bool) mm'`;
      `DISJOINT (n2:real^3->bool) mm'`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mm':real^3->bool`; `n1:real^3->bool`] MOI_S5C_CONNECTED_SIDE) THEN
  MP_TAC(ISPECL [`mm':real^3->bool`; `n2:real^3->bool`] MOI_S5C_CONNECTED_SIDE) THEN
  MP_TAC(ISPECL [`mm:real^3->bool`; `n1:real^3->bool`] MOI_S5C_CONNECTED_SIDE) THEN
  MP_TAC(ISPECL [`mm:real^3->bool`; `n2:real^3->bool`] MOI_S5C_CONNECTED_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  (* nn meets inside mm' and outside mm *)
  SUBGOAL_THEN `~(nn INTER inside mm':real^3->bool = {}) /\
                ~(nn INTER outside mm:real^3->bool = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    W(fun (_,w) -> MP_TAC(ISPECL [`nn:real^3->bool`; rand(lhand(rand w))]
      OPEN_INTER_CLOSURE_EQ_EMPTY)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `p:real^3` THEN
    ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPEC `inside mm':real^3->bool` CLOSURE_SUBSET) THEN
      UNDISCH_TAC `frontier(inside mm':real^3->bool) = mm'` THEN
      REWRITE_TAC[frontier] THEN UNDISCH_TAC `(p:real^3) IN mm'` THEN SET_TAC[];
      UNDISCH_TAC `(mm:real^3->bool) SUBSET closure (outside mm)` THEN
      UNDISCH_TAC `(p:real^3) IN mm` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `mm:real^3->bool` INSIDE_INTER_OUTSIDE) THEN
  MP_TAC(ISPEC `mm:real^3->bool` INSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `mm:real^3->bool` OUTSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `mm':real^3->bool` OUTSIDE_NO_OVERLAP) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `inside mm' SUBSET mm UNION inside (mm:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `mm' UNION inside mm' SUBSET mm UNION inside (mm:real^3->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside mm' INTER mm':real^3->bool = {}` ASSUME_TAC THENL
   [REWRITE_TAC[INSIDE_NO_OVERLAP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`nn:real^3->bool`; `n1:real^3->bool`; `n2:real^3->bool`;
                 `mm:real^3->bool`; `mm':real^3->bool`; `inside mm:real^3->bool`;
                 `outside mm:real^3->bool`; `inside mm':real^3->bool`;
                 `outside mm':real^3->bool`] MOI_S3CS_SIDES_HALF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`nn:real^3->bool`; `n2:real^3->bool`; `n1:real^3->bool`;
                 `mm:real^3->bool`; `mm':real^3->bool`; `inside mm:real^3->bool`;
                 `outside mm:real^3->bool`; `inside mm':real^3->bool`;
                 `outside mm':real^3->bool`] MOI_S3CS_SIDES_HALF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `nn SUBSET n1 UNION mm' UNION (n2:real^3->bool)` THEN SET_TAC[];
    DISCH_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`n1 INTER inside mm INTER outside mm':real^3->bool = {}`;
    `n2 INTER inside mm INTER outside mm':real^3->bool = {}`;
    `nn SUBSET n1 UNION mm' UNION (n2:real^3->bool)`;
    `outside mm' INTER mm':real^3->bool = {}`] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 4. INSIDE (Moise p.218, case 2).  The region inside the torus            *)
(* M and outside the sphere M' is the inside of the handle sphere           *)
(* a UNION d1 UNION d2 (its frontier lies in the handle sphere by the local *)
(* sides at the bicollar of M'); so X = X' UNION hb with X' INTER hb =      *)
(* d1 UNION d2, and HANDLE_SOLID_TORUS applies.                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CS_HANDLE_REGION = prove
 (mk_imp(`MOISE_266_STATEMENT`,
  `!(mm:real^3->bool) (m':(real^3->bool)->bool) sg.
     compact mm /\ mm SUBSET closure (outside mm) /\
     FINITE m' /\ combinatorial_manifold 2 m' /\
     UNIONS m' homeomorphic sphere(vec 0:real^3,&1) /\
     sg homeomorphic sphere(vec 0:real^3,&1) /\
     mm DIFF sg = UNIONS m' DIFF sg /\ sg SUBSET mm UNION UNIONS m' /\
     UNIONS m' UNION inside (UNIONS m') SUBSET mm UNION inside mm /\
     ~(inside mm INTER outside (UNIONS m') = {})
     ==> inside mm INTER outside (UNIONS m') = inside sg`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m':(real^3->bool)->bool`; `(:real^3)`]
    (MP SURFACE_BICOLLAR_R3 (ASSUME `MOISE_266_STATEMENT`))) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` (X_CHOOSE_THEN `pc:real^(3,1)finite_sum->real^3`
    (X_CHOOSE_THEN `qc:real^3->real^(3,1)finite_sum` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `homeomorphism (UNIONS m' PCROSS interval[--vec 1:real^1,vec 1],w)
                  ((pc:real^(3,1)finite_sum->real^3),qc)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  ABBREV_TAC `mm' = UNIONS (m':(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `compact (mm':real^3->bool) /\ compact (sg:real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`mm':real^3->bool`; `sphere(vec 0:real^3,&1)`]
        HOMEOMORPHIC_COMPACTNESS);
      MP_TAC(ISPECL [`sg:real^3->bool`; `sphere(vec 0:real^3,&1)`]
        HOMEOMORPHIC_COMPACTNESS)] THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE];
    ALL_TAC] THEN
  ABBREV_TAC `u = inside mm INTER outside (mm':real^3->bool)` THEN
  SUBGOAL_THEN `open (u:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC OPEN_INTER THEN
    ASM_SIMP_TAC[OPEN_INSIDE; OPEN_OUTSIDE; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  (* the frontier of the region lies in sg *)
  SUBGOAL_THEN `frontier u SUBSET (sg:real^3->bool)` ASSUME_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MOI_S5C_BOUNDED_CLOPEN_INSIDE THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `inside mm:real^3->bool` THEN
      ASM_SIMP_TAC[BOUNDED_INSIDE; COMPACT_IMP_BOUNDED] THEN EXPAND_TAC "u" THEN
      REWRITE_TAC[INTER_SUBSET];
      EXPAND_TAC "u" THEN
      MP_TAC(ISPEC `mm:real^3->bool` INSIDE_NO_OVERLAP) THEN
      MP_TAC(ISPEC `mm':real^3->bool` OUTSIDE_NO_OVERLAP) THEN
      UNDISCH_TAC `(sg:real^3->bool) SUBSET mm UNION mm'` THEN SET_TAC[];
      UNDISCH_TAC `frontier u SUBSET (sg:real^3->bool)` THEN
      ASM_SIMP_TAC[frontier; INTERIOR_OPEN] THEN SET_TAC[]]] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(p:real^3) IN mm` ASSUME_TAC THENL
   [MP_TAC(ISPEC `mm:real^3->bool` FRONTIER_INSIDE_SUBSET) THEN
    MP_TAC(ISPEC `mm':real^3->bool` FRONTIER_OUTSIDE_SUBSET) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    MP_TAC(ISPECL [`inside mm:real^3->bool`; `outside mm':real^3->bool`]
      FRONTIER_INTER_SUBSET) THEN
    UNDISCH_TAC `(p:real^3) IN frontier u` THEN EXPAND_TAC "u" THEN
    UNDISCH_TAC `~((p:real^3) IN sg)` THEN
    UNDISCH_TAC `mm DIFF sg = (mm':real^3->bool) DIFF sg` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mm:real^3->bool`; `mm':real^3->bool`; `w:real^3->bool`;
                 `pc:real^(3,1)finite_sum->real^3`; `qc:real^3->real^(3,1)finite_sum`;
                 `p:real^3`; `(:real^3) DIFF sg`] MOI_S3CS_LOCAL_SIDES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; GSYM closed; IN_DIFF; IN_UNIV] THEN
    UNDISCH_TAC `mm DIFF sg = (mm':real^3->bool) DIFF sg` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `nn INTER u:real^3->bool = {}` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`nn:real^3->bool`; `u:real^3->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(p:real^3) IN frontier u` THEN REWRITE_TAC[frontier] THEN
  UNDISCH_TAC `(p:real^3) IN nn` THEN SET_TAC[]);;

(* SET_TAC with every UNIONS subterm of the goal generalized to a variable *)
(* first (SET_TAC would otherwise expand UNIONS into existentials).          *)

let MOI_S3CS_UNIONS_SET_TAC : tactic =
  W(fun (_,w) ->
    let us = setify (find_terms (fun t -> is_comb t && is_const(rator t) &&
                                          fst(dest_const(rator t)) = "UNIONS") w) in
    EVERY (map (fun u -> SPEC_TAC(u,genvar(type_of u))) us)) THEN
  SET_TAC[];;

let S307_INSIDE = prove
 (MOI_S30_307_INSIDE,
  REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sd") (CONJUNCTS_THEN2 (LABEL_TAC "m266")
    (CONJUNCTS_THEN2 (LABEL_TAC "sch") (CONJUNCTS_THEN2 (LABEL_TAC "ss")
    (CONJUNCTS_THEN2 (LABEL_TAC "se") (CONJUNCTS_THEN2 (LABEL_TAC "bd")
    (CONJUNCTS_THEN2 (LABEL_TAC "ev") (CONJUNCTS_THEN2 (LABEL_TAC "hst")
    (LABEL_TAC "du"))))))))) THEN
  MAP_EVERY X_GEN_TAC [`s1:real^3->bool`; `s2:real^3->bool`; `m:(real^3->bool)->bool`;
    `x:(real^3->bool)->bool`; `s:real^3->bool`; `d:real^3->bool`;
    `f:real^3->real^3`; `g:real^3->real^3`] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `UNIONS (x:(real^3->bool)->bool) = UNIONS m UNION inside (UNIONS m)` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `d:real^3->bool`; `f:real^3->real^3`;
                 `g:real^3->real^3`] MOI_S3CS_RIM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `j = IMAGE (f:real^3->real^3) (relative_frontier s)` THEN
  (* split along d inside v = interior s2 *)
  USE_THEN "sd" (MP_TAC o SPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`;
    `j:real^3->bool`; `interior s2:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_INTERIOR]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3->bool` (X_CHOOSE_THEN `j1:real^3->bool`
    (X_CHOOSE_THEN `j2:real^3->bool` (X_CHOOSE_THEN `d1:real^3->bool`
      (X_CHOOSE_THEN `d2:real^3->bool` (X_CHOOSE_THEN `m':(real^3->bool)->bool`
        STRIP_ASSUME_TAC)))))) THEN
  UNDISCH_TAC `UNIONS (m':(real^3->bool)->bool) = (UNIONS m DIFF a) UNION d1 UNION d2` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  (* the new surface is a sphere *)
  SUBGOAL_THEN `pl_sphere 2 (UNIONS (m':(real^3->bool)->bool))` ASSUME_TAC THENL
   [USE_THEN "ss" (fun ss -> USE_THEN "se" (fun se -> USE_THEN "bd" (fun bd ->
      USE_THEN "ev" (fun ev ->
        MP_TAC(SPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j:real^3->bool`;
                      `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`;
                      `d2:real^3->bool`; `m':(real^3->bool)->bool`]
          (MP MOI_S3CS_SPHERE_STEP (CONJ ss (CONJ se (CONJ bd ev))))))))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_ADD_LID] THEN
      UNDISCH_TAC `(a:real^3->bool) SUBSET UNIONS m INTER interior s2` THEN
      MOI_S3CS_UNIONS_SET_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* the new 3-manifold, inside X *)
  FIRST_X_ASSUM(MP_TAC o SPEC `x:(real^3->bool)->bool` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t &&
                             fst(dest_const t) = "combinatorial_manifold_with_boundary"))
        (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    can (find_term (fun t ->
      t = `DISJOINT (d:real^3->bool) (UNIONS (x':(real^3->bool)->bool))`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* X' is a ball *)
  SUBGOAL_THEN `compact (UNIONS (x':(real^3->bool)->bool)) /\
                compact (UNIONS (x:(real^3->bool)->bool))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S3D_X_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(d1 DIFF j1:real^3->bool = {}) /\ ~(d2 DIFF j2:real^3->bool = {}) /\
                ~(d DIFF j:real^3->bool = {})` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_S5C_CELL_INTERIOR_NONEMPTY THEN
    EXISTS_TAC `2` THEN ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(interior (UNIONS (x':(real^3->bool)->bool)) = {})` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3CS_CMWB_INTERIOR THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `UNIONS (x':(real^3->bool)->bool)` FRONTIER_SUBSET_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(UNIONS m DIFF a) UNION d1 UNION d2 = UNIONS (m':(real^3->bool)->bool)` THEN
    UNDISCH_TAC `~(d1 DIFF j1:real^3->bool = {})` THEN
    MOI_S3CS_UNIONS_SET_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (m':(real^3->bool)->bool)`; `UNIONS (x':(real^3->bool)->bool)`]
    MOI_S5C_FILL_CHAR) THEN
  ASM_SIMP_TAC[MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC; DIMINDEX_3; ARITH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN
  SUBGOAL_THEN `pl_ball 3 (UNIONS (x':(real^3->bool)->bool))` ASSUME_TAC THENL
   [USE_THEN "sch" (MP_TAC o SPEC `UNIONS (m':(real^3->bool)->bool)` o
      REWRITE_RULE[PL_SCHOENFLIES_3_STATEMENT]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the ends and the handle sphere *)
  MP_TAC(ISPECL [`a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
    MOI_S5C_ANN_ENDS_SUBSET) THEN
  MP_TAC(ISPECL [`2`; `d1:real^3->bool`; `j1:real^3->bool`] MOI_S5C_CELL_COMPACT2) THEN
  MP_TAC(ISPECL [`2`; `d2:real^3->bool`; `j2:real^3->bool`] MOI_S5C_CELL_COMPACT2) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `d1 INTER a = j1:real^3->bool /\ d2 INTER a = j2:real^3->bool`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`d1 INTER UNIONS m = j1:real^3->bool`; `d2 INTER UNIONS m = j2:real^3->bool`;
      `(a:real^3->bool) SUBSET UNIONS m INTER interior s2`;
      `(j1:real^3->bool) SUBSET a`; `(j2:real^3->bool) SUBSET a`;
      `(j1:real^3->bool) SUBSET d1`; `(j2:real^3->bool) SUBSET d2`] THEN
    MOI_S3CS_UNIONS_SET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 ((a:real^3->bool) UNION d1 UNION d2)` ASSUME_TAC THENL
   [USE_THEN "du" (fun du -> MATCH_MP_TAC(MP MOI_S3CS_SIGMA_SPHERE du)) THEN
    MAP_EVERY EXISTS_TAC [`j1:real^3->bool`; `j2:real^3->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(a:real^3->bool) UNION d1 UNION d2` MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `UNIONS (m':(real^3->bool)->bool)` MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `pl_ball 3 (((a:real^3->bool) UNION d1 UNION d2) UNION inside (a UNION d1 UNION d2)) /\
    frontier (((a:real^3->bool) UNION d1 UNION d2) UNION inside (a UNION d1 UNION d2)) =
    a UNION d1 UNION d2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "sch" (MP_TAC o SPEC `(a:real^3->bool) UNION d1 UNION d2` o
        REWRITE_RULE[PL_SCHOENFLIES_3_STATEMENT]) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5C_FILL_FRONTIER THEN ASM_REWRITE_TAC[DIMINDEX_3; ARITH]];
    ALL_TAC] THEN
  (* Moise 26.6 for M: M is the frontier of its outside *)
  USE_THEN "m266" (MP_TAC o SPEC `m:(real^3->bool)->bool` o
    REWRITE_RULE[MOISE_266_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b0:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `UNIONS m SUBSET closure (outside (UNIONS m:real^3->bool))` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier (outside (UNIONS m:real^3->bool)) = UNIONS m` THEN
    REWRITE_TAC[frontier] THEN MOI_S3CS_UNIONS_SET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS m:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier (UNIONS (x:(real^3->bool)->bool)) = UNIONS m` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC COMPACT_FRONTIER THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the region between M and M' is the inside of the handle sphere *)
  SUBGOAL_THEN `UNIONS m' UNION inside (UNIONS m') SUBSET
                UNIONS m UNION inside (UNIONS m:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(inside (UNIONS m) INTER outside (UNIONS m':real^3->bool) = {})`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `UNIONS (m':(real^3->bool)->bool)` INSIDE_UNION_OUTSIDE) THEN
    MAP_EVERY UNDISCH_TAC
     [`~(d DIFF j:real^3->bool = {})`; `(d:real^3->bool) SUBSET UNIONS x`;
      `d INTER UNIONS m = j:real^3->bool`;
      `DISJOINT (d:real^3->bool) (UNIONS (x':(real^3->bool)->bool))`;
      `UNIONS m UNION inside (UNIONS m) = UNIONS (x:(real^3->bool)->bool)`;
      `UNIONS m' UNION inside (UNIONS m') = UNIONS (x':(real^3->bool)->bool)`] THEN
    MOI_S3CS_UNIONS_SET_TAC;
    ALL_TAC] THEN
  USE_THEN "m266" (fun th -> MP_TAC(ISPECL [`UNIONS m:real^3->bool`;
    `m':(real^3->bool)->bool`; `(a:real^3->bool) UNION d1 UNION d2`]
    (MP MOI_S3CS_HANDLE_REGION th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(UNIONS m DIFF a) UNION d1 UNION d2 = UNIONS (m':(real^3->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(a:real^3->bool) SUBSET UNIONS m INTER interior s2` THEN
    MOI_S3CS_UNIONS_SET_TAC;
    DISCH_TAC] THEN
  (* a misses the inside of M' *)
  SUBGOAL_THEN `(a:real^3->bool) INTER inside (UNIONS m') = {}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`UNIONS (x':(real^3->bool)->bool)`; `UNIONS (x:(real^3->bool)->bool)`]
      SUBSET_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `frontier (UNIONS (x:(real^3->bool)->bool)) = UNIONS m` THEN
    REWRITE_TAC[frontier] THEN
    UNDISCH_TAC `(a:real^3->bool) SUBSET UNIONS m INTER interior s2` THEN
    MOI_S3CS_UNIONS_SET_TAC;
    ALL_TAC] THEN
  (* X = X' UNION hb and X' INTER hb = d1 UNION d2 *)
  SUBGOAL_THEN
   `UNIONS (x:(real^3->bool)->bool) =
    UNIONS x' UNION ((a UNION d1 UNION d2) UNION inside (a UNION d1 UNION d2)) /\
    UNIONS (x':(real^3->bool)->bool) INTER
    ((a UNION d1 UNION d2) UNION inside (a UNION d1 UNION d2)) = d1 UNION d2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `UNIONS (m':(real^3->bool)->bool)` INSIDE_UNION_OUTSIDE) THEN
    MP_TAC(ISPEC `UNIONS (m':(real^3->bool)->bool)` INSIDE_INTER_OUTSIDE) THEN
    MP_TAC(ISPEC `UNIONS (m':(real^3->bool)->bool)` OUTSIDE_NO_OVERLAP) THEN
    MAP_EVERY UNDISCH_TAC
     [`UNIONS m UNION inside (UNIONS m) = UNIONS (x:(real^3->bool)->bool)`;
      `UNIONS m' UNION inside (UNIONS m') = UNIONS (x':(real^3->bool)->bool)`;
      `UNIONS (x':(real^3->bool)->bool) SUBSET UNIONS x`;
      `(UNIONS m DIFF a) UNION d1 UNION d2 = UNIONS (m':(real^3->bool)->bool)`;
      `inside (UNIONS m) INTER outside (UNIONS m') =
       inside ((a:real^3->bool) UNION d1 UNION d2)`;
      `(a:real^3->bool) INTER inside (UNIONS m') = {}`;
      `(a:real^3->bool) SUBSET UNIONS m INTER interior s2`] THEN
    MOI_S3CS_UNIONS_SET_TAC;
    ALL_TAC] THEN
  (* the handle *)
  UNDISCH_TAC
   `UNIONS (x:(real^3->bool)->bool) =
    UNIONS x' UNION ((a UNION d1 UNION d2) UNION inside (a UNION d1 UNION d2))` THEN
  DISCH_THEN SUBST1_TAC THEN
  USE_THEN "hst" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`d1:real^3->bool`; `j1:real^3->bool`; `d2:real^3->bool`;
                        `j2:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(UNIONS m DIFF a) UNION d1 UNION d2 = UNIONS (m':(real^3->bool)->bool)` THEN
  MOI_S3CS_UNIONS_SET_TAC);;


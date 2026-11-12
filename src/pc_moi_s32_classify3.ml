(* ========================================================================= *)
(* pc_moi_s32_classify3: Moise Sec 32 Types 1-3, pp.226-227.  Main theorem  *)
(* CLASSIFY_3 |- MOI_S32_CLASSIFY_3 of pc_moi_s3032_stmt6: a state3 at all  *)
(* levels is reduced.  Per member c of level i: every component of c INTER  *)
(* K is essential; the history witness c0 in T''_(2i+1) has the same        *)
(* essential polygons, which are essential in T''_(2i+1) (31.4; solid tori  *)
(* are not simply connected); in the torus there are 0 or 2 of them (28.6,  *)
(* a parallel copy for one), and with 2 the Euler count gives chi + (number *)
(* of inessential polygons) = 0 for c0, so chi = 0 for c, an annulus by     *)
(* SURFACE_PLANAR.                                                          *)
(* ========================================================================= *)

needs "src/pc_moi_s32_init.ml";;
needs "src/pc_moi_s28_plane.ml";;
needs "src/pc_moi_fnd_surfb0.ml";;
needs "src/pc_moi_s26_surf.ml";;
needs "src/pc_moi_s30_cut_a.ml";;
needs "src/pc_moi_s3032_stmt6.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Part 1: at all levels every component of c INTER K is essential.        *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CF_EVENS_SPLIT = prove
 (`!(g:real^3->real^3) v pp dd s2 i (c:real^3->bool).
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     c INTER moi_s32_evens s2 SUBSET frontier (s2 (&2 * i)) UNION frontier (s2 (&2 * i + &2))
     ==> components (c INTER moi_s32_evens s2) =
         components (c INTER frontier (s2 (&2 * i))) UNION
         components (c INTER frontier (s2 (&2 * i + &2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (frontier ((s2:int->real^3->bool) (&2 * i)))
                         (frontier (s2 (&2 * i + &2))) /\
                closed (frontier ((s2:int->real^3->bool) (&2 * i))) /\
                closed (frontier ((s2:int->real^3->bool) (&2 * i + &2)))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `i:int` (MATCH_MP MOI_S3I2_LEVEL_FACTS
      (CONJ (ASSUME `moi_s32_model g v`) (ASSUME `moi_s32_tower g v pp dd s2`)))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "kf") (ASSUME_TAC o CONJUNCT1)) THEN
    USE_THEN "kf" (MP_TAC o SPEC `&2 * i:int`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "kf" (MP_TAC o SPEC `&2 * i + &2:int`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[FRONTIER_CLOSED] THEN
    UNDISCH_TAC `DISJOINT ((s2:int->real^3->bool) (&2 * i)) (s2 (&2 * i + &2))` THEN
    UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET s2 (&2 * i)` THEN
    UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i + &2)) SUBSET s2 (&2 * i + &2)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET moi_s32_evens s2 /\
                frontier (s2 (&2 * i + &2)) SUBSET moi_s32_evens s2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s32_evens; SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THENL
     [EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `i + &1:int` THEN
      ASM_REWRITE_TAC[INT_ARITH `&2 * (i + &1) = &2 * i + &2:int`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->bool) INTER moi_s32_evens s2 =
                (c INTER frontier (s2 (&2 * i))) UNION (c INTER frontier (s2 (&2 * i + &2)))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `(c:real^3->bool) INTER moi_s32_evens s2 SUBSET
                 frontier (s2 (&2 * i)) UNION frontier (s2 (&2 * i + &2))` THEN
    UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET moi_s32_evens s2` THEN
    UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i + &2)) SUBSET moi_s32_evens s2` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPONENTS_SEPARATED_UNION THEN
  SUBGOAL_THEN `closure ((c:real^3->bool) INTER frontier (s2 (&2 * i))) SUBSET
                frontier ((s2:int->real^3->bool) (&2 * i)) /\
                closure ((c:real^3->bool) INTER frontier (s2 (&2 * i + &2))) SUBSET
                frontier ((s2:int->real^3->bool) (&2 * i + &2))`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (frontier ((s2:int->real^3->bool) (&2 * i)))
                        (frontier (s2 (&2 * i + &2)))` THEN
  SET_TAC[]);;

let MOI_S3CF_INESS_EMPTY = prove
 (`!(g:real^3->real^3) v pp dd s2 i (c:real^3->bool).
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     c INTER moi_s32_evens s2 SUBSET frontier (s2 (&2 * i)) UNION frontier (s2 (&2 * i + &2)) /\
     (!jj. jj IN components (c INTER frontier (s2 (&2 * i)))
           ==> moi_s32_ess s2 (&2 * i) jj) /\
     (!jj. jj IN components (c INTER frontier (s2 (&2 * i + &2)))
           ==> moi_s32_ess s2 (&2 * i + &2) jj)
     ==> moi_s32_inessc s2 i c = {} /\
         moi_s32_essc s2 i c = components (c INTER moi_s32_evens s2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `c:real^3->bool`]
                MOI_S3CF_EVENS_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[moi_s32_inessc; moi_s32_essc; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Part 2: Lemma 2 of p.225 in the form used here: a crossing polygon       *)
(* bounds a 2-cell in one of the two crossing frontiers iff in the other    *)
(* (31.4; a polygon carrying the loops of a solid torus bounds no 2-cell    *)
(* in it, since a solid torus is not simply connected).                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CF_SOLID_TORUS_NOT_SC = prove
 (`!s:real^3->bool. solid_torus s ==> ~simply_connected s /\ path_connected s`,
  GEN_TAC THEN REWRITE_TAC[solid_torus] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP HOMEOMORPHIC_SIMPLY_CONNECTED_EQ th;
                                     MATCH_MP HOMEOMORPHIC_PATH_CONNECTEDNESS th]) THEN
  REWRITE_TAC[SIMPLY_CONNECTED_PCROSS_EQ; PATH_CONNECTED_PCROSS_EQ;
              SIMPLY_CONNECTED_SPHERE_EQ; CBALL_EQ_EMPTY; SPHERE_EQ_EMPTY; DIMINDEX_2] THEN
  CONV_TAC(DEPTH_CONV NUM_LE_CONV) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[] THEN CONJ_TAC THEN
  SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; CONVEX_CBALL; PATH_CONNECTED_SPHERE; DIMINDEX_2;
           LE_REFL]);;

let MOI_S3CF_CARRIED_NO_DISK = prove
 (`!(s:real^3->bool) j d.
     solid_torus s /\ loops_carried j s /\ d SUBSET s /\ pl_cell_with_boundary 2 d j
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3CF_SOLID_TORUS_NOT_SC) THEN
  UNDISCH_TAC `~simply_connected (s:real^3->bool)` THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^3->bool) j` THEN
  REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `h:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `simply_connected (d:real^3->bool) /\ (j:real^3->bool) SUBSET d`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTRACTIBLE_IMP_SIMPLY_CONNECTED THEN
      MATCH_MP_TAC(ISPECL [`k:real^3->bool`; `d:real^3->bool`] HOMEOMORPHIC_CONTRACTIBLE) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[homeomorphic] THEN
        MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `h:real^3->real^3`] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONVEX_IMP_CONTRACTIBLE THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `relative_frontier k SUBSET (k:real^3->bool)` MP_TAC THENL
       [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
        ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
        UNDISCH_TAC `IMAGE (f:real^3->real^3) k = d` THEN SET_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_SOME] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:real^1->real^3` THEN STRIP_TAC THEN
  UNDISCH_TAC `loops_carried (j:real^3->bool) s` THEN REWRITE_TAC[loops_carried] THEN
  DISCH_THEN(MP_TAC o SPEC `p:real^1->real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `pathstart (q:real^1->real^3)` THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `q:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN EXISTS_TAC `q:real^1->real^3` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN
  EXISTS_TAC `d:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `simply_connected (d:real^3->bool)` THEN
  REWRITE_TAC[SIMPLY_CONNECTED_EQ_CONTRACTIBLE_LOOP_ANY] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `q:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN ASM SET_TAC[]);;

(* The crossing dichotomy transferred: for a crossing polygon of T''_b and *)
(* T''_(b+1) in the tower, bounding a 2-cell in one is bounding in the     *)
(* other.                                                                    *)

let MOI_S3CF_ESS_TRANSFER = prove
 (`!(g:real^3->real^3) v pp dd s2 b (jj:real^3->bool).
     MOISE_314_STATEMENT /\
     (!s:real^3->bool. pl_solid_torus s ==> solid_torus s /\ (?j. spine j s /\ pl_sphere 1 j)) /\
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     pl_sphere 1 jj /\ jj SUBSET frontier (s2 b) INTER frontier (s2 (b + &1))
     ==> ((?d. d SUBSET frontier (s2 b) /\ pl_cell_with_boundary 2 d jj) <=>
          (?d. d SUBSET frontier (s2 (b + &1)) /\ pl_cell_with_boundary 2 d jj))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "m314") (CONJUNCTS_THEN2 (LABEL_TAC "bas")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!k:int. solid_torus ((s2:int->real^3->bool) k) /\
                        frontier (s2 k) SUBSET s2 k` (LABEL_TAC "st") THENL
   [X_GEN_TAC `k:int` THEN
    MP_TAC(SPEC `k:int` (MATCH_MP MOI_S3GF_TOWER_TORI
      (ASSUME `moi_s32_tower g v pp dd s2`))) THEN STRIP_TAC THEN
    USE_THEN "bas" (MP_TAC o C MATCH_MP
      (ASSUME `pl_solid_torus ((s2:int->real^3->bool) k)`)) THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  USE_THEN "m314" (MP_TAC o SPECL
    [`\k. (pp:int->real^3) (b + &k)`; `\k. (dd:int->real^3->bool) (b + &k)`;
     `g:real^3->real^3`; `\k. (s2:int->real^3->bool) (b + &k)`; `0`; `jj:real^3->bool`] o
    GEN_REWRITE_RULE I [MOISE_314_STATEMENT]) THEN
  REWRITE_TAC[ARITH; INT_ADD_RID] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `moi_s32_tower g v pp dd s2` THEN
    REWRITE_TAC[moi_s32_tower] THEN SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC(TAUT `~p /\ ~q ==> (p <=> q)`) THEN CONJ_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_S3CF_CARRIED_NO_DISK THENL
     [MAP_EVERY EXISTS_TAC [`(s2:int->real^3->bool) b`; `jj:real^3->bool`; `d:real^3->bool`];
      MAP_EVERY EXISTS_TAC [`(s2:int->real^3->bool) (b + &1)`; `jj:real^3->bool`;
                            `d:real^3->bool`]] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "st" (fun th -> MP_TAC(SPEC `b:int` th) THEN MP_TAC(SPEC `b + &1:int` th)) THEN
    ASM SET_TAC[];
    ASM_MESON_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Part 3: surfaces inside a surface.  In a set x that is locally R^2       *)
(* at every point, a subset homeomorphic to the plane is open (invariance   *)
(* of domain, MOI_S8CU_IOD); so the interior of a combinatorial surface in  *)
(* x is open in x, and no neighbourhood in x of a boundary point lies in    *)
(* the surface.                                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CF_R2_OPEN = prove
 (`!(x:real^3->bool) u.
     (!y. y IN x ==> moi_s28_locally_r2 x y) /\ u SUBSET x /\ u homeomorphic (:real^2)
     ==> open_in (subtopology euclidean x) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:real^3->real^2` (X_CHOOSE_THEN `h:real^2->real^3`
    ASSUME_TAC) o GEN_REWRITE_RULE I [homeomorphic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `!p q. p IN (:real^2) /\ q IN (:real^2) /\ (h:real^2->real^3) p = h q
                      ==> p = q` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_MESON_TAC[IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN IMAGE (h:real^2->real^3) (:real^2) ==> moi_s8ta_emb2 x y`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S8TA_EMB2_OF THEN DISJ1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^2->real^3) (:real^2) SUBSET x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `h:real^2->real^3`; `(:real^2)`] MOI_S8CU_IOD) THEN
  ASM_REWRITE_TAC[OPEN_UNIV]);;

let MOI_S3CF_SURF_BOUNDARY_SUBSET = prove
 (`!c:(real^3->bool)->bool. surface_boundary c SUBSET UNIONS c`,
  REWRITE_TAC[surface_boundary] THEN SET_TAC[]);;

let MOI_S3CF_SURF_INTERIOR_OPEN = prove
 (`!(x:real^3->bool) (e:(real^3->bool)->bool).
     (!y. y IN x ==> moi_s28_locally_r2 x y) /\
     FINITE e /\ combinatorial_manifold_with_boundary 2 e /\ UNIONS e SUBSET x
     ==> open_in (subtopology euclidean x) (UNIONS e DIFF surface_boundary e)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:(real^3->bool)->bool`; `y:real^3`] MOI_S8TA_NONR2_BD) THEN
  ASM_REWRITE_TAC[moi_s28_locally_r2] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(u:real^3->bool) SUBSET UNIONS e` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3CF_R2_OPEN THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`e:(real^3->bool)->bool`; `z:real^3`] MOI_S8TA_BD_NO_R2) THEN
    ASM_REWRITE_TAC[moi_s28_locally_r2] THEN EXISTS_TAC `u:real^3->bool` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S3CF_SURF_BD_NOT_INTERIOR = prove
 (`!(x:real^3->bool) (e:(real^3->bool)->bool) y v.
     (!y. y IN x ==> moi_s28_locally_r2 x y) /\
     FINITE e /\ combinatorial_manifold_with_boundary 2 e /\ UNIONS e SUBSET x /\
     y IN surface_boundary e /\ open_in (subtopology euclidean x) v /\ y IN v
     ==> ~(v SUBSET UNIONS e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`e:(real^3->bool)->bool`; `y:real^3`] MOI_S8TA_BD_NO_R2) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`x:real^3->bool`; `v:real^3->bool`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPEC `e:(real^3->bool)->bool` MOI_S3CF_SURF_BOUNDARY_SUBSET) THEN ASM SET_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Part 4: the torus T = frontier s (locally R^2, compact, connected),       *)
(* 2-cells in it (triangulated as surfaces, interiors open in T), and the   *)
(* closure of the interior of a surface.                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CF_TORUS_FACTS = prove
 (`!(s:real^3->bool).
     pl_solid_torus s /\
     (?(f:real^(2,2)finite_sum->real^3) h.
        pl_homeomorphism (pl_torus_model,frontier s) (f,h))
     ==> (!y. y IN frontier s ==> moi_s28_locally_r2 (frontier s) y) /\
         compact (frontier s) /\ connected (frontier s)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `f:real^(2,2)finite_sum->real^3`
      (X_CHOOSE_THEN `h:real^3->real^(2,2)finite_sum` ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S8TO_PL_TORUS_R2 THEN
    MAP_EVERY EXISTS_TAC [`f:real^(2,2)finite_sum->real^3`; `h:real^3->real^(2,2)finite_sum`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_FRONTIER THEN
    ASM_MESON_TAC[MOI_S3I2_SOLID_TORUS_REGULAR];
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    UNDISCH_TAC `IMAGE (f:real^(2,2)finite_sum->real^3) pl_torus_model = frontier s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[MOI_S8TO_MODEL_FACTS]]);;

let MOI_S3CF_CELL_COMPLEX = prove
 (`!(d:real^3->bool) j.
     pl_cell_with_boundary 2 d j
     ==> ?L. FINITE L /\ simplicial_complex L /\ combinatorial_manifold_with_boundary 2 L /\
             UNIONS L = d /\ surface_boundary L = j /\ (!s. s IN L ==> aff_dim s <= &2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (d:real^3->bool)` MP_TAC THENL
   [UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^3->bool) j` THEN
    REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `L:(real^3->bool)->bool` THEN
  MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`]
                MOI_S3CA_DISK_TRI) THEN
  SUBGOAL_THEN `FINITE (L:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

let MOI_S3CF_SURF_CLOSURE_INTERIOR = prove
 (`!e:(real^3->bool)->bool.
     FINITE e /\ combinatorial_manifold_with_boundary 2 e
     ==> UNIONS e SUBSET closure (UNIONS e DIFF surface_boundary e)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(y:real^3) IN surface_boundary e` THENL
   [ALL_TAC;
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN ASM_REWRITE_TAC[IN_DIFF]] THEN
  SUBGOAL_THEN `simplicial_complex (e:(real^3->bool)->bool)` MP_TAC THENL
   [REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 2 (e:(real^3->bool)->bool)` THEN
    SIMP_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  REWRITE_TAC[simplicial_complex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "simp")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "inter")))) THEN
  UNDISCH_TAC `(y:real^3) IN surface_boundary e` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [surface_boundary] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~({r:real^3->bool | r IN e /\ aff_dim r = &2 /\ s SUBSET r} = {})`
  MP_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `CARD {r:real^3->bool | r IN e /\ aff_dim r = &2 /\ s SUBSET r} = 1` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `relative_interior (t:real^3->bool) SUBSET UNIONS e DIFF surface_boundary e`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `t:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(x:real^3) IN relative_interior t` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `s':real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s':real^3->bool) INTER t face_of t` ASSUME_TAC THENL
     [USE_THEN "inter" (MP_TAC o SPECL [`s':real^3->bool`; `t:real^3->bool`]) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(s':real^3->bool) INTER t = t` THENL
     [MP_TAC(ISPECL [`t:real^3->bool`; `s':real^3->bool`] AFF_DIM_SUBSET) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(s':real^3->bool) INTER t = t` THEN SET_TAC[]; ASM_REWRITE_TAC[]] THEN
      INT_ARITH_TAC;
      MP_TAC(ISPECL [`(s':real^3->bool) INTER t`; `t:real^3->bool`]
                    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `t:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(x:real^3) IN relative_interior t` THEN
      UNDISCH_TAC `(x:real^3) IN s'` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3->bool) SUBSET closure (relative_interior t)` ASSUME_TAC THENL
   [SUBGOAL_THEN `convex (t:real^3->bool) /\ closed t` STRIP_ASSUME_TAC THENL
     [USE_THEN "simp" (X_CHOOSE_TAC `n:int` o C MATCH_MP (ASSUME `(t:real^3->bool) IN e`)) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SIMPLEX_IMP_CONVEX THEN EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC SIMPLEX_IMP_COMPACT THEN
        EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED; SUBSET_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_interior (t:real^3->bool)`;
                 `UNIONS e DIFF surface_boundary (e:(real^3->bool)->bool)`] SUBSET_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(t:real^3->bool) SUBSET closure (relative_interior t)` THEN
  UNDISCH_TAC `(s:real^3->bool) SUBSET t` THEN UNDISCH_TAC `(y:real^3) IN s` THEN
  SET_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Part 5: the caps.  For a connected surface c0 in x (locally R^2)         *)
(* not contained in a 2-cell d of x bounded by one of its boundary          *)
(* polygons, c0 meets d only in that polygon; two such caps are disjoint.  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CF_CONNECTED_OPEN_SIDE = prove
 (`!(x:real^3->bool) s u v.
     connected s /\ s SUBSET x /\ s SUBSET u UNION v /\
     open_in (subtopology euclidean x) u /\ open_in (subtopology euclidean x) v /\
     DISJOINT u v
     ==> s SUBSET u \/ s SUBSET v`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `connected (s:real^3->bool)` THEN REWRITE_TAC[CONNECTED_OPEN_IN] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`(s:real^3->bool) INTER u`; `(s:real^3->bool) INTER v`]) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `x:real^3->bool`; `u:real^3->bool`]
                MOI_S8CU_OPEN_IN_SUBSET_INTER) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `x:real^3->bool`; `v:real^3->bool`]
                MOI_S8CU_OPEN_IN_SUBSET_INTER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3CF_CELL_FACTS = prove
 (`!(x:real^3->bool) d j.
     (!y. y IN x ==> moi_s28_locally_r2 x y) /\ d SUBSET x /\ pl_cell_with_boundary 2 d j
     ==> open_in (subtopology euclidean x) (d DIFF j) /\
         open_in (subtopology euclidean x) (x DIFF d) /\
         compact d /\ connected d /\ j SUBSET d /\
         d SUBSET closure (d DIFF j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `L:(real^3->bool)->bool` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S3CF_CELL_COMPLEX) THEN
  SUBGOAL_THEN `compact (d:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS L = (d:real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_S8CU_PL_POLYHEDRON_COMPACT THEN
    REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
    EXISTS_TAC `L:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`x:real^3->bool`; `L:(real^3->bool)->bool`]
                   MOI_S3CF_SURF_INTERIOR_OPEN) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `(:real^3) DIFF d` THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED] THEN SET_TAC[];
    UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^3->bool) j` THEN
    REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
    UNDISCH_TAC `UNIONS L = (d:real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `surface_boundary L = (j:real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MOI_S3CF_SURF_BOUNDARY_SUBSET];
    UNDISCH_TAC `UNIONS L = (d:real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `surface_boundary L = (j:real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_S3CF_SURF_CLOSURE_INTERIOR THEN ASM_REWRITE_TAC[]]);;

let MOI_S3CF_CAP_OUTSIDE = prove
 (`!(x:real^3->bool) (cc0:(real^3->bool)->bool) d J.
     (!y. y IN x ==> moi_s28_locally_r2 x y) /\
     FINITE cc0 /\ combinatorial_manifold_with_boundary 2 cc0 /\
     connected (UNIONS cc0) /\ UNIONS cc0 SUBSET x /\
     J SUBSET surface_boundary cc0 /\
     d SUBSET x /\ pl_cell_with_boundary 2 d J /\ ~(UNIONS cc0 SUBSET d)
     ==> UNIONS cc0 INTER (d DIFF J) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `d:real^3->bool`; `J:real^3->bool`] MOI_S3CF_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `cc0:(real^3->bool)->bool` INT_CONNECTED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `cc0:(real^3->bool)->bool`] MOI_S3CF_SURF_INTERIOR_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `cc0:(real^3->bool)->bool` MOI_S3CF_SURF_CLOSURE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`x:real^3->bool`;
                 `UNIONS cc0 DIFF surface_boundary (cc0:(real^3->bool)->bool)`;
                 `(d:real^3->bool) DIFF J`; `(x:real^3->bool) DIFF d`]
                MOI_S3CF_CONNECTED_OPEN_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN STRIP_TAC THENL
   [UNDISCH_TAC `~(UNIONS cc0 SUBSET (d:real^3->bool))` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure (UNIONS cc0 DIFF surface_boundary (cc0:(real^3->bool)->bool))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  UNDISCH_TAC `open_in (subtopology euclidean x) ((d:real^3->bool) DIFF J)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `o1:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:real^3) IN closure (UNIONS cc0 DIFF surface_boundary cc0)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  UNDISCH_TAC `open (o1:real^3->bool)` THEN REWRITE_TAC[open_def] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^3) IN o1` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `UNIONS cc0 DIFF surface_boundary cc0 SUBSET (x:real^3->bool) DIFF d` THEN
  UNDISCH_TAC `(d:real^3->bool) DIFF J = x INTER o1` THEN
  UNDISCH_TAC `(w:real^3) IN UNIONS cc0 DIFF surface_boundary cc0` THEN
  UNDISCH_TAC `(w:real^3) IN o1` THEN
  UNDISCH_TAC `UNIONS cc0 SUBSET (x:real^3->bool)` THEN SET_TAC[]);;

let MOI_S3CF_CAPS_DISJOINT = prove
 (`!(x:real^3->bool) (c0:real^3->bool) d d' J J'.
     (!y. y IN x ==> moi_s28_locally_r2 x y) /\
     J SUBSET c0 /\ J' SUBSET c0 /\ DISJOINT J J' /\ ~(J' = {}) /\
     d SUBSET x /\ pl_cell_with_boundary 2 d J /\
     d' SUBSET x /\ pl_cell_with_boundary 2 d' J' /\
     c0 INTER (d DIFF J) = {} /\ c0 INTER (d' DIFF J') = {}
     ==> DISJOINT d d'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `d:real^3->bool`; `J:real^3->bool`] MOI_S3CF_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `d':real^3->bool`; `J':real^3->bool`]
                MOI_S3CF_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `DISJOINT (J:real^3->bool) d' /\ DISJOINT (J':real^3->bool) d`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `d':real^3->bool`;
                 `(d:real^3->bool) DIFF J`; `(x:real^3->bool) DIFF d`]
                MOI_S3CF_CONNECTED_OPEN_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 6: surface bookkeeping for the torus count.  Finite surfaces        *)
(* are compact; the components of a finite disjoint union of closed         *)
(* connected sets are its members; a boundary minus some of its components *)
(* is the union of the others; gluing 2-cells onto boundary polygons one at *)
(* a time (SURF_GLUE, chi of a 2-cell is 1).                                *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CF_SURF_COMPACT = prove
 (`!e:(real^3->bool)->bool.
     FINITE e /\ combinatorial_manifold_with_boundary 2 e
     ==> simplicial_complex e /\ compact (UNIONS e) /\
         (!s. s IN e ==> aff_dim s <= &2)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (e:(real^3->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 2 (e:(real^3->bool)->bool)` THEN
    SIMP_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_PL_POLYHEDRON_COMPACT THEN
    REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
    EXISTS_TAC `e:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[MOI_FSB_DIM]]);;

let MOI_S3CF_SURF_BOUNDARY_CLOSED = prove
 (`!e:(real^3->bool)->bool.
     FINITE e /\ combinatorial_manifold_with_boundary 2 e
     ==> closed (surface_boundary e)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3CF_SURF_COMPACT) THEN
  REWRITE_TAC[simplicial_complex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "simp" o CONJUNCT1))
    (K ALL_TAC)) THEN
  REWRITE_TAC[surface_boundary] THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `e:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^3->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  USE_THEN "simp" (X_CHOOSE_TAC `n:int` o C MATCH_MP (ASSUME `(t:real^3->bool) IN e`)) THEN
  MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC SIMPLEX_IMP_COMPACT THEN
  EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[]);;

let MOI_S3CF_CELL_CONNECTED = prove
 (`!n (d:real^3->bool) j. pl_cell_with_boundary n d j ==> connected d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  UNDISCH_TAC `IMAGE (f:real^3->real^3) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED]);;

let MOI_S3CF_ANNULUS_ENDS = prove
 (`!(a:real^3->bool) j0 j1.
     pl_annulus_with_ends a j0 j1
     ==> j0 SUBSET a /\ j1 SUBSET a /\ connected a /\ compact a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^3->bool)->bool` STRIP_ASSUME_TAC o
    MATCH_MP ANNULUS_COMPLEX) THEN
  MP_TAC(ISPEC `d:(real^3->bool)->bool` MOI_S3CF_SURF_COMPACT) THEN
  MP_TAC(ISPEC `d:(real^3->bool)->bool` MOI_S3CF_SURF_BOUNDARY_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM SET_TAC[]);;

(* The components of a finite union of disjoint closed connected sets.     *)

let MOI_S3CF_COMPONENT_OF_UNIONS = prove
 (`!(ff:(real^3->bool)->bool) c.
     FINITE ff /\ pairwise DISJOINT ff /\
     (!c. c IN ff ==> closed c /\ connected c /\ ~(c = {})) /\ c IN ff
     ==> c IN components (UNIONS ff)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pd")
    (CONJUNCTS_THEN2 (LABEL_TAC "cl") ASSUME_TAC))) THEN
  USE_THEN "cl" (MP_TAC o C MATCH_MP (ASSUME `(c:real^3->bool) IN ff`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `closed (UNIONS (ff DELETE (c:real^3->bool)))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
    X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
    USE_THEN "cl" (MP_TAC o C MATCH_MP (ASSUME `(t:real^3->bool) IN ff`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->bool) INTER UNIONS (ff DELETE c) = {}` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS; IN_DELETE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    USE_THEN "pd" (MP_TAC o SPECL [`t:real^3->bool`; `c:real^3->bool`] o
      REWRITE_RULE[pairwise]) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN c` THEN UNDISCH_TAC `(y:real^3) IN t` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS ff = (c:real^3->bool) UNION UNIONS (ff DELETE c)` ASSUME_TAC THENL
   [UNDISCH_TAC `(c:real^3->bool) IN ff` THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_COMPONENTS_MAXIMAL] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `d:real^3->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS (ff DELETE (c:real^3->bool)) INTER d = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `connected (d:real^3->bool)` THEN REWRITE_TAC[CONNECTED_CLOSED] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:real^3->bool`; `UNIONS (ff DELETE (c:real^3->bool))`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `a /\ b ==> ~(a /\ b /\ ~c) ==> c`) THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(c:real^3->bool) INTER UNIONS (ff DELETE c) = {}` THEN SET_TAC[];
      UNDISCH_TAC `(c:real^3->bool) SUBSET d` THEN UNDISCH_TAC `~(c:real^3->bool = {})` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `UNIONS (ff DELETE (c:real^3->bool)) INTER d = {}` THEN
  UNDISCH_TAC `(d:real^3->bool) SUBSET c UNION UNIONS (ff DELETE c)` THEN
  UNDISCH_TAC `(c:real^3->bool) SUBSET d` THEN SET_TAC[]);;

let MOI_S3CF_COMPONENTS_UNIONS = prove
 (`!ff:(real^3->bool)->bool.
     FINITE ff /\ pairwise DISJOINT ff /\
     (!c. c IN ff ==> closed c /\ connected c /\ ~(c = {}))
     ==> components (UNIONS ff) = ff`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!c:real^3->bool. c IN ff ==> c IN components (UNIONS ff)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3CF_COMPONENT_OF_UNIONS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `k:real^3->bool` THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`UNIONS ff:real^3->bool`; `k:real^3->bool`] IN_COMPONENTS_NONEMPTY) THEN
    MP_TAC(ISPECL [`UNIONS ff:real^3->bool`; `k:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `?c:real^3->bool. c IN ff /\ ~(c INTER k = {})` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(k:real^3->bool = {})` THEN UNDISCH_TAC `(k:real^3->bool) SUBSET UNIONS ff` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`UNIONS ff:real^3->bool`; `c:real^3->bool`; `k:real^3->bool`]
                  COMPONENTS_EQ) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

(* A boundary minus some of its components is the union of the others.     *)

let MOI_S3CF_SPLIT_COMPONENTS = prove
 (`!(b:real^3->bool) P.
     b DIFF UNIONS {j | j IN components b /\ P j} =
     UNIONS {j | j IN components b /\ ~P j}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPEC `b:real^3->bool` UNIONS_COMPONENTS) THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `j:real^3->bool` THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `j:real^3->bool` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`b:real^3->bool`; `j:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN j` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `j':real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`b:real^3->bool`; `j:real^3->bool`; `j':real^3->bool`] COMPONENTS_EQ) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(j:real^3->bool = j')` (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN j` THEN UNDISCH_TAC `(y:real^3) IN j'` THEN SET_TAC[]]);;

(* Gluing the caps onto a surface, one at a time (SURF_GLUE; a 2-cell has   *)
(* chi 1 by EULER_VALUES).                                                   *)

let MOI_S3CF_GLUE_CAPS = prove
 (mk_imp(moi_n3 MOI_FND_EULER_VALUES,
  `!(cc0:(real^3->bool)->bool) ic (cap:(real^3->bool)->(real^3->bool)).
     FINITE cc0 /\ combinatorial_manifold_with_boundary 2 cc0 /\
     connected (UNIONS cc0) /\
     FINITE ic /\ ic SUBSET components (surface_boundary cc0) /\
     (!J. J IN ic ==> pl_cell_with_boundary 2 (cap J) J /\ UNIONS cc0 INTER cap J = J) /\
     (!J J'. J IN ic /\ J' IN ic /\ ~(J = J') ==> DISJOINT (cap J) (cap J'))
     ==> ?e. FINITE e /\ combinatorial_manifold_with_boundary 2 e /\
             UNIONS e = UNIONS cc0 UNION UNIONS (IMAGE cap ic) /\
             connected (UNIONS e) /\
             surface_boundary e = surface_boundary cc0 DIFF UNIONS ic /\
             complex_euler e = complex_euler cc0 + &(CARD ic)`),
  DISCH_THEN(LABEL_TAC "ev") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "capf") (LABEL_TAC "capd"))))))) THEN
  SUBGOAL_THEN `!K:real^3->bool. K IN ic ==> K IN components (surface_boundary cc0)`
  (LABEL_TAC "comp") THENL
   [UNDISCH_TAC `ic SUBSET components (surface_boundary (cc0:(real^3->bool)->bool))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!jj:(real^3->bool)->bool. FINITE jj ==> jj SUBSET ic ==>
      ?e. FINITE e /\ combinatorial_manifold_with_boundary 2 e /\
          UNIONS e = UNIONS cc0 UNION UNIONS (IMAGE (cap:(real^3->bool)->(real^3->bool)) jj) /\
          connected (UNIONS e) /\
          surface_boundary e = surface_boundary cc0 DIFF UNIONS jj /\
          complex_euler e = complex_euler cc0 + &(CARD jj)`
  (fun th -> MP_TAC(SPEC `ic:(real^3->bool)->bool` th) THEN ASM_REWRITE_TAC[SUBSET_REFL]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `cc0:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; UNION_EMPTY; DIFF_EMPTY; CARD_CLAUSES] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`J:real^3->bool`; `jj:(real^3->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(J:real^3->bool) IN ic /\ jj SUBSET (ic:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(J:real^3->bool) INSERT jj SUBSET ic` THEN SET_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o C MATCH_MP (ASSUME `jj SUBSET (ic:(real^3->bool)->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "capf" (MP_TAC o C MATCH_MP (ASSUME `(J:real^3->bool) IN ic`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(cap:(real^3->bool)->(real^3->bool)) J`; `J:real^3->bool`]
                MOI_S3CF_CELL_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `complex_euler (L:(real^3->bool)->bool) = &1` ASSUME_TAC THENL
   [USE_THEN "ev" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `simplicial_complex (L:(real^3->bool)->bool)`)
            (ASSUME `!s:real^3->bool. s IN L ==> aff_dim s <= &2`))) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3CA_CELL_BALL THEN
    EXISTS_TAC `J:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^3->bool) IN components (surface_boundary cc0)` ASSUME_TAC THENL
   [USE_THEN "comp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(J:real^3->bool = {}) /\ J SUBSET surface_boundary cc0 /\ connected J`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_SUBSET; IN_COMPONENTS_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^3->bool) INTER UNIONS jj = {}` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTER; IN_UNIONS; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `J':real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(J':real^3->bool) IN components (surface_boundary cc0)` ASSUME_TAC THENL
     [USE_THEN "comp" MATCH_MP_TAC THEN
      UNDISCH_TAC `jj SUBSET (ic:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `(J':real^3->bool) IN jj` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`surface_boundary (cc0:(real^3->bool)->bool)`; `J:real^3->bool`;
                   `J':real^3->bool`] COMPONENTS_EQ) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(J:real^3->bool = J')` (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN J` THEN UNDISCH_TAC `(y:real^3) IN J'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (IMAGE (cap:(real^3->bool)->(real^3->bool)) jj) INTER cap J = {}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; UNIONS_IMAGE; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `J':real^3->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    USE_THEN "capd" (MP_TAC o SPECL [`J':real^3->bool`; `J:real^3->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `jj SUBSET (ic:(real^3->bool)->bool)` THEN
        UNDISCH_TAC `(J':real^3->bool) IN jj` THEN SET_TAC[];
        DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN (cap:(real^3->bool)->(real^3->bool)) J` THEN
    UNDISCH_TAC `(y:real^3) IN (cap:(real^3->bool)->(real^3->bool)) J'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS e INTER UNIONS L = (J:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `UNIONS (IMAGE (cap:(real^3->bool)->(real^3->bool)) jj) INTER cap J = {}` THEN
    UNDISCH_TAC `UNIONS cc0 INTER (cap:(real^3->bool)->(real^3->bool)) J = J` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^3->bool) SUBSET surface_boundary e` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(J:real^3->bool) INTER UNIONS jj = {}` THEN
    UNDISCH_TAC `(J:real^3->bool) SUBSET surface_boundary cc0` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!b:real^3->bool. b IN components (surface_boundary e) /\ ~(b INTER J = {})
                                 ==> b SUBSET J` ASSUME_TAC THENL
   [X_GEN_TAC `b:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `surface_boundary (cc0:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`surface_boundary (e:(real^3->bool)->bool)`; `b:real^3->bool`]
                  IN_COMPONENTS_SUBSET) THEN
    MP_TAC(ISPECL [`surface_boundary (e:(real^3->bool)->bool)`; `b:real^3->bool`]
                  IN_COMPONENTS_CONNECTED) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((b:real^3->bool) INTER J = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!b:real^3->bool. b IN components (surface_boundary L) /\ ~(b INTER J = {})
                                 ==> b SUBSET J` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`e:(real^3->bool)->bool`; `L:(real^3->bool)->bool`; `J:real^3->bool`]
                MOI_S6G_SURF_GLUE_BODY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN SET_TAC[];
    MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `connected (UNIONS (e:(real^3->bool)->bool))` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3CF_CELL_CONNECTED THEN
      MAP_EVERY EXISTS_TAC [`2`; `J:real^3->bool`] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `UNIONS e INTER UNIONS L = (J:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[UNIONS_INSERT] THEN SET_TAC[];
    ASM_SIMP_TAC[CARD_CLAUSES; GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Part 7: two or more essential polygons.  Let e be the surface c0         *)
(* with the caps glued on, in the torus T, with boundary the union of the  *)
(* family gg of essential boundary polygons.  The interior of e is a        *)
(* component of T minus the polygons (connected, open in T, and closed in  *)
(* the complement of the polygons); by 28.6 its closure, the whole of e, is *)
(* a PL annulus, so chi e = 0, and SURFACE_PLANAR (chi + b <= 2) leaves      *)
(* exactly two polygons.                                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CF_TWO_ESS = prove
 (mk_imp(list_mk_conj [`MOISE_286_STATEMENT`; moi_n3 MOI_FND_EULER_VALUES;
                       moi_n3 MOI_FND_SURFACE_PLANAR],
  `!(s:real^3->bool) (gg:(real^3->bool)->bool) (e:(real^3->bool)->bool).
     pl_solid_torus s /\ (!y. y IN frontier s ==> moi_s28_locally_r2 (frontier s) y) /\
     FINITE gg /\ 2 <= CARD gg /\ pairwise DISJOINT gg /\
     (!j. j IN gg ==> pl_sphere 1 j /\ j SUBSET frontier s /\
                      closed j /\ connected j /\ ~(j = {})) /\
     (!j d. j IN gg /\ d SUBSET frontier s ==> ~pl_cell_with_boundary 2 d j) /\
     FINITE e /\ combinatorial_manifold_with_boundary 2 e /\ connected (UNIONS e) /\
     UNIONS e SUBSET frontier s /\ surface_boundary e = UNIONS gg
     ==> gg HAS_SIZE 2 /\ complex_euler e = &0`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "286") (CONJUNCTS_THEN2 (LABEL_TAC "ev")
    (LABEL_TAC "sp"))) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gj")
    (CONJUNCTS_THEN2 (LABEL_TAC "nd") STRIP_ASSUME_TAC))))))) THEN
  USE_THEN "286" (MP_TAC o SPECL [`s:real^3->bool`; `gg:(real^3->bool)->bool`] o
    REWRITE_RULE[MOISE_286_STATEMENT]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `j:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "gj" (MP_TAC o C MATCH_MP (ASSUME `(j:real^3->bool) IN gg`)) THEN
    SIMP_TAC[];
    DISCH_THEN(LABEL_TAC "ann")] THEN
  MP_TAC(ISPEC `e:(real^3->bool)->bool` MOI_S3CF_SURF_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `e:(real^3->bool)->bool` INT_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`frontier s:real^3->bool`; `e:(real^3->bool)->bool`]
                MOI_S3CF_SURF_INTERIOR_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `e:(real^3->bool)->bool` MOI_S3CF_SURF_CLOSURE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `e:(real^3->bool)->bool` MOI_S3CF_SURF_BOUNDARY_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* e is not empty, nor is its interior *)
  SUBGOAL_THEN `~(gg:(real^3->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `2 <= CARD (gg:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(UNIONS (e:(real^3->bool)->bool) = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `~(gg:(real^3->bool)->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `j:real^3->bool`) THEN
    USE_THEN "gj" (MP_TAC o C MATCH_MP (ASSUME `(j:real^3->bool) IN gg`)) THEN
    STRIP_TAC THEN
    UNDISCH_TAC `UNIONS gg SUBSET UNIONS (e:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `(j:real^3->bool) IN gg` THEN UNDISCH_TAC `~(j:real^3->bool = {})` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^3. x IN UNIONS e DIFF UNIONS gg` (X_CHOOSE_TAC `x:real^3`) THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `UNIONS e SUBSET closure (UNIONS e DIFF UNIONS gg:real^3->bool)` THEN
    ASM_REWRITE_TAC[CLOSURE_EMPTY; SUBSET_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN connected_component (frontier s DIFF UNIONS gg) x`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
    UNDISCH_TAC `(x:real^3) IN UNIONS e DIFF UNIONS gg` THEN
    UNDISCH_TAC `UNIONS (e:(real^3->bool)->bool) SUBSET frontier s` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the component of x is the interior of e *)
  SUBGOAL_THEN `open_in (subtopology euclidean (frontier s))
                        (frontier s DIFF UNIONS (e:(real^3->bool)->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `(:real^3) DIFF UNIONS e` THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_component (frontier s DIFF UNIONS gg) (x:real^3) =
                UNIONS e DIFF UNIONS gg` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`frontier s:real^3->bool`;
                     `connected_component (frontier s DIFF UNIONS gg) (x:real^3)`;
                     `UNIONS e DIFF UNIONS gg:real^3->bool`;
                     `frontier s DIFF UNIONS (e:(real^3->bool)->bool)`]
                    MOI_S3CF_CONNECTED_OPEN_SIDE) THEN
      MP_TAC(ISPECL [`frontier s DIFF UNIONS gg:real^3->bool`; `x:real^3`]
                    CONNECTED_COMPONENT_SUBSET) THEN
      REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT] THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [UNDISCH_TAC `connected_component (frontier s DIFF UNIONS gg) (x:real^3) SUBSET
                       frontier s DIFF UNIONS gg` THEN SET_TAC[];
          UNDISCH_TAC `connected_component (frontier s DIFF UNIONS gg) (x:real^3) SUBSET
                       frontier s DIFF UNIONS gg` THEN SET_TAC[];
          SET_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `connected_component (frontier s DIFF UNIONS gg) (x:real^3) SUBSET
                   frontier s DIFF UNIONS e` THEN
      UNDISCH_TAC `(x:real^3) IN connected_component (frontier s DIFF UNIONS gg) x` THEN
      UNDISCH_TAC `(x:real^3) IN UNIONS e DIFF UNIONS gg` THEN SET_TAC[];
      MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `UNIONS (e:(real^3->bool)->bool) SUBSET frontier s` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure (UNIONS e DIFF UNIONS gg:real^3->bool) = UNIONS e` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  (* 28.6: e is an annulus *)
  USE_THEN "ann" (MP_TAC o SPEC `x:real^3`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN UNIONS e DIFF UNIONS gg` THEN
    UNDISCH_TAC `UNIONS (e:(real^3->bool)->bool) SUBSET frontier s` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j0:real^3->bool` (X_CHOOSE_THEN `j1:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `complex_euler (e:(real^3->bool)->bool) = &0` ASSUME_TAC THENL
   [USE_THEN "ev" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `simplicial_complex (e:(real^3->bool)->bool)`)
            (ASSUME `!s:real^3->bool. s IN e ==> aff_dim s <= &2`))) THEN
    DISCH_THEN(MATCH_MP_TAC o el 4 o CONJUNCTS) THEN
    REWRITE_TAC[pl_annulus] THEN
    UNDISCH_TAC `pl_annulus_with_ends (UNIONS e) (j0:real^3->bool) j1` THEN
    REWRITE_TAC[pl_annulus_with_ends] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* SURFACE_PLANAR: chi + b <= 2 *)
  USE_THEN "sp" (MP_TAC o C MATCH_MP
    (end_itlist CONJ [ASSUME `FINITE (e:(real^3->bool)->bool)`;
                      ASSUME `combinatorial_manifold_with_boundary 2 (e:(real^3->bool)->bool)`;
                      ASSUME `connected (UNIONS (e:(real^3->bool)->bool))`;
                      ASSUME `~(UNIONS (e:(real^3->bool)->bool) = {})`])) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  MP_TAC(ISPEC `gg:(real^3->bool)->bool` MOI_S3CF_COMPONENTS_UNIONS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "gj" (MP_TAC o C MATCH_MP (ASSUME `(j:real^3->bool) IN gg`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `2 <= CARD (gg:(real^3->bool)->bool)` THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part 8: one essential polygon is impossible.  If the capped surface      *)
(* e in the torus T had boundary a single essential polygon J1, take a      *)
(* parallel copy J1' of J1 (a bicollar of J1 in T, MOI_FND_BICOLLAR_CURVE_2 *)
(* on a triangulation of T, orientable by 26.8).  J1' is essential too (a  *)
(* disk bounded by J1' misses J1 and meets the strip between them only in   *)
(* J1', so disk plus strip is a disk bounded by J1, SURF_GLUE and           *)
(* SURFACE_PLANAR with k = 0).  By 28.6 every component of T minus J1 and  *)
(* J1' has J1' in its closure, so T minus J1 is connected; but the interior *)
(* of e and the complement of e split it.                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CF_TORUS_COMPLEX = prove
 (`MOISE_268_STATEMENT
   ==> !s:real^3->bool.
         pl_solid_torus s /\
         (?(f:real^(2,2)finite_sum->real^3) h.
            pl_homeomorphism (pl_torus_model,frontier s) (f,h))
         ==> ?c. FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
                 orientable_surface_complex c /\
                 UNIONS c = frontier s /\ surface_boundary c = {}`,
  DISCH_THEN(LABEL_TAC "268") THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S3CF_TORUS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S3I2_SOLID_TORUS_REGULAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `f:real^(2,2)finite_sum->real^3`
    (X_CHOOSE_TAC `h:real^3->real^(2,2)finite_sum`) o check (is_exists o concl)) THEN
  MP_TAC(ISPECL [`frontier s:real^3->bool`; `f:real^(2,2)finite_sum->real^3`;
                 `h:real^3->real^(2,2)finite_sum`] MOI_S8TO_TRIANG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTERIOR_FRONTIER_EMPTY THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `FINITE (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPEC `t:(real^3->bool)->bool` SURF_LOCAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `surface_boundary (t:(real^3->bool)->bool) = {}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `t:(real^3->bool)->bool` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  USE_THEN "268" (MATCH_MP_TAC o REWRITE_RULE[MOISE_268_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Levels of a bicollar of a compact connected curve.                       *)

let MOI_S3CF_BICOLLAR_FACTS = prove
 (`!(m:real^3->bool) w (p:real^(3,1)finite_sum->real^3) q.
     moi_s26_bicollar m w p q /\ compact m /\ connected m /\ ~(m = {})
     ==> moi_s26_level m p (&0) = m /\
         (!a b. --(&1) <= a /\ b <= &1
                ==> IMAGE p (m PCROSS {x:real^1 | a <= drop x /\ drop x <= b}) SUBSET w) /\
         (!t. --(&1) <= t /\ t <= &1
              ==> moi_s26_level m p t SUBSET w /\
                  compact (moi_s26_level m p t) /\ connected (moi_s26_level m p t) /\
                  ~(moi_s26_level m p t = {}) /\
                  (~(t = &0) ==> DISJOINT m (moi_s26_level m p t)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s26_bicollar; pl_homeomorphism] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  REWRITE_TAC[moi_s26_level] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIFT_NUM] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_SING] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^1` STRIP_ASSUME_TAC)) THEN
      ASM_SIMP_TAC[];
      DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`y:real^3`; `vec 0:real^1`] THEN
      ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (p:real^(3,1)finite_sum->real^3)
                       (m PCROSS interval[--vec 1:real^1,vec 1]) = w` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
                IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(m:real^3->bool) PCROSS {lift t} SUBSET m PCROSS interval[--vec 1:real^1,vec 1]`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (p:real^(3,1)finite_sum->real^3)
                       (m PCROSS interval[--vec 1:real^1,vec 1]) = w` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(m:real^3->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_SING]];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(m:real^3->bool) PCROSS interval[--vec 1:real^1,vec 1]` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[CONNECTED_PCROSS; CONNECTED_SING]];
    REWRITE_TAC[IMAGE_EQ_EMPTY; PCROSS_EQ_EMPTY; NOT_INSERT_EMPTY] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[DISJOINT] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN X_GEN_TAC `y:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^(3,1)finite_sum`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `z IN (m:real^3->bool) PCROSS interval[--vec 1:real^1,vec 1] /\
                pastecart (y:real^3) (vec 0:real^1) IN m PCROSS interval[--vec 1:real^1,vec 1]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `z IN (m:real^3->bool) PCROSS {lift t}` THEN
      UNDISCH_TAC `(m:real^3->bool) PCROSS {lift t} SUBSET m PCROSS interval[--vec 1:real^1,vec 1]` THEN
      SET_TAC[];
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3->real^(3,1)finite_sum) y = z` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) = p (z:real^(3,1)finite_sum)` THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3->real^(3,1)finite_sum) y = pastecart y (vec 0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(p:real^(3,1)finite_sum->real^3) (pastecart y (vec 0)) = y` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `z = pastecart (y:real^3) (vec 0:real^1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `z IN (m:real^3->bool) PCROSS {lift t}` THEN
  SUBST1_TAC(ASSUME `z = pastecart (y:real^3) (vec 0:real^1)`) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING; GSYM LIFT_NUM; LIFT_EQ] THEN
  ASM_MESON_TAC[]);;

(* The two ends of a PL annulus that are compact, connected and disjoint are *)
(* polygons.                                                                  *)

let MOI_S3CF_ANNULUS_END_SPHERES = prove
 (`!(a:real^3->bool) j0 j1.
     pl_annulus_with_ends a j0 j1 /\
     compact j0 /\ connected j0 /\ ~(j0 = {}) /\
     compact j1 /\ connected j1 /\ ~(j1 = {}) /\ DISJOINT j0 j1
     ==> pl_sphere 1 j0 /\ pl_sphere 1 j1 /\ components (j0 UNION j1) = {j0, j1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `components ((j0:real^3->bool) UNION j1) = {j0, j1}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `{j0:real^3->bool, j1}` MOI_S3CF_COMPONENTS_UNIONS) THEN
    REWRITE_TAC[UNIONS_2] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
                pairwise; IN_INSERT] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM_MESON_TAC[DISJOINT_SYM; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `d:(real^3->bool)->bool` STRIP_ASSUME_TAC o
    MATCH_MP ANNULUS_COMPLEX) THEN
  MP_TAC(ISPEC `d:(real^3->bool)->bool` MOI_FSB_BD_CIRCLES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[IN_INSERT] THEN MESON_TAC[]);;

(* A parallel copy of a polygon in the torus.                               *)

let MOI_S3CF_PARALLEL_COPY = prove
 (mk_imp(list_mk_conj [`MOISE_268_STATEMENT`; moi_n3 MOI_FND_BICOLLAR_CURVE_2],
  `!(s:real^3->bool) J1.
     pl_solid_torus s /\
     (?(f:real^(2,2)finite_sum->real^3) h.
        pl_homeomorphism (pl_torus_model,frontier s) (f,h)) /\
     pl_sphere 1 J1 /\ J1 SUBSET frontier s /\ compact J1 /\ connected J1 /\ ~(J1 = {})
     ==> ?S J1'. pl_annulus_with_ends S J1' J1 /\ S SUBSET frontier s /\
                 J1' SUBSET frontier s /\ compact J1' /\ connected J1' /\ ~(J1' = {}) /\
                 DISJOINT J1 J1' /\ pl_sphere 1 J1'`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "268") (LABEL_TAC "bic")) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `s:real^3->bool` (MP MOI_S3CF_TORUS_COMPLEX (ASSUME `MOISE_268_STATEMENT`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `J1:real^3->bool` POLYGON_COMPLEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "bic" (MP_TAC o SPECL [`c:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                                  `frontier s:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[DIFF_EMPTY; OPEN_IN_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` (X_CHOOSE_THEN `p:real^(3,1)finite_sum->real^3`
    (X_CHOOSE_THEN `q:real^3->real^(3,1)finite_sum` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `moi_s26_bicollar (J1:real^3->bool) w p q` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s26_bicollar]; ALL_TAC] THEN
  MP_TAC(ISPECL [`J1:real^3->bool`; `w:real^3->bool`; `p:real^(3,1)finite_sum->real^3`;
                 `q:real^3->real^(3,1)finite_sum`] MOI_S3CF_BICOLLAR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "strip")
    (LABEL_TAC "lev"))) THEN
  MP_TAC(ISPECL [`J1:real^3->bool`; `w:real^3->bool`; `p:real^(3,1)finite_sum->real^3`;
                 `q:real^3->real^(3,1)finite_sum`; `-- &1 / &2`; `&0`] PRODUCT_ANNULUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "lev" (MP_TAC o SPEC `-- &1 / &2`) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `~(-- &1 / &2 = &0)`] THEN STRIP_TAC THEN
  USE_THEN "strip" (MP_TAC o SPECL [`-- &1 / &2`; `&0`]) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (p:real^(3,1)finite_sum->real^3)
           (J1 PCROSS {x:real^1 | -- &1 / &2 <= drop x /\ drop x <= &0})`;
    `moi_s26_level J1 (p:real^(3,1)finite_sum->real^3) (-- &1 / &2)`; `J1:real^3->bool`]
   MOI_S3CF_ANNULUS_END_SPHERES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (p:real^(3,1)finite_sum->real^3)
           (J1 PCROSS {x:real^1 | -- &1 / &2 <= drop x /\ drop x <= &0})`;
    `moi_s26_level J1 (p:real^(3,1)finite_sum->real^3) (-- &1 / &2)`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(w:real^3->bool) SUBSET frontier s` THEN
  UNDISCH_TAC `moi_s26_level J1 (p:real^(3,1)finite_sum->real^3) (-- &1 / &2) SUBSET w` THEN
  UNDISCH_TAC `IMAGE (p:real^(3,1)finite_sum->real^3)
                 (J1 PCROSS {x:real^1 | -- &1 / &2 <= drop x /\ drop x <= &0}) SUBSET w` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 9: the copy is essential, the torus minus J1 is connected          *)
(* (28.6 on J1 and its copy), and one essential boundary polygon is        *)
(* impossible.                                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CF_COPY_ESSENTIAL = prove
 (mk_imp(list_mk_conj [moi_n3 MOI_FND_EULER_VALUES; moi_n3 MOI_FND_SURFACE_PLANAR],
  `!(x:real^3->bool) S J1 J1'.
     (!y. y IN x ==> moi_s28_locally_r2 x y) /\
     pl_annulus_with_ends S J1' J1 /\ S SUBSET x /\
     pl_sphere 1 J1 /\ compact J1 /\ connected J1 /\ ~(J1 = {}) /\
     compact J1' /\ connected J1' /\ ~(J1' = {}) /\ DISJOINT J1 J1' /\
     ~(?d. d SUBSET x /\ pl_cell_with_boundary 2 d J1)
     ==> ~(?d. d SUBSET x /\ pl_cell_with_boundary 2 d J1')`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ev") (LABEL_TAC "sp")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `D:real^3->bool`; `J1':real^3->bool`]
                MOI_S3CF_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `J1':real^3->bool`; `J1:real^3->bool`]
                MOI_S3CF_ANNULUS_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(J1:real^3->bool) SUBSET x` ASSUME_TAC THENL
   [UNDISCH_TAC `(J1:real^3->bool) SUBSET S` THEN UNDISCH_TAC `(S:real^3->bool) SUBSET x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* J1 lies outside D *)
  SUBGOAL_THEN `DISJOINT (J1:real^3->bool) D` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x:real^3->bool`; `J1:real^3->bool`; `D DIFF (J1':real^3->bool)`;
                   `(x:real^3->bool) DIFF D`] MOI_S3CF_CONNECTED_OPEN_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (J1:real^3->bool) J1'` THEN
      UNDISCH_TAC `(J1:real^3->bool) SUBSET x` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
     [MP_TAC(ISPECL [`D:real^3->bool`; `J1':real^3->bool`; `J1:real^3->bool`] DISK_POLYGON) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(J1:real^3->bool) SUBSET D DIFF J1'` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[moi_s28_bounds_disk] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real^3->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~(?d. d SUBSET (x:real^3->bool) /\ pl_cell_with_boundary 2 d J1)` THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      EXISTS_TAC `d:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(d:real^3->bool) SUBSET D` THEN UNDISCH_TAC `(D:real^3->bool) SUBSET x` THEN
      SET_TAC[];
      UNDISCH_TAC `(J1:real^3->bool) SUBSET x DIFF D` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the strip meets D only in J1' *)
  SUBGOAL_THEN `(S:real^3->bool) INTER D = J1'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^3->bool`; `J1':real^3->bool`; `J1:real^3->bool`]
                  MOI_S3CA_ANNULUS_MINUS_END) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^3->bool`; `S DIFF (J1':real^3->bool)`; `D DIFF (J1':real^3->bool)`;
                   `(x:real^3->bool) DIFF D`] MOI_S3CF_CONNECTED_OPEN_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(S:real^3->bool) SUBSET x` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
     [UNDISCH_TAC `(S:real^3->bool) DIFF J1' SUBSET D DIFF J1'` THEN
      UNDISCH_TAC `(J1:real^3->bool) SUBSET S` THEN
      UNDISCH_TAC `DISJOINT (J1:real^3->bool) J1'` THEN
      UNDISCH_TAC `DISJOINT (J1:real^3->bool) D` THEN
      UNDISCH_TAC `~(J1:real^3->bool = {})` THEN SET_TAC[];
      UNDISCH_TAC `(S:real^3->bool) DIFF J1' SUBSET x DIFF D` THEN
      UNDISCH_TAC `(J1':real^3->bool) SUBSET S` THEN
      UNDISCH_TAC `(J1':real^3->bool) SUBSET D` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* complexes for the disk and the strip, glued along J1' *)
  MP_TAC(ISPECL [`D:real^3->bool`; `J1':real^3->bool`] MOI_S3CF_CELL_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `J1':real^3->bool`; `J1:real^3->bool`] ANNULUS_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `complex_euler (L:(real^3->bool)->bool) = &1` ASSUME_TAC THENL
   [USE_THEN "ev" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `simplicial_complex (L:(real^3->bool)->bool)`)
            (ASSUME `!s:real^3->bool. s IN L ==> aff_dim s <= &2`))) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3CA_CELL_BALL THEN
    EXISTS_TAC `J1':real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`J1':real^3->bool`; `J1:real^3->bool`] (ISPEC `S:real^3->bool`
                MOI_S3CF_ANNULUS_END_SPHERES)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `!b:real^3->bool. b IN components (surface_boundary L) /\ ~(b INTER J1' = {})
                                 ==> b SUBSET J1'` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!b:real^3->bool. b IN components (surface_boundary A) /\ ~(b INTER J1' = {})
                                 ==> b SUBSET J1'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    UNDISCH_TAC `~((b:real^3->bool) INTER J1' = {})` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (J1:real^3->bool) J1'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS L INTER UNIONS A = (J1':real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `A:(real^3->bool)->bool`; `J1':real^3->bool`]
                MOI_S6G_SURF_GLUE_BODY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL; SUBSET_UNION]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `surface_boundary (g:(real^3->bool)->bool) = J1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT (J1:real^3->bool) J1'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (UNIONS (g:(real^3->bool)->bool)) /\ ~(UNIONS g = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(J1':real^3->bool) SUBSET D` THEN UNDISCH_TAC `~(J1':real^3->bool = {})` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "sp" (MP_TAC o C MATCH_MP
    (end_itlist CONJ [ASSUME `FINITE (g:(real^3->bool)->bool)`;
                      ASSUME `combinatorial_manifold_with_boundary 2 (g:(real^3->bool)->bool)`;
                      ASSUME `connected (UNIONS (g:(real^3->bool)->bool))`;
                      ASSUME `~(UNIONS (g:(real^3->bool)->bool) = {})`])) THEN
  DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ASSUME `surface_boundary (g:(real^3->bool)->bool) = J1`] THEN
    SUBGOAL_THEN `components (J1:real^3->bool) = {J1}` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[COMPONENTS_EQ_SING]; ALL_TAC] THEN
    REWRITE_TAC[CARD_SING] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `h:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `~(?d. d SUBSET (x:real^3->bool) /\ pl_cell_with_boundary 2 d J1)` THEN
  REWRITE_TAC[] THEN EXISTS_TAC `UNIONS (g:(real^3->bool)->bool)` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(D:real^3->bool) SUBSET x` THEN
    UNDISCH_TAC `(S:real^3->bool) SUBSET x` THEN SET_TAC[];
    UNDISCH_TAC `IMAGE (f:real^2->real^3) (frontier (holed_disk_model 0)) =
                 surface_boundary (g:(real^3->bool)->bool)` THEN
    REWRITE_TAC[ASSUME `surface_boundary (g:(real^3->bool)->bool) = J1`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SQUARE_CELL THEN EXISTS_TAC `h:real^3->real^2` THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(* 28.6 on J1 and an essential copy disjoint from it: T minus J1 is         *)
(* connected (every component of T minus both has J1' in its closure).     *)

let MOI_S3CF_NONSEP = prove
 (`MOISE_286_STATEMENT
   ==> !(s:real^3->bool) J1 J1'.
         pl_solid_torus s /\
         pl_sphere 1 J1 /\ J1 SUBSET frontier s /\
         pl_sphere 1 J1' /\ J1' SUBSET frontier s /\ connected J1' /\ ~(J1' = {}) /\
         DISJOINT J1 J1' /\
         ~(?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d J1) /\
         ~(?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d J1')
         ==> connected (frontier s DIFF J1)`,
  DISCH_THEN(LABEL_TAC "286") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(J1:real^3->bool = J1')` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `DISJOINT (J1':real^3->bool) J1'` THEN
    UNDISCH_TAC `~(J1':real^3->bool = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "286" (MP_TAC o SPECL [`s:real^3->bool`; `{J1:real^3->bool, J1'}`] o
    REWRITE_RULE[MOISE_286_STATEMENT]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_SING; NOT_IN_EMPTY] THEN
      ARITH_TAC;
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
      REWRITE_TAC[pairwise; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[DISJOINT_SYM];
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]];
    DISCH_THEN(LABEL_TAC "ann" o REWRITE_RULE[UNIONS_2])] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN frontier s DIFF (J1 UNION J1')
               ==> J1' SUBSET closure (connected_component (frontier s DIFF (J1 UNION J1')) y)`
  (LABEL_TAC "cl") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "ann" (MP_TAC o C MATCH_MP
      (ASSUME `(y:real^3) IN frontier s DIFF (J1 UNION J1')`)) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `j0:real^3->bool` (X_CHOOSE_THEN `j1:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S3CF_ANNULUS_ENDS) THEN STRIP_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frontier s DIFF (J1:real^3->bool) =
    UNIONS (J1' INSERT
            {connected_component (frontier s DIFF (J1 UNION J1')) y UNION J1' | y |
             y IN frontier s DIFF (J1 UNION J1')})` SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[UNIONS_INSERT; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_TAC THEN ASM_CASES_TAC `(z:real^3) IN J1'` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `z:real^3` THEN
      SUBGOAL_THEN `(z:real^3) IN frontier s DIFF (J1 UNION J1')` ASSUME_TAC THENL
       [UNDISCH_TAC `(z:real^3) IN frontier s DIFF J1` THEN
        UNDISCH_TAC `~((z:real^3) IN J1')` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM_REWRITE_TAC[];
      STRIP_TAC THENL
       [UNDISCH_TAC `(z:real^3) IN J1'` THEN
        UNDISCH_TAC `(J1':real^3->bool) SUBSET frontier s` THEN
        UNDISCH_TAC `DISJOINT (J1:real^3->bool) J1'` THEN SET_TAC[];
        MP_TAC(ISPECL [`frontier s DIFF (J1 UNION J1'):real^3->bool`; `y:real^3`]
                      CONNECTED_COMPONENT_SUBSET) THEN
        UNDISCH_TAC `(z:real^3) IN connected_component (frontier s DIFF (J1 UNION J1')) y` THEN
        SET_TAC[];
        UNDISCH_TAC `(z:real^3) IN J1'` THEN
        UNDISCH_TAC `(J1':real^3->bool) SUBSET frontier s` THEN
        UNDISCH_TAC `DISJOINT (J1:real^3->bool) J1'` THEN SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNIONS THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
    EXISTS_TAC `connected_component (frontier s DIFF (J1 UNION J1')) (y:real^3)` THEN
    REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT; SUBSET_UNION] THEN
    MP_TAC(ISPEC `connected_component (frontier s DIFF (J1 UNION J1')) (y:real^3)`
                 CLOSURE_SUBSET) THEN
    USE_THEN "cl" (MP_TAC o C MATCH_MP
      (ASSUME `(y:real^3) IN frontier s DIFF (J1 UNION J1')`)) THEN
    SET_TAC[];
    SUBGOAL_THEN
     `(J1':real^3->bool) SUBSET
      INTERS (J1' INSERT
              {connected_component (frontier s DIFF (J1 UNION J1')) y UNION J1' | y |
               y IN frontier s DIFF (J1 UNION J1')})` MP_TAC THENL
     [REWRITE_TAC[SUBSET_INTERS; FORALL_IN_INSERT; FORALL_IN_GSPEC] THEN SET_TAC[];
      UNDISCH_TAC `~(J1':real^3->bool = {})` THEN SET_TAC[]]]);;

(* One essential boundary polygon is impossible.                            *)

let MOI_S3CF_ONE_ESS = prove
 (mk_imp(list_mk_conj [`MOISE_286_STATEMENT`; `MOISE_268_STATEMENT`;
                       moi_n3 MOI_FND_BICOLLAR_CURVE_2;
                       moi_n3 MOI_FND_EULER_VALUES; moi_n3 MOI_FND_SURFACE_PLANAR],
  `!(s:real^3->bool) J1 (e:(real^3->bool)->bool).
     pl_solid_torus s /\
     (?(f:real^(2,2)finite_sum->real^3) h.
        pl_homeomorphism (pl_torus_model,frontier s) (f,h)) /\
     pl_sphere 1 J1 /\ J1 SUBSET frontier s /\ compact J1 /\ connected J1 /\ ~(J1 = {}) /\
     ~(?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d J1) /\
     FINITE e /\ combinatorial_manifold_with_boundary 2 e /\ UNIONS e SUBSET frontier s /\
     surface_boundary e = J1
     ==> F`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "286") (CONJUNCTS_THEN2 (LABEL_TAC "268")
    (CONJUNCTS_THEN2 (LABEL_TAC "bic") (CONJUNCTS_THEN2 (LABEL_TAC "ev") (LABEL_TAC "sp"))))) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S3CF_TORUS_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `J1:real^3->bool`]
    (MP MOI_S3CF_PARALLEL_COPY (CONJ (ASSUME `MOISE_268_STATEMENT`)
                                     (ASSUME (moi_n3 MOI_FND_BICOLLAR_CURVE_2))))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `J1':real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`frontier s:real^3->bool`; `S:real^3->bool`; `J1:real^3->bool`;
                 `J1':real^3->bool`]
    (MP MOI_S3CF_COPY_ESSENTIAL (CONJ (ASSUME (moi_n3 MOI_FND_EULER_VALUES))
                                      (ASSUME (moi_n3 MOI_FND_SURFACE_PLANAR))))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `J1:real^3->bool`; `J1':real^3->bool`]
    (MP MOI_S3CF_NONSEP (ASSUME `MOISE_286_STATEMENT`))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPEC `e:(real^3->bool)->bool` MOI_S3CF_SURF_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`frontier s:real^3->bool`; `e:(real^3->bool)->bool`]
                MOI_S3CF_SURF_INTERIOR_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `e:(real^3->bool)->bool` MOI_S3CF_SURF_CLOSURE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `e:(real^3->bool)->bool` MOI_S3CF_SURF_BOUNDARY_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(UNIONS e DIFF J1:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `UNIONS e SUBSET closure (UNIONS e DIFF J1:real^3->bool)` THEN
    ASM_REWRITE_TAC[CLOSURE_EMPTY; SUBSET_EMPTY] THEN
    UNDISCH_TAC `(J1:real^3->bool) SUBSET UNIONS e` THEN
    UNDISCH_TAC `~(J1:real^3->bool = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(frontier s DIFF UNIONS (e:(real^3->bool)->bool) = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `?y:real^3. y IN J1` (X_CHOOSE_TAC `y:real^3`) THENL
     [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN frontier s` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN J1` THEN UNDISCH_TAC `(J1:real^3->bool) SUBSET frontier s` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`frontier s:real^3->bool`; `e:(real^3->bool)->bool`; `y:real^3`;
                   `frontier s:real^3->bool`] MOI_S3CF_SURF_BD_NOT_INTERIOR) THEN
    ASM_REWRITE_TAC[OPEN_IN_REFL] THEN
    UNDISCH_TAC `frontier s DIFF UNIONS (e:(real^3->bool)->bool) = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (frontier s))
                        (frontier s DIFF UNIONS (e:(real^3->bool)->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `(:real^3) DIFF UNIONS e` THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier s:real^3->bool`; `frontier s DIFF (J1:real^3->bool)`;
                 `UNIONS e DIFF (J1:real^3->bool)`;
                 `frontier s DIFF UNIONS (e:(real^3->bool)->bool)`]
                MOI_S3CF_CONNECTED_OPEN_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(J1:real^3->bool) SUBSET UNIONS e` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [UNDISCH_TAC `~(frontier s DIFF UNIONS (e:(real^3->bool)->bool) = {})` THEN
    UNDISCH_TAC `frontier s DIFF J1 SUBSET UNIONS e DIFF (J1:real^3->bool)` THEN
    UNDISCH_TAC `(J1:real^3->bool) SUBSET UNIONS e` THEN SET_TAC[];
    UNDISCH_TAC `~(UNIONS e DIFF J1:real^3->bool = {})` THEN
    UNDISCH_TAC `frontier s DIFF J1 SUBSET frontier s DIFF UNIONS (e:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `UNIONS (e:(real^3->bool)->bool) SUBSET frontier s` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 10: the torus count (28.6 on the essential polygons, a parallel     *)
(* copy for one, and the Euler count after capping).  For a compact         *)
(* connected surface c0 in the frontier T of a PL solid torus the boundary  *)
(* polygons bounding no 2-cell of T are 0 or 2 in number, and with 2 of     *)
(* them chi plus the number of the others is 0.  If there is an essential   *)
(* polygon J1, no inessential one bounds a cap containing c0 (else J1 would *)
(* bound a disk in the cap, DISK_POLYGON); the caps meet c0 only in their   *)
(* rims and are disjoint (Part 5); gluing them on (GLUE_CAPS) gives e with  *)
(* boundary the union of the essential polygons and                         *)
(* chi e = chi c0 + (number of caps); then TWO_ESS or ONE_ESS.              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CF_TORUS_COUNT = prove
 (mk_imp(list_mk_conj [`MOISE_286_STATEMENT`; `MOISE_268_STATEMENT`;
                       moi_n3 MOI_FND_BICOLLAR_CURVE_2;
                       moi_n3 MOI_FND_EULER_VALUES; moi_n3 MOI_FND_SURFACE_PLANAR],
  `!(s:real^3->bool) (cc0:(real^3->bool)->bool).
     pl_solid_torus s /\
     (?(f:real^(2,2)finite_sum->real^3) h.
        pl_homeomorphism (pl_torus_model,frontier s) (f,h)) /\
     FINITE cc0 /\ combinatorial_manifold_with_boundary 2 cc0 /\
     connected (UNIONS cc0) /\ UNIONS cc0 SUBSET frontier s
     ==> {jj | jj IN components (surface_boundary cc0) /\
               ~(?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d jj)} = {} \/
         ({jj | jj IN components (surface_boundary cc0) /\
                ~(?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d jj)} HAS_SIZE 2 /\
          complex_euler cc0 +
          &(CARD {jj | jj IN components (surface_boundary cc0) /\
                       (?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d jj)}) = &0)`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "286") (CONJUNCTS_THEN2 (LABEL_TAC "268")
    (CONJUNCTS_THEN2 (LABEL_TAC "bic") (CONJUNCTS_THEN2 (LABEL_TAC "ev")
    (LABEL_TAC "sp"))))) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S3CF_TORUS_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `cc0:(real^3->bool)->bool` MOI_FSB_BD_CIRCLES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sph")) THEN
  MP_TAC(ISPEC `cc0:(real^3->bool)->bool` MOI_S3CF_SURF_BOUNDARY_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `cc0:(real^3->bool)->bool` MOI_S3CF_SURF_BOUNDARY_SUBSET) THEN DISCH_TAC THEN
  (* the boundary polygons *)
  SUBGOAL_THEN
   `!J:real^3->bool. J IN components (surface_boundary cc0)
       ==> pl_sphere 1 J /\ J SUBSET surface_boundary cc0 /\ J SUBSET UNIONS cc0 /\
           J SUBSET frontier s /\ closed J /\ compact J /\ connected J /\ ~(J = {})`
  (LABEL_TAC "cj") THENL
   [X_GEN_TAC `J:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "sph" (MP_TAC o C MATCH_MP
      (ASSUME `(J:real^3->bool) IN components (surface_boundary cc0)`)) THEN
    MP_TAC(ISPECL [`surface_boundary (cc0:(real^3->bool)->bool)`; `J:real^3->bool`]
                  IN_COMPONENTS_SUBSET) THEN
    MP_TAC(ISPECL [`surface_boundary (cc0:(real^3->bool)->bool)`; `J:real^3->bool`]
                  IN_COMPONENTS_CONNECTED) THEN
    MP_TAC(ISPECL [`surface_boundary (cc0:(real^3->bool)->bool)`; `J:real^3->bool`]
                  IN_COMPONENTS_NONEMPTY) THEN
    MP_TAC(ISPECL [`surface_boundary (cc0:(real^3->bool)->bool)`; `J:real^3->bool`]
                  CLOSED_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(J:real^3->bool) SUBSET UNIONS cc0 /\ J SUBSET frontier s`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(J:real^3->bool) SUBSET surface_boundary cc0` THEN
      UNDISCH_TAC `surface_boundary cc0 SUBSET UNIONS (cc0:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `UNIONS (cc0:(real^3->bool)->bool) SUBSET frontier s` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `frontier s:real^3->bool` THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  ABBREV_TAC `E0 = {jj:real^3->bool | jj IN components (surface_boundary cc0) /\
                     ~(?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d jj)}` THEN
  ABBREV_TAC `I0 = {jj:real^3->bool | jj IN components (surface_boundary cc0) /\
                     (?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d jj)}` THEN
  SUBGOAL_THEN `!J:real^3->bool. J IN E0 <=> J IN components (surface_boundary cc0) /\
                  ~(?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d J)`
  (LABEL_TAC "inE") THENL
   [EXPAND_TAC "E0" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!J:real^3->bool. J IN I0 <=> J IN components (surface_boundary cc0) /\
                  (?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d J)`
  (LABEL_TAC "inI") THENL
   [EXPAND_TAC "I0" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `E0 SUBSET components (surface_boundary (cc0:(real^3->bool)->bool)) /\
                I0 SUBSET components (surface_boundary cc0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN USE_THEN "inE" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "inI" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (E0:(real^3->bool)->bool) /\ FINITE (I0:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `components (surface_boundary (cc0:(real^3->bool)->bool))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `E0:(real^3->bool)->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?J1:real^3->bool. J1 IN E0` (X_CHOOSE_TAC `J1:real^3->bool`) THENL
   [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  USE_THEN "inE" (fun th -> MP_TAC(EQ_MP (SPEC `J1:real^3->bool` th)
    (ASSUME `(J1:real^3->bool) IN E0`))) THEN STRIP_TAC THEN
  USE_THEN "cj" (MP_TAC o C MATCH_MP
    (ASSUME `(J1:real^3->bool) IN components (surface_boundary cc0)`)) THEN STRIP_TAC THEN
  (* the caps *)
  SUBGOAL_THEN `?cap:(real^3->bool)->(real^3->bool).
                  !J. J IN I0 ==> cap J SUBSET frontier s /\ pl_cell_with_boundary 2 (cap J) J`
  (X_CHOOSE_THEN `cap:(real^3->bool)->(real^3->bool)` (LABEL_TAC "capd0")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `J:real^3->bool` THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
    USE_THEN "inI" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!J:real^3->bool. J IN I0 ==> UNIONS cc0 INTER cap J = J` (LABEL_TAC "capo") THENL
   [X_GEN_TAC `J:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "capd0" (MP_TAC o C MATCH_MP (ASSUME `(J:real^3->bool) IN I0`)) THEN STRIP_TAC THEN
    SUBGOAL_THEN `(J:real^3->bool) IN components (surface_boundary cc0)` ASSUME_TAC THENL
     [UNDISCH_TAC `I0 SUBSET components (surface_boundary (cc0:(real^3->bool)->bool))` THEN
      UNDISCH_TAC `(J:real^3->bool) IN I0` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "cj" (MP_TAC o C MATCH_MP
      (ASSUME `(J:real^3->bool) IN components (surface_boundary cc0)`)) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`2`; `(cap:(real^3->bool)->(real^3->bool)) J`; `J:real^3->bool`]
                  MOI_CEL_CELL_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(UNIONS cc0 SUBSET (cap:(real^3->bool)->(real^3->bool)) J)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`(cap:(real^3->bool)->(real^3->bool)) J`; `J:real^3->bool`;
                     `J1:real^3->bool`] DISK_POLYGON) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `UNIONS cc0 SUBSET (cap:(real^3->bool)->(real^3->bool)) J` THEN
        UNDISCH_TAC `(J1:real^3->bool) SUBSET UNIONS cc0` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[moi_s28_bounds_disk] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real^3->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~(?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d (J1:real^3->bool))` THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN EXISTS_TAC `d:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(d:real^3->bool) SUBSET (cap:(real^3->bool)->(real^3->bool)) J` THEN
      UNDISCH_TAC `(cap:(real^3->bool)->(real^3->bool)) J SUBSET frontier s` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`frontier s:real^3->bool`; `cc0:(real^3->bool)->bool`;
                   `(cap:(real^3->bool)->(real^3->bool)) J`; `J:real^3->bool`]
                  MOI_S3CF_CAP_OUTSIDE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `UNIONS cc0 INTER ((cap:(real^3->bool)->(real^3->bool)) J DIFF J) = {}` THEN
    UNDISCH_TAC `(J:real^3->bool) SUBSET UNIONS cc0` THEN
    UNDISCH_TAC `(J:real^3->bool) SUBSET (cap:(real^3->bool)->(real^3->bool)) J` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!J J':real^3->bool. J IN I0 /\ J' IN I0 /\ ~(J = J')
                  ==> DISJOINT ((cap:(real^3->bool)->(real^3->bool)) J) (cap J')`
  (LABEL_TAC "capdis") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(J:real^3->bool) IN components (surface_boundary cc0) /\
                  (J':real^3->bool) IN components (surface_boundary cc0)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `I0 SUBSET components (surface_boundary (cc0:(real^3->bool)->bool))` THEN
      UNDISCH_TAC `(J:real^3->bool) IN I0` THEN UNDISCH_TAC `(J':real^3->bool) IN I0` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (J:real^3->bool) J'` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`surface_boundary (cc0:(real^3->bool)->bool)`; `J:real^3->bool`;
                     `J':real^3->bool`] COMPONENTS_EQ) THEN
      ASM_REWRITE_TAC[DISJOINT];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `UNIONS cc0 INTER ((cap:(real^3->bool)->(real^3->bool)) J DIFF J) = {} /\
      UNIONS cc0 INTER ((cap:(real^3->bool)->(real^3->bool)) J' DIFF J') = {}`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "capo" (MP_TAC o C MATCH_MP (ASSUME `(J:real^3->bool) IN I0`)) THEN
      USE_THEN "capo" (MP_TAC o C MATCH_MP (ASSUME `(J':real^3->bool) IN I0`)) THEN
      SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "capd0" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(J:real^3->bool) IN I0`)) THEN
    USE_THEN "capd0" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(J':real^3->bool) IN I0`)) THEN
    USE_THEN "cj" (STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(J:real^3->bool) IN components (surface_boundary cc0)`)) THEN
    USE_THEN "cj" (STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(J':real^3->bool) IN components (surface_boundary cc0)`)) THEN
    MATCH_MP_TAC MOI_S3CF_CAPS_DISJOINT THEN
    MAP_EVERY EXISTS_TAC [`frontier s:real^3->bool`; `UNIONS cc0:real^3->bool`;
                          `J:real^3->bool`; `J':real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* glue the caps on *)
  MP_TAC(ISPECL [`cc0:(real^3->bool)->bool`; `I0:(real^3->bool)->bool`;
                 `cap:(real^3->bool)->(real^3->bool)`]
    (MP MOI_S3CF_GLUE_CAPS (ASSUME (moi_n3 MOI_FND_EULER_VALUES)))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `J:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "capd0" (MP_TAC o C MATCH_MP (ASSUME `(J:real^3->bool) IN I0`)) THEN
    USE_THEN "capo" (MP_TAC o C MATCH_MP (ASSUME `(J:real^3->bool) IN I0`)) THEN
    SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e:(real^3->bool)->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `surface_boundary (e:(real^3->bool)->bool) = UNIONS E0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`surface_boundary (cc0:(real^3->bool)->bool)`;
                   `\jj:real^3->bool. ?d. d SUBSET frontier s /\ pl_cell_with_boundary 2 d jj`]
                  MOI_S3CF_SPLIT_COMPONENTS) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (e:(real^3->bool)->bool) SUBSET frontier s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNION_SUBSET] THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `J:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "capd0" (MP_TAC o C MATCH_MP (ASSUME `(J:real^3->bool) IN I0`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `2 <= CARD (E0:(real^3->bool)->bool)` THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `E0:(real^3->bool)->bool`; `e:(real^3->bool)->bool`]
      (MP MOI_S3CF_TWO_ESS (end_itlist CONJ
        [ASSUME `MOISE_286_STATEMENT`; ASSUME (moi_n3 MOI_FND_EULER_VALUES);
         ASSUME (moi_n3 MOI_FND_SURFACE_PLANAR)]))) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [MATCH_MP_TAC PAIRWISE_MONO THEN
        EXISTS_TAC `components (surface_boundary (cc0:(real^3->bool)->bool))` THEN
        ASM_REWRITE_TAC[PAIRWISE_DISJOINT_COMPONENTS];
        X_GEN_TAC `j:real^3->bool` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(j:real^3->bool) IN components (surface_boundary cc0)` ASSUME_TAC THENL
         [UNDISCH_TAC `E0 SUBSET components (surface_boundary (cc0:(real^3->bool)->bool))` THEN
          UNDISCH_TAC `(j:real^3->bool) IN E0` THEN SET_TAC[];
          ALL_TAC] THEN
        USE_THEN "cj" (MP_TAC o C MATCH_MP
          (ASSUME `(j:real^3->bool) IN components (surface_boundary cc0)`)) THEN
        SIMP_TAC[];
        MAP_EVERY X_GEN_TAC [`j:real^3->bool`; `d:real^3->bool`] THEN STRIP_TAC THEN
        USE_THEN "inE" (fun th -> MP_TAC(EQ_MP (SPEC `j:real^3->bool` th)
          (ASSUME `(j:real^3->bool) IN E0`))) THEN
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `complex_euler (e:(real^3->bool)->bool) =
                 complex_euler (cc0:(real^3->bool)->bool) + &(CARD (I0:(real^3->bool)->bool))` THEN
    UNDISCH_TAC `complex_euler (e:(real^3->bool)->bool) = &0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `E0 = {J1:real^3->bool}` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
    ASM_REWRITE_TAC[SING_SUBSET; CARD_SING] THEN
    MP_TAC(ISPEC `E0:(real^3->bool)->bool` CARD_EQ_0) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(2 <= CARD (E0:(real^3->bool)->bool))` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `J1:real^3->bool`; `e:(real^3->bool)->bool`]
    (MP MOI_S3CF_ONE_ESS (end_itlist CONJ
      [ASSUME `MOISE_286_STATEMENT`; ASSUME `MOISE_268_STATEMENT`;
       ASSUME (moi_n3 MOI_FND_BICOLLAR_CURVE_2); ASSUME (moi_n3 MOI_FND_EULER_VALUES);
       ASSUME (moi_n3 MOI_FND_SURFACE_PLANAR)]))) THEN
  REWRITE_TAC[ASSUME `surface_boundary (e:(real^3->bool)->bool) = UNIONS E0`;
              ASSUME `E0 = {J1:real^3->bool}`; UNIONS_1] THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Part 11: the witness's essential polygons are those bounding no          *)
(* 2-cell of T''_(2i+1); the type of a member; CLASSIFY_3.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CF_COMPONENT_SIDE = prove
 (`!(s:real^3->bool) t u.
     connected s /\ s SUBSET t UNION u /\ closed t /\ closed u /\ DISJOINT t u
     ==> s SUBSET t \/ s SUBSET u`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `connected (s:real^3->bool)` THEN REWRITE_TAC[CONNECTED_CLOSED] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real^3->bool`; `u:real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3CF_EVEN_PAIR = prove
 (`!(g:real^3->real^3) v pp dd s2 i.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2
     ==> closed (frontier (s2 (&2 * i))) /\ closed (frontier (s2 (&2 * i + &2))) /\
         DISJOINT (frontier (s2 (&2 * i))) (frontier (s2 (&2 * i + &2)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FRONTIER_CLOSED] THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:int` o MATCH_MP MOI_S3I2_LEVEL_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "kf") (ASSUME_TAC o CONJUNCT1)) THEN
  USE_THEN "kf" (MP_TAC o SPEC `&2 * i:int`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "kf" (MP_TAC o SPEC `&2 * i + &2:int`) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `DISJOINT ((s2:int->real^3->bool) (&2 * i)) (s2 (&2 * i + &2))` THEN
  UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i)) SUBSET s2 (&2 * i)` THEN
  UNDISCH_TAC `frontier ((s2:int->real^3->bool) (&2 * i + &2)) SUBSET s2 (&2 * i + &2)` THEN
  SET_TAC[]);;

let MOI_S3CF_ESS_POINT = prove
 (`!(g:real^3->real^3) v pp dd s2 i (c0:real^3->bool) cc0 jj.
     MOISE_314_STATEMENT /\
     (!s:real^3->bool. pl_solid_torus s ==> solid_torus s /\ (?j. spine j s /\ pl_sphere 1 j)) /\
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     FINITE cc0 /\ combinatorial_manifold_with_boundary 2 cc0 /\ UNIONS cc0 = c0 /\
     c0 SUBSET frontier (s2 (&2 * i + &1)) /\
     surface_boundary cc0 = c0 INTER moi_s32_evens s2 /\
     jj IN components (c0 INTER moi_s32_evens s2)
     ==> ((moi_s32_ess s2 (&2 * i) jj \/ moi_s32_ess s2 (&2 * i + &2) jj) <=>
          ~(?d. d SUBSET frontier (s2 (&2 * i + &1)) /\ pl_cell_with_boundary 2 d jj))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "m314") (CONJUNCTS_THEN2 (LABEL_TAC "bas")
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`] MOI_S3CF_EVEN_PAIR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `cc0:(real^3->bool)->bool` MOI_FSB_BD_CIRCLES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `jj:real^3->bool` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`(c0:real^3->bool) INTER moi_s32_evens s2`; `jj:real^3->bool`]
                IN_COMPONENTS_SUBSET) THEN
  MP_TAC(ISPECL [`(c0:real^3->bool) INTER moi_s32_evens s2`; `jj:real^3->bool`]
                IN_COMPONENTS_CONNECTED) THEN
  MP_TAC(ISPECL [`(c0:real^3->bool) INTER moi_s32_evens s2`; `jj:real^3->bool`]
                IN_COMPONENTS_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(jj:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i)) UNION
                                   frontier (s2 (&2 * i + &2))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`]
                  MOI_S3I2_ODD_EVENS) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(jj:real^3->bool) SUBSET c0 INTER moi_s32_evens s2` THEN
    UNDISCH_TAC `(c0:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i + &1))` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNION] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`jj:real^3->bool`; `frontier ((s2:int->real^3->bool) (&2 * i))`;
                 `frontier ((s2:int->real^3->bool) (&2 * i + &2))`] MOI_S3CF_COMPONENT_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `~((jj:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i + &2)))` ASSUME_TAC THENL
     [UNDISCH_TAC `DISJOINT (frontier ((s2:int->real^3->bool) (&2 * i)))
                            (frontier (s2 (&2 * i + &2)))` THEN
      UNDISCH_TAC `~(jj:real^3->bool = {})` THEN
      UNDISCH_TAC `(jj:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i))` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `&2 * i:int`;
                   `jj:real^3->bool`] MOI_S3CF_ESS_TRANSFER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_INTER] THEN
      UNDISCH_TAC `(jj:real^3->bool) SUBSET c0 INTER moi_s32_evens s2` THEN
      UNDISCH_TAC `(c0:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i + &1))` THEN SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[moi_s32_ess];
    SUBGOAL_THEN `~((jj:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i)))` ASSUME_TAC THENL
     [UNDISCH_TAC `DISJOINT (frontier ((s2:int->real^3->bool) (&2 * i)))
                            (frontier (s2 (&2 * i + &2)))` THEN
      UNDISCH_TAC `~(jj:real^3->bool = {})` THEN
      UNDISCH_TAC `(jj:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i + &2))` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `&2 * i + &1:int`;
                   `jj:real^3->bool`] MOI_S3CF_ESS_TRANSFER) THEN
    REWRITE_TAC[INT_ARITH `(&2 * i + &1) + &1 = &2 * i + &2:int`] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_INTER] THEN
      UNDISCH_TAC `(jj:real^3->bool) SUBSET c0 INTER moi_s32_evens s2` THEN
      UNDISCH_TAC `(c0:real^3->bool) SUBSET frontier ((s2:int->real^3->bool) (&2 * i + &1))` THEN SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[moi_s32_ess]]);;

let MOI_S3CF_ESSC_C0 = prove
 (`!(g:real^3->real^3) v pp dd s2 i (c0:real^3->bool) cc0.
     MOISE_314_STATEMENT /\
     (!s:real^3->bool. pl_solid_torus s ==> solid_torus s /\ (?j. spine j s /\ pl_sphere 1 j)) /\
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     FINITE cc0 /\ combinatorial_manifold_with_boundary 2 cc0 /\ UNIONS cc0 = c0 /\
     c0 SUBSET frontier (s2 (&2 * i + &1)) /\
     surface_boundary cc0 = c0 INTER moi_s32_evens s2
     ==> moi_s32_essc s2 i c0 =
         {jj | jj IN components (surface_boundary cc0) /\
               ~(?d. d SUBSET frontier (s2 (&2 * i + &1)) /\ pl_cell_with_boundary 2 d jj)} /\
         moi_s32_inessc s2 i c0 =
         {jj | jj IN components (surface_boundary cc0) /\
               (?d. d SUBSET frontier (s2 (&2 * i + &1)) /\ pl_cell_with_boundary 2 d jj)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!jj. jj IN components ((c0:real^3->bool) INTER moi_s32_evens s2)
         ==> ((moi_s32_ess s2 (&2 * i) jj \/ moi_s32_ess s2 (&2 * i + &2) jj) <=>
              ~(?d. d SUBSET frontier ((s2:int->real^3->bool) (&2 * i + &1)) /\
                    pl_cell_with_boundary 2 d jj))`
  ASSUME_TAC THENL
   [X_GEN_TAC `jj:real^3->bool` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3CF_ESS_POINT THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                          `dd:int->real^3->bool`; `c0:real^3->bool`;
                          `cc0:(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s32_essc; moi_s32_inessc] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN CONJ_TAC THEN X_GEN_TAC `jj:real^3->bool` THEN
  ASM_CASES_TAC `(jj:real^3->bool) IN components (c0 INTER moi_s32_evens s2)` THEN
  ASM_SIMP_TAC[]);;

(* The type of a member at all levels. *)

let MOI_S3CF_MEMBER_TYPE = prove
 (mk_imp(list_mk_conj [`MOISE_314_STATEMENT`; `MOISE_286_STATEMENT`; `MOISE_268_STATEMENT`;
                       moi_n3 MOI_FND_BICOLLAR_CURVE_2; moi_n3 MOI_FND_SURFACE_PLANAR;
                       moi_n3 MOI_FND_PL_SOLID_TORUS_BASIC; moi_n3 MOI_FND_EULER_VALUES],
  `!(g:real^3->real^3) v pp dd s2 i cc (c:real^3->bool).
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\
     UNIONS cc = c /\ connected c /\ ~(c = {}) /\
     surface_boundary cc = c INTER moi_s32_evens s2 /\
     c INTER moi_s32_evens s2 SUBSET frontier (s2 (&2 * i)) UNION frontier (s2 (&2 * i + &2)) /\
     (!jj. jj IN components (c INTER frontier (s2 (&2 * i)))
           ==> moi_s32_ess s2 (&2 * i) jj) /\
     (!jj. jj IN components (c INTER frontier (s2 (&2 * i + &2)))
           ==> moi_s32_ess s2 (&2 * i + &2) jj) /\
     moi_s32_hist s2 i cc c
     ==> DISJOINT c (moi_s32_evens s2) \/
         ?j j'. pl_annulus_with_ends c j j' /\
                c INTER moi_s32_evens s2 = j UNION j' /\
                (moi_s32_ess s2 (&2 * i) j \/ moi_s32_ess s2 (&2 * i + &2) j) /\
                (moi_s32_ess s2 (&2 * i) j' \/ moi_s32_ess s2 (&2 * i + &2) j')`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "m314") (CONJUNCTS_THEN2 (LABEL_TAC "m286")
    (CONJUNCTS_THEN2 (LABEL_TAC "m268")
    (CONJUNCTS_THEN2 (LABEL_TAC "bic") (CONJUNCTS_THEN2 (LABEL_TAC "planar")
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "bas1") (LABEL_TAC "bas2"))
    (LABEL_TAC "ev"))))))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `c:real^3->bool`]
                MOI_S3CF_INESS_EMPTY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s32_hist s2 i cc c` THEN REWRITE_TAC[moi_s32_hist] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real^3->bool` (X_CHOOSE_THEN `cc0:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `i:int`; `c0:real^3->bool`;
                 `cc0:(real^3->bool)->bool`] MOI_S3CF_ESSC_C0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "m314" ACCEPT_TAC; USE_THEN "bas1" ACCEPT_TAC];
    STRIP_TAC] THEN
  SUBGOAL_THEN `pl_solid_torus ((s2:int->real^3->bool) (&2 * i + &1))` ASSUME_TAC THENL
   [MP_TAC(SPEC `&2 * i + &1:int` (MATCH_MP MOI_S3GF_TOWER_TORI
      (ASSUME `moi_s32_tower g v pp dd s2`))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(s2:int->real^3->bool) (&2 * i + &1)`; `cc0:(real^3->bool)->bool`]
    (MP MOI_S3CF_TORUS_COUNT (end_itlist CONJ
      [ASSUME `MOISE_286_STATEMENT`; ASSUME `MOISE_268_STATEMENT`;
       ASSUME (moi_n3 MOI_FND_BICOLLAR_CURVE_2); ASSUME (moi_n3 MOI_FND_EULER_VALUES);
       ASSUME (moi_n3 MOI_FND_SURFACE_PLANAR)]))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    USE_THEN "bas2" (MATCH_MP_TAC o SPEC `(s2:int->real^3->bool) (&2 * i + &1)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM(ASSUME `moi_s32_essc s2 i c0 =
    {jj | jj IN components (surface_boundary cc0) /\
          ~(?d. d SUBSET frontier ((s2:int->real^3->bool) (&2 * i + &1)) /\
                pl_cell_with_boundary 2 d jj)}`);
              GSYM(ASSUME `moi_s32_inessc s2 i c0 =
    {jj | jj IN components (surface_boundary cc0) /\
          (?d. d SUBSET frontier ((s2:int->real^3->bool) (&2 * i + &1)) /\
               pl_cell_with_boundary 2 d jj)}`)] THEN
  UNDISCH_TAC `moi_s32_essc s2 i c = moi_s32_essc s2 i c0` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBST1_TAC(ASSUME
    `moi_s32_essc s2 i c = components ((c:real^3->bool) INTER moi_s32_evens s2)`) THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN UNDISCH_TAC `components ((c:real^3->bool) INTER moi_s32_evens s2) = {}` THEN
    REWRITE_TAC[COMPONENTS_EQ_EMPTY; DISJOINT];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  SUBGOAL_THEN `complex_euler (cc:(real^3->bool)->bool) = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `complex_euler (cc0:(real^3->bool)->bool) +
                 &(CARD (moi_s32_inessc s2 i c0)) = &0` THEN
    UNDISCH_TAC `complex_euler (cc:(real^3->bool)->bool) +
                 &(CARD (moi_s32_inessc s2 i c)) =
                 complex_euler (cc0:(real^3->bool)->bool) +
                 &(CARD (moi_s32_inessc s2 i c0))` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `components ((c:real^3->bool) INTER moi_s32_evens s2) HAS_SIZE 2` THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:real^3->bool` (X_CHOOSE_THEN `j':real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`j:real^3->bool`; `j':real^3->bool`] THEN
  SUBGOAL_THEN `(j:real^3->bool) IN components (c INTER moi_s32_evens s2) /\
                (j':real^3->bool) IN components (c INTER moi_s32_evens s2)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD (components (surface_boundary (cc:(real^3->bool)->bool))) = 2`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_SING; NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->bool) INTER moi_s32_evens s2 = j UNION j'` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [UNIONS_COMPONENTS] THEN
    ASM_REWRITE_TAC[UNIONS_2];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `moi_s32_essc s2 i c = components ((c:real^3->bool) INTER moi_s32_evens s2)` THEN
    REWRITE_TAC[moi_s32_essc; EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `j:real^3->bool`) THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `moi_s32_essc s2 i c = components ((c:real^3->bool) INTER moi_s32_evens s2)` THEN
    REWRITE_TAC[moi_s32_essc; EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `j':real^3->bool`) THEN ASM_REWRITE_TAC[]] THEN
  USE_THEN "planar" (MP_TAC o SPEC `cc:(real^3->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `1` o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `h:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC ANNULUS_FROM_HOLED THEN
  MAP_EVERY EXISTS_TAC [`f:real^2->real^3`; `h:real^3->real^2`] THEN
  ASM_MESON_TAC[IN_COMPONENTS_CONNECTED; IN_COMPONENTS_NONEMPTY; COMPONENTS_NONOVERLAP;
                DISJOINT]);;

let moi_s3cf_top_conjuncts =
  let rec take n th = if n <= 1 then [th] else CONJUNCT1 th :: take (n - 1) (CONJUNCT2 th) in
  take;;

let CLASSIFY_3 = prove
 (MOI_S32_CLASSIFY_3,
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(MATCH_MP MOI_S3CF_MEMBER_TYPE (end_itlist CONJ
      (map (fun k -> el k (moi_s3cf_top_conjuncts 9 th)) [0; 1; 2; 3; 4; 5; 7])))) THEN
  DISCH_THEN(LABEL_TAC "type") THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                       `dd:int->real^3->bool`; `s2:int->real^3->bool`;
                       `fam:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN REWRITE_TAC[moi_s32_reduced] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3S6_STATE3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `c:real^3->bool` THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_s32_state3 g dd s2 (:int) fam` THEN REWRITE_TAC[moi_s32_state3] THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `(c:real^3->bool) IN fam`) o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:int` (X_CHOOSE_THEN `cc:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "type" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                        `dd:int->real^3->bool`; `cc:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[]);;


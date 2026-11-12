(* ========================================================================= *)
(* pc_moi_s33_ltd7: Moise 33.1 Lemma 7 (GTM 47, pp.232-233), one splitting  *)
(* step.  Main theorem LTD_STEP : |- MOI_S33_LTD_STEP                       *)
(* (pc_moi_s33_stmt.ml).  Route: push the loop theorem disk off the         *)
(* pseudo-cells (MOI_S39_PUSH_BODY), split Bd X at it away from them        *)
(* (MOI_FND_SPLIT_DISK_R3), keep a separating piece (SPLIT_ESSENTIAL and    *)
(* MOISE_302), fill it (BOUNDS); the traces are untouched and chi of the    *)
(* boundary rises by at least 1.  The inputs SPLIT_DISK_R3, PUSH_BODY and   *)
(* the four s33_conn lemmas are antecedents of MOI_S3L7_LTD_STEP_COND       *)
(* (stated with mk_imp); they are discharged in Part 7 (pc_moi_fnd_split),  *)
(* Part 8 (pc_moi_s33_conn) and Part 9 (S39_PUSH of pc_moi_s33_push).       *)
(* ========================================================================= *)

needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_fnd_bicol.ml";;
needs "src/pc_moi_s33_l9stmt.ml";;
needs "src/pc_moi_s30_comp.ml";;
needs "src/pc_moi_s30_bound.ml";;
needs "src/pc_moi_s26_nbhd.ml";;
needs "src/pc_moi_s26_cut.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_fnd_rn.ml";;
needs "src/pc_moi_fnd_euler.ml";;
needs "src/pc_moi_s27.ml";;
needs "src/pc_moi_fnd_surfa.ml";;
needs "src/pc_moi_fnd_m3a.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_fnd_split.ml";;
needs "src/pc_moi_fnd_sptrace.ml";;
needs "src/pc_moi_s33_conn.ml";;
needs "src/pc_moi_s33_push.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1: the loop theorem disk as a PL disk with a PL circle as           *)
(* boundary; W is open; the union of the pseudo-cells is closed; the push   *)
(* off the pseudo-cells (MOI_S39_PUSH_BODY with u = W).                     *)
(* ========================================================================= *)

let MOI_S3L7_LTD_CELL = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) x d.
     moi_s33_ltd t l h x d
     ==> ?j. pl_cell_with_boundary 2 d j /\ pl_sphere 1 j /\
             d INTER frontier (UNIONS x) = j /\ d SUBSET moi_s33_ww t l h /\
             compact d /\ j SUBSET d /\
             ~(?z. homotopic_with (\f. T)
                     (subtopology euclidean j,subtopology euclidean (frontier (UNIONS x)))
                     (\y. y) (\y. z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_ltd] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `IMAGE (f:real^3->real^3) (relative_frontier k)` THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (d:real^3->bool)
                  (IMAGE (f:real^3->real^3) (relative_frontier k))` ASSUME_TAC THENL
   [REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:real^3->bool`; `IMAGE (f:real^3->real^3) (relative_frontier k)`]
    MOI_S3CP_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `d:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    MP_TAC(ISPECL [`k:real^3->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]]);;

let MOI_S3L7_WW_OPEN = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3).
     compact (IMAGE h (UNIONS l)) ==> open (moi_s33_ww t l h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s33_ww] THEN
  MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_INTERIOR; COMPACT_IMP_CLOSED]);;

(* The graph is a finite simplicial complex; its edges are segments.        *)

let MOI_S3L7_TUBE_SC = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3).
     moi_s33_tube t l h ==> simplicial_complex l /\ FINITE l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_tube; graph_in_complex; simplicial_subcomplex] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
  MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
  ASM_REWRITE_TAC[simplicial_subcomplex]);;

let MOI_S3L7_PCS_CLOSED = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c.
     moi_s33_hd t l h e c
     ==> closed (moi_s39_pcs l e) /\
         (!s. s IN l /\ aff_dim s = &1 ==> e s SUBSET moi_s39_pcs l e)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_s33_tube t l (h:real^3->real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_hd t l (h:real^3->real^3) e c` THEN SIMP_TAC[moi_s33_hd];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L7_TUBE_SC) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_s39_pcs] THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FSA_EDGE_VERTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `q:real^3`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)))) THEN
      UNDISCH_TAC `moi_s33_hd t l (h:real^3->real^3) e c` THEN REWRITE_TAC[moi_s33_hd] THEN
      DISCH_THEN(MP_TAC o SPECL [`p:real^3`; `q:real^3`] o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[pseudo_cell] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM(el 3 (CONJUNCTS (CONJUNCT1 th)))]) THEN
      REWRITE_TAC[CLOSED_CLOSURE]];
    REWRITE_TAC[moi_s39_pcs] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* The push: an LTD in a piece is replaced by one missing the pseudo-cells. *)

let MOI_S3L7_PUSHED = prove
 (mk_imp(mk_conj(MOI_S33_TUBE_FACTS, MOI_S39_PUSH_BODY),
  `!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x v d.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ {v} IN l /\
     moi_s33_ltd t l h x d /\ d SUBSET c v
     ==> ?d'. moi_s33_ltd t l h x d' /\ d' INTER moi_s39_pcs l e = {}`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tf") (LABEL_TAC "push")) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                       `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`;
                       `v:real^3`; `d:real^3->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `moi_s33_tube t l (h:real^3->real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_hd t l (h:real^3->real^3) e c` THEN SIMP_TAC[moi_s33_hd];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (h:real^3->real^3) (UNIONS l))` ASSUME_TAC THENL
   [USE_THEN "tf" (MP_TAC o C MP (ASSUME `moi_s33_tube t l (h:real^3->real^3)`) o
      SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `x:(real^3->bool)->bool`; `d:real^3->bool`] MOI_S3L7_LTD_CELL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `j:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]
               MOI_S3L7_PCS_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "push" (MP_TAC o SPECL
    [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
     `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
     `x:(real^3->bool)->bool`; `v:real^3`; `d:real^3->bool`;
     `moi_s33_ww t l (h:real^3->real^3)`; `d INTER moi_s39_pcs l e`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_S3L7_WW_OPEN; SUBSET_REFL; COMPACT_INTER_CLOSED] THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET moi_s33_ww t l h` THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET c (v:real^3)` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d':real^3->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(d:real^3->bool) SUBSET moi_s33_ww t l h` THEN SET_TAC[]);;

(* ========================================================================= *)
(* Part 2: the split (MOI_FND_SPLIT_DISK_R3 with its x-clause applied       *)
(* to x, in one existential), and the separation by the frontier of a       *)
(* compact set of a set in its interior from a set outside it.             *)
(* ========================================================================= *)

let MOI_S3L7_SPLIT_FACTS = prove
 (mk_imp(MOI_FND_SPLIT_DISK_R3,
  `!(m:(real^3->bool)->bool) (x:(real^3->bool)->bool) d j v.
     FINITE m /\ combinatorial_manifold 2 m /\ frontier (UNIONS x) = UNIONS m /\
     FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\ open v /\ d SUBSET v
     ==> ?a j1 j2 d1 d2 (m':(real^3->bool)->bool) (x':(real^3->bool)->bool).
           pl_annulus_with_ends a j1 j2 /\ a SUBSET UNIONS m INTER v /\
           j SUBSET a DIFF (j1 UNION j2) /\
           pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
           d1 SUBSET v /\ d2 SUBSET v /\ DISJOINT d1 d2 /\
           d1 INTER UNIONS m = j1 /\ d2 INTER UNIONS m = j2 /\
           FINITE m' /\ combinatorial_manifold 2 m' /\
           UNIONS m' = (UNIONS m DIFF a) UNION d1 UNION d2 /\
           complex_euler m' = complex_euler m + &2 /\
           FINITE x' /\ combinatorial_manifold_with_boundary 3 x' /\
           frontier (UNIONS x') = UNIONS m' /\
           (UNIONS x DIFF UNIONS x') UNION (UNIONS x' DIFF UNIONS x) SUBSET v`),
  DISCH_THEN(LABEL_TAC "split") THEN
  MAP_EVERY X_GEN_TAC [`m:(real^3->bool)->bool`; `x:(real^3->bool)->bool`;
                       `d:real^3->bool`; `j:real^3->bool`; `v:real^3->bool`] THEN
  STRIP_TAC THEN
  USE_THEN "split" (MP_TAC o SPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`;
                                    `j:real^3->bool`; `v:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3->bool` (X_CHOOSE_THEN `j1:real^3->bool`
    (X_CHOOSE_THEN `j2:real^3->bool` (X_CHOOSE_THEN `d1:real^3->bool`
    (X_CHOOSE_THEN `d2:real^3->bool` (X_CHOOSE_THEN `m':(real^3->bool)->bool`
    STRIP_ASSUME_TAC)))))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:(real^3->bool)->bool` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                        `d1:real^3->bool`; `d2:real^3->bool`;
                        `m':(real^3->bool)->bool`; `x':(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* The frontier of a compact set separates its interior from its outside.  *)

let MOI_S3L7_SEP_FRONTIER = prove
 (`!(xx:real^3->bool) hs ks.
     compact xx /\ hs SUBSET interior xx /\ DISJOINT ks xx
     ==> euclidean_separates (frontier xx) hs ks`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[euclidean_separates] THEN
  MAP_EVERY EXISTS_TAC [`interior xx:real^3->bool`; `(:real^3) DIFF xx`] THEN
  SUBGOAL_THEN `closed (xx:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR; GSYM closed] THEN
  REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
  MP_TAC(ISPEC `xx:real^3->bool` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `DISJOINT (ks:real^3->bool) xx` THEN SET_TAC[]);;

(* ========================================================================= *)
(* Part 3: the kept piece.  SPLIT_ESSENTIAL (the curve is essential in      *)
(* the connected surface): the split surface is connected (chi + 2), or    *)
(* consists of two nonspherical pieces (each chi <= 1), one of which        *)
(* separates (MOISE_302) and has chi >= chi + 1.                            *)
(* ========================================================================= *)

let MOI_S3L7_ESS = MP SPLIT_ESSENTIAL (CONJ (ISPEC `(:3)` MOISE_273) DISK_COMPLEMENT);;

let MOI_S3L7_LE1 = MP MOI_S3CP_EULER_LE1 (INST_TYPE [`:3`,`:N`] SURFACE_EULER_SPHERE);;

let MOI_S3L7_KEPT = prove
 (mk_imp(`MOISE_302_STATEMENT`,
  `!(m:(real^3->bool)->bool) a j j1 j2 d1 d2 (m':(real^3->bool)->bool) hs ks.
     FINITE m /\ combinatorial_manifold 2 m /\ connected (UNIONS m) /\
     pl_annulus_with_ends a j1 j2 /\ a SUBSET UNIONS m /\
     pl_sphere 1 j /\ j SUBSET a DIFF (j1 UNION j2) /\
     pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
     DISJOINT d1 d2 /\ d1 INTER UNIONS m = j1 /\ d2 INTER UNIONS m = j2 /\
     FINITE m' /\ combinatorial_manifold 2 m' /\
     UNIONS m' = (UNIONS m DIFF a) UNION d1 UNION d2 /\
     complex_euler m' = complex_euler m + &2 /\
     ~(?z. homotopic_with (\f. T)
             (subtopology euclidean j,subtopology euclidean (UNIONS m))
             (\x. x) (\x. z)) /\
     closed hs /\ closed ks /\ connected hs /\ connected ks /\
     ~(hs = {}) /\ ~(ks = {}) /\
     DISJOINT (UNIONS m') hs /\ DISJOINT (UNIONS m') ks /\
     euclidean_separates (UNIONS m') hs ks
     ==> ?mb. FINITE mb /\ combinatorial_manifold 2 mb /\ connected (UNIONS mb) /\
              ~(UNIONS mb = {}) /\ UNIONS mb IN components (UNIONS m') /\
              FINITE (components (UNIONS m')) /\
              euclidean_separates (UNIONS mb) hs ks /\
              complex_euler m + &1 <= complex_euler mb`),
  DISCH_THEN(LABEL_TAC "302") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(d1:real^3->bool) SUBSET UNIONS m'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j:real^3->bool`;
                `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
                `m':(real^3->bool)->bool`] MOI_S3L7_ESS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `UNIONS (m':(real^3->bool)->bool)`)) THEN
  SUBGOAL_THEN `~(UNIONS (m':(real^3->bool)->bool) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d1:real^3->bool`; `j1:real^3->bool`] MOI_S3CP_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(d1:real^3->bool) SUBSET UNIONS m'` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `m1:(real^3->bool)->bool` (X_CHOOSE_THEN `m2:(real^3->bool)->bool`
      STRIP_ASSUME_TAC))) THENL
   [EXISTS_TAC `m':(real^3->bool)->bool` THEN
    SUBGOAL_THEN `components (UNIONS (m':(real^3->bool)->bool)) = {UNIONS m'}`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[COMPONENTS_EQ_SING]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_SING; FINITE_SING] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS m1 UNION UNIONS m2 = UNIONS (m':(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNIONS_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `complex_euler (m:(real^3->bool)->bool) + &2 =
                complex_euler (m1:(real^3->bool)->bool) + complex_euler (m2:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `complex_euler (m':(real^3->bool)->bool) = complex_euler (m:(real^3->bool)->bool) + &2` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `m':(real^3->bool)->bool = m1 UNION m2` THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_S3CP_EULER_DISJOINT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `m':(real^3->bool)->bool = m1 UNION m2` THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `complex_euler (m1:(real^3->bool)->bool) <= &1 /\
                complex_euler (m2:(real^3->bool)->bool) <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S3L7_LE1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS (m1:(real^3->bool)->bool)) /\ closed (UNIONS (m2:(real^3->bool)->bool))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC MOI_S3CP_COMPLEX_COMPACT THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `components (UNIONS (m':(real^3->bool)->bool)) =
                {UNIONS (m1:(real^3->bool)->bool), UNIONS (m2:(real^3->bool)->bool)}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS m1 UNION UNIONS m2 = UNIONS (m':(real^3->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MOI_S3CP_COMPONENTS_2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (hs:real^3->bool) ks` ASSUME_TAC THENL
   [UNDISCH_TAC `euclidean_separates (UNIONS (m':(real^3->bool)->bool)) hs ks` THEN
    REWRITE_TAC[euclidean_separates] THEN
    DISCH_THEN(X_CHOOSE_THEN `uu:real^3->bool` (X_CHOOSE_THEN `vv:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (uu:real^3->bool) vv`; `(hs:real^3->bool) SUBSET uu`;
      `(ks:real^3->bool) SUBSET vv`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "302" (MP_TAC o SPECL [`(:real^3)`; `UNIONS (m':(real^3->bool)->bool)`;
                                  `hs:real^3->bool`; `ks:real^3->bool`] o
                  REWRITE_RULE[MOISE_302_STATEMENT]) THEN
  REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; MOI_S3CP_SEP_UNIV] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(SIMP_TAC[CONVEX_IMP_SIMPLY_CONNECTED; CONVEX_UNIV] THEN NO_TAC) THEN
    TRY(ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN NO_TAC) THEN
    TRY(MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_S3CP_COMPLEX_COMPACT THEN
        EXISTS_TAC `2` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    ASM_MESON_TAC[DISJOINT_SYM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `m1:(real^3->bool)->bool`; EXISTS_TAC `m2:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[IN_INSERT; FINITE_INSERT; FINITE_EMPTY] THEN
  UNDISCH_TAC `complex_euler (m:(real^3->bool)->bool) + &2 =
               complex_euler (m1:(real^3->bool)->bool) + complex_euler (m2:(real^3->bool)->bool)` THEN
  UNDISCH_TAC `complex_euler (m1:(real^3->bool)->bool) <= &1` THEN
  UNDISCH_TAC `complex_euler (m2:(real^3->bool)->bool) <= &1` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Part 4: the fill of a closed connected surface (BOUNDS discharged by     *)
(* MOISE_266 and its other inputs COMPACT_NBHD, CUT and                     *)
(* COMPLEX_EULER_PL_INVARIANT, as in MOI_S3CN_BOUNDS of s33_conn), the      *)
(* outer set ks = UNIV minus Int N' and the graph image K'.                 *)
(* ========================================================================= *)

let MOI_S3L7_FILL = prove
 (`MOISE_266_STATEMENT
   ==> !m:(real^3->bool)->bool.
         FINITE m /\ combinatorial_manifold 2 m /\ connected (UNIONS m) /\
         ~(UNIONS m = {})
         ==> ?x:(real^3->bool)->bool.
               FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
               UNIONS x = UNIONS m UNION inside (UNIONS m) /\
               frontier (UNIONS x) = UNIONS m /\ complex_boundary x = UNIONS m /\
               complex_euler (boundary_complex x) = complex_euler m`,
  DISCH_TAC THEN MP_TAC BOUNDS THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ACCEPT_TAC(MATCH_MP COMPACT_NBHD (INST_TYPE [`:3`,`:N`] DERIVED_NBHD_COMBINATORIAL));
    ACCEPT_TAC(MATCH_MP CUT (CONJ (ASSUME `MOISE_266_STATEMENT`) SPHERE_SPLIT));
    MATCH_ACCEPT_TAC COMPLEX_EULER_PL_INVARIANT]);;

(* K' and ks = UNIV DIFF interior N'.                                        *)

let MOI_S3L7_TUBE_SETS = prove
 (mk_imp(MOI_S33_TUBE_FACTS,
  `!(t:(real^3->bool)->bool) l (h:real^3->real^3).
     moi_s33_tube t l h
     ==> compact (IMAGE h (UNIONS l)) /\ connected (IMAGE h (UNIONS l)) /\
         ~(IMAGE h (UNIONS l) = {}) /\
         IMAGE h (UNIONS l) SUBSET interior (IMAGE h (derived_nbhd t l)) /\
         closed ((:real^3) DIFF interior (IMAGE h (derived_nbhd t l))) /\
         connected ((:real^3) DIFF interior (IMAGE h (derived_nbhd t l))) /\
         ~((:real^3) DIFF interior (IMAGE h (derived_nbhd t l)) = {}) /\
         ~bounded ((:real^3) DIFF interior (IMAGE h (derived_nbhd t l))) /\
         open (moi_s33_ww t l h) /\
         DISJOINT (moi_s33_ww t l h) (IMAGE h (UNIONS l)) /\
         DISJOINT (moi_s33_ww t l h)
                  ((:real^3) DIFF interior (IMAGE h (derived_nbhd t l))) /\
         IMAGE h (derived_frontier t l) SUBSET
         (:real^3) DIFF interior (IMAGE h (derived_nbhd t l))`),
  DISCH_THEN(LABEL_TAC "tf") THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  USE_THEN "tf" (MP_TAC o C MP (ASSUME `moi_s33_tube t l (h:real^3->real^3)`) o
    SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`]) THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun i -> ASSUME_TAC (el i (CONJUNCTS th))) [2;3;5;7;8;11]) THEN
  SUBGOAL_THEN `UNIONS l SUBSET UNIONS (t:(real^3->bool)->bool) /\
                (h:real^3->real^3) continuous_on UNIONS t /\
                connected (UNIONS (l:(real^3->bool)->bool)) /\ ~(UNIONS l = {})`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_tube t l (h:real^3->real^3)` THEN
    REWRITE_TAC[moi_s33_tube; graph_in_complex; simplicial_subcomplex] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[EMPTY_UNIONS] THEN DISCH_THEN(MP_TAC o SPEC `s:real^3->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `aff_dim (s:real^3->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (h:real^3->real^3) (derived_nbhd t l))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `UNIONS (t:(real^3->bool)->bool)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~bounded ((:real^3) DIFF interior (IMAGE (h:real^3->real^3)
                                                  (derived_nbhd t l)))` ASSUME_TAC THENL
   [DISCH_TAC THEN MP_TAC(INST_TYPE [`:3`,`:N`] NOT_BOUNDED_UNIV) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `((:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l)))
                UNION IMAGE h (derived_nbhd t l)` THEN
    ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED] THEN
    MP_TAC(ISPEC `IMAGE (h:real^3->real^3) (derived_nbhd t l)` INTERIOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `UNIONS (t:(real^3->bool)->bool)` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
    MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_UNIV; OPEN_INTERIOR];
    REWRITE_TAC[GSYM CLOSURE_COMPLEMENT] THEN MATCH_MP_TAC CONNECTED_CLOSURE THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN UNDISCH_TAC `~bounded ((:real^3) DIFF interior (IMAGE (h:real^3->real^3)
                                                (derived_nbhd t l)))` THEN
    ASM_REWRITE_TAC[BOUNDED_EMPTY];
    MATCH_MP_TAC MOI_S3L7_WW_OPEN THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s33_ww] THEN SET_TAC[];
    REWRITE_TAC[moi_s33_ww] THEN SET_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `frontier (IMAGE (h:real^3->real^3) (derived_nbhd t l))`)) THEN
    REWRITE_TAC[frontier] THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Part 5: the invariants of the new 3-manifold.  The statements of four    *)
(* lemmas of pc_moi_s33_conn (discharged in Part 8) are antecedents here.   *)
(* x' fills a component b of the new surface mm, which agrees with Bd X off *)
(* a closed set z inside Int N' missing the pseudo-cells; K' lies inside b  *)
(* and UNIV minus Int N' outside.                                           *)
(* ========================================================================= *)

let MOI_S3L7_CN_CROSSING_LOCAL =
 `!(s:real^3->bool) t t' y w.
     pl_crossing_at s t y /\ open w /\ y IN w /\ t INTER w = t' INTER w
     ==> pl_crossing_at s t' y`;;

let MOI_S3L7_CN_TRACE_KEEP =
 `!(e:real^3->bool) j p d jd bdx b.
     pseudo_cell e j p /\ disk_with_boundary d jd /\ pl_sphere 1 jd /\
     jd SUBSET e /\ jd SUBSET bdx /\ e INTER bdx SUBSET jd /\ d SUBSET e DIFF j /\
     closed bdx /\ b IN components bdx /\ p IN d DIFF jd /\ p IN inside b /\
     j SUBSET outside b
     ==> jd SUBSET b /\ e INTER b = jd /\ e INTER (b UNION inside b) = d`;;

let MOI_S3L7_CN_SEP_INSIDE =
 `!(b:real^3->bool) k1 k2.
     compact b /\ separates_in (:real^3) b k1 k2 /\
     connected k1 /\ ~(k1 = {}) /\ DISJOINT b k1 /\
     connected k2 /\ ~bounded k2 /\ DISJOINT b k2
     ==> k1 SUBSET inside b /\ k2 SUBSET outside b`;;

let MOI_S3L7_CN_INSIDE_UNION_CONNECTED =
 `!m:(real^3->bool)->bool.
     MOISE_266_STATEMENT /\ FINITE m /\ combinatorial_manifold 2 m /\
     connected (UNIONS m) /\ ~(UNIONS m = {})
     ==> connected (UNIONS m UNION inside (UNIONS m))`;;

let MOI_S3L7_CN =
  list_mk_conj [MOI_S3L7_CN_CROSSING_LOCAL; MOI_S3L7_CN_TRACE_KEEP;
                MOI_S3L7_CN_SEP_INSIDE; MOI_S3L7_CN_INSIDE_UNION_CONNECTED];;

(* A component of a closed set with finitely many components is closed and *)
(* so is the union of the others.                                           *)

let MOI_S3L7_COMPONENT_REST = prove
 (`!(mm:real^3->bool) b.
     closed mm /\ b IN components mm /\ FINITE (components mm)
     ==> closed b /\ b SUBSET mm /\ connected b /\ closed (mm DIFF b)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CLOSED_COMPONENTS THEN EXISTS_TAC `mm:real^3->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN EXISTS_TAC `mm:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mm DIFF b = UNIONS (components mm DELETE (b:real^3->bool))` SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_DELETE] THEN EQ_TAC THENL
     [STRIP_TAC THEN MP_TAC(ISPEC `mm:real^3->bool` UNIONS_COMPONENTS) THEN
      GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `cc:real^3->bool` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `cc:real^3->bool` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET];
        MP_TAC(ISPECL [`mm:real^3->bool`; `cc:real^3->bool`; `b:real^3->bool`]
          COMPONENTS_NONOVERLAP) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN cc` THEN SET_TAC[]]];
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
    ASM_MESON_TAC[CLOSED_COMPONENTS]]);;

let MOI_S3L7_NEW_INV = prove
 (mk_imp(mk_conj(MOI_S3L7_CN_CROSSING_LOCAL, MOI_S3L7_CN_TRACE_KEEP),
  `!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x mm z b
    (x':(real^3->bool)->bool).
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\
     closed mm /\ closed z /\ DISJOINT z (moi_s39_pcs l e) /\
     z SUBSET interior (IMAGE h (derived_nbhd t l)) /\
     mm DIFF z = frontier (UNIONS x) DIFF z /\
     b IN components mm /\ FINITE (components mm) /\
     IMAGE h (UNIONS l) SUBSET inside b /\
     (:real^3) DIFF interior (IMAGE h (derived_nbhd t l)) SUBSET outside b /\
     FINITE x' /\ combinatorial_manifold_with_boundary 3 x' /\
     UNIONS x' = b UNION inside b /\ frontier (UNIONS x') = b /\ connected (UNIONS x')
     ==> moi_s33_inv t l h e x'`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cl") (LABEL_TAC "tk")) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                       `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`;
                       `mm:real^3->bool`; `z:real^3->bool`; `b:real^3->bool`;
                       `x':(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]
               MOI_S3L7_PCS_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "inpcs" o CONJUNCT2) THEN
  UNDISCH_TAC `moi_s33_hd (t:(real^3->bool)->bool) l (h:real^3->real^3) e c` THEN
  REWRITE_TAC[moi_s33_hd] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "pc") (K ALL_TAC))) THEN
  UNDISCH_TAC `moi_s33_inv (t:(real^3->bool)->bool) l (h:real^3->real^3) e x` THEN
  REWRITE_TAC[moi_s33_inv; moi_s33_x2; moi_s33_traces] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "xcr")))))
    (CONJUNCTS_THEN2 (LABEL_TAC "xtr") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`mm:real^3->bool`; `b:real^3->bool`] MOI_S3L7_COMPONENT_REST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier (UNIONS x) SUBSET UNIONS (x:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC MOI_S3D_X_COMPACT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (inside b) (outside (b:real^3->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; INSIDE_INTER_OUTSIDE]; ALL_TAC] THEN
  (* points of the pseudo-cells avoid z; there mm and Bd X agree *)
  SUBGOAL_THEN
   `!u v. ~(u = v) /\ segment[u,v] IN l
          ==> (e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER z = {}`
  (LABEL_TAC "ez") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "inpcs" (MP_TAC o SPEC `segment[u:real^3,v]`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[AFF_DIM_SEGMENT]; ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (z:real^3->bool) (moi_s39_pcs l e)` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s33_inv; moi_s33_x2; moi_s33_traces] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* K' inside the interior *)
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `inside (b:real^3->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN
    ASM_SIMP_TAC[OPEN_INSIDE] THEN SET_TAC[];
    (* inside Int N' *)
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `mm:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mm DIFF z = frontier (UNIONS x) DIFF (z:real^3->bool)` THEN
      UNDISCH_TAC `(z:real^3->bool) SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
      UNDISCH_TAC `frontier (UNIONS x) SUBSET UNIONS (x:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `UNIONS (x:(real^3->bool)->bool) SUBSET
                   interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
      SET_TAC[];
      UNDISCH_TAC `(:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))
                   SUBSET outside b` THEN
      UNDISCH_TAC `DISJOINT (inside b) (outside (b:real^3->bool))` THEN SET_TAC[]];
    (* crossing *)
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`; `y:real^3`] THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    USE_THEN "ez" (MP_TAC o C MP (CONJ (ASSUME `~(u:real^3 = v)`)
      (ASSUME `segment[u:real^3,v] IN l`)) o SPECL [`u:real^3`; `v:real^3`]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN frontier (UNIONS x)` ASSUME_TAC THENL
     [UNDISCH_TAC `mm DIFF z = frontier (UNIONS x) DIFF (z:real^3->bool)` THEN
      UNDISCH_TAC `(b:real^3->bool) SUBSET mm` THEN
      UNDISCH_TAC `(y:real^3) IN b` THEN
      UNDISCH_TAC `(y:real^3) IN (e:(real^3->bool)->real^3->bool) (segment[u,v])` THEN
      UNDISCH_TAC `(e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER z = {}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "cl" MATCH_MP_TAC THEN
    EXISTS_TAC `frontier (UNIONS (x:(real^3->bool)->bool))` THEN
    EXISTS_TAC `(:real^3) DIFF (z UNION (mm DIFF b))` THEN REPEAT CONJ_TAC THENL
     [USE_THEN "xcr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC CLOSED_UNION THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(y:real^3) IN (e:(real^3->bool)->real^3->bool) (segment[u,v])` THEN
      UNDISCH_TAC `(e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER z = {}` THEN
      UNDISCH_TAC `(y:real^3) IN b` THEN SET_TAC[];
      UNDISCH_TAC `mm DIFF z = frontier (UNIONS x) DIFF (z:real^3->bool)` THEN
      UNDISCH_TAC `(b:real^3->bool) SUBSET mm` THEN SET_TAC[]];
    (* traces *)
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    USE_THEN "ez" (MP_TAC o C MP (CONJ (ASSUME `~(u:real^3 = v)`)
      (ASSUME `segment[u:real^3,v] IN l`)) o SPECL [`u:real^3`; `v:real^3`]) THEN
    DISCH_TAC THEN
    USE_THEN "pc" (MP_TAC o C MP (CONJ (ASSUME `~(u:real^3 = v)`)
      (ASSUME `segment[u:real^3,v] IN l`)) o SPECL [`u:real^3`; `v:real^3`]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    USE_THEN "xtr" (MP_TAC o C MP (CONJ (ASSUME `~(u:real^3 = v)`)
      (ASSUME `segment[u:real^3,v] IN l`)) o SPECL [`u:real^3`; `v:real^3`]) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^3->real^3) (midpoint(u,v)) IN
                  (e:(real^3->bool)->real^3->bool) (segment[u,v]) /\
                  h (midpoint(u,v)) IN IMAGE h (UNIONS l)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `e (segment[u,v]) INTER IMAGE (h:real^3->real^3) (UNIONS l) =
                   {h(midpoint(u:real^3,v))}` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "tk" (MP_TAC o SPECL
      [`(e:(real^3->bool)->real^3->bool) (segment[u,v])`; `moi_s33_rim t l h u v`;
       `(h:real^3->real^3) (midpoint(u,v))`;
       `(e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER UNIONS x`;
       `(e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER frontier (UNIONS x)`;
       `mm:real^3->bool`; `b:real^3->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[INTER_SUBSET] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `mm DIFF z = frontier (UNIONS x) DIFF (z:real^3->bool)` THEN
        UNDISCH_TAC `(e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER z = {}` THEN
        SET_TAC[];
        UNDISCH_TAC `mm DIFF z = frontier (UNIONS x) DIFF (z:real^3->bool)` THEN
        UNDISCH_TAC `(e:(real^3->bool)->real^3->bool) (segment[u,v]) INTER z = {}` THEN
        SET_TAC[];
        UNDISCH_TAC `e (segment[u,v]) INTER frontier (IMAGE (h:real^3->real^3)
                       (derived_nbhd t l)) = moi_s33_rim t l h u v` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `UNIONS (x:(real^3->bool)->bool) SUBSET
                     interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
        REWRITE_TAC[frontier] THEN SET_TAC[];
        REWRITE_TAC[IN_DIFF; IN_INTER] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MP_TAC(ISPEC `UNIONS (x:(real^3->bool)->bool)` INTERIOR_SUBSET) THEN
          UNDISCH_TAC `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior (UNIONS x)` THEN
          UNDISCH_TAC `(h:real^3->real^3) (midpoint(u,v)) IN IMAGE h (UNIONS l)` THEN
          SET_TAC[];
          REWRITE_TAC[frontier; IN_DIFF] THEN
          UNDISCH_TAC `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior (UNIONS x)` THEN
          UNDISCH_TAC `(h:real^3->real^3) (midpoint(u,v)) IN IMAGE h (UNIONS l)` THEN
          SET_TAC[]];
        UNDISCH_TAC `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET inside b` THEN
        UNDISCH_TAC `(h:real^3->real^3) (midpoint(u,v)) IN IMAGE h (UNIONS l)` THEN
        SET_TAC[];
        UNDISCH_TAC `e (segment[u,v]) INTER frontier (IMAGE (h:real^3->real^3)
                       (derived_nbhd t l)) = moi_s33_rim t l h u v` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `(:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))
                     SUBSET outside b` THEN
        REWRITE_TAC[frontier] THEN SET_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Part 6: the step for a loop theorem disk missing the pseudo-cells        *)
(* (split, separation, kept piece, fill, invariants, chi) and               *)
(* MOI_S3L7_LTD_STEP_COND, the main theorem with the inputs SPLIT_DISK_R3,  *)
(* PUSH_BODY and the s33_conn lemmas as antecedents.                        *)
(* ========================================================================= *)

let MOI_S3L7_INV_BC3 =
  MP MOI_S3D_INV_BC (CONJ (INST_TYPE [`:3`,`:N`] BOUNDARY_COMPLEX_SURFACE)
                          COMPLEX_BOUNDARY_FRONTIER_3);;

let MOI_S3L7_SPLIT_STEP = prove
 (mk_imp(list_mk_conj [MOI_FND_SPLIT_DISK_R3; MOI_S3L7_CN; `MOISE_302_STATEMENT`;
                       `MOISE_266_STATEMENT`; MOI_S33_TUBE_FACTS],
  `!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c x d.
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_ltd t l h x d /\
     d INTER moi_s39_pcs l e = {}
     ==> ?x'. moi_s33_inv t l h e x' /\
              complex_euler (boundary_complex x) + &1 <=
              complex_euler (boundary_complex x')`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "split") (CONJUNCTS_THEN2 (LABEL_TAC "cn")
    (CONJUNCTS_THEN2 (LABEL_TAC "302") (CONJUNCTS_THEN2 (LABEL_TAC "266")
    (LABEL_TAC "tf"))))) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                       `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`;
                       `d:real^3->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `moi_s33_tube t l (h:real^3->real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_hd t l (h:real^3->real^3) e c` THEN SIMP_TAC[moi_s33_hd];
    ALL_TAC] THEN
  USE_THEN "tf" (fun tf -> MP_TAC(MATCH_MP (MP MOI_S3L7_TUBE_SETS tf)
    (ASSUME `moi_s33_tube t l (h:real^3->real^3)`))) THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                `x:(real^3->bool)->bool`] MOI_S3L7_INV_BC3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `FINITE (x:(real^3->bool)->bool) /\ combinatorial_manifold_with_boundary 3 x /\
    IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior (UNIONS x) /\
    UNIONS x SUBSET interior (IMAGE h (derived_nbhd t l)) /\
    connected (frontier (UNIONS x))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_inv (t:(real^3->bool)->bool) l (h:real^3->real^3) e x` THEN
    REWRITE_TAC[moi_s33_inv; moi_s33_x2] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS (x:(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3D_X_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (frontier (UNIONS x)) (interior (UNIONS (x:(real^3->bool)->bool))) /\
                frontier (UNIONS x) SUBSET UNIONS (x:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[frontier] THEN SET_TAC[];
      MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `x:(real^3->bool)->bool`; `d:real^3->bool`] MOI_S3L7_LTD_CELL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `j:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]
               MOI_S3L7_PCS_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `vv = moi_s33_ww t l (h:real^3->real^3) DIFF moi_s39_pcs l e` THEN
  SUBGOAL_THEN `open (vv:real^3->bool) /\ (d:real^3->bool) SUBSET vv /\
                vv SUBSET moi_s33_ww t l (h:real^3->real^3) /\
                DISJOINT vv (moi_s39_pcs l e)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "vv" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(d:real^3->bool) INTER moi_s39_pcs l e = {}` THEN
      UNDISCH_TAC `(d:real^3->bool) SUBSET moi_s33_ww t l h` THEN SET_TAC[];
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  (* the split *)
  USE_THEN "split" (fun sp -> MP_TAC(SPECL
    [`boundary_complex (x:(real^3->bool)->bool)`; `x:(real^3->bool)->bool`;
     `d:real^3->bool`; `j:real^3->bool`; `vv:real^3->bool`]
    (MP MOI_S3L7_SPLIT_FACTS sp))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3->bool` (X_CHOOSE_THEN `j1:real^3->bool`
    (X_CHOOSE_THEN `j2:real^3->bool` (X_CHOOSE_THEN `d1:real^3->bool`
    (X_CHOOSE_THEN `d2:real^3->bool` (X_CHOOSE_THEN `m':(real^3->bool)->bool`
    (X_CHOOSE_THEN `x'':(real^3->bool)->bool` STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `j1:real^3->bool`] MOI_S3CP_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d2:real^3->bool`; `j2:real^3->bool`] MOI_S3CP_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
    MOI_S3CP_ANNULUS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `UNIONS (m':(real^3->bool)->bool) SUBSET frontier (UNIONS x) UNION vv /\
    UNIONS m' DIFF (a UNION d1 UNION d2) = frontier (UNIONS x) DIFF (a UNION d1 UNION d2) /\
    closed (UNIONS m') /\ compact (UNIONS (x'':(real^3->bool)->bool))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `UNIONS (m':(real^3->bool)->bool) = (UNIONS (boundary_complex (x:(real^3->bool)->bool)) DIFF a) UNION d1 UNION d2` THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(d1:real^3->bool) SUBSET vv` THEN
      UNDISCH_TAC `(d2:real^3->bool) SUBSET vv` THEN SET_TAC[];
      UNDISCH_TAC `UNIONS (m':(real^3->bool)->bool) = (UNIONS (boundary_complex (x:(real^3->bool)->bool)) DIFF a) UNION d1 UNION d2` THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_S3CP_COMPLEX_COMPACT THEN
      EXISTS_TAC `2` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3D_X_COMPACT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the separation of K' from ks *)
  ABBREV_TAC `ks = (:real^3) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
  SUBGOAL_THEN
   `DISJOINT (UNIONS (m':(real^3->bool)->bool)) (IMAGE (h:real^3->real^3) (UNIONS l)) /\
    DISJOINT (UNIONS (m':(real^3->bool)->bool)) ks`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (frontier (UNIONS x)) (interior (UNIONS (x:(real^3->bool)->bool)))` THEN
    UNDISCH_TAC `frontier (UNIONS x) SUBSET UNIONS (x:(real^3->bool)->bool)` THEN
    MP_TAC(ISPEC `UNIONS (x:(real^3->bool)->bool)` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `UNIONS (m':(real^3->bool)->bool) SUBSET frontier (UNIONS x) UNION vv` THEN
    UNDISCH_TAC `(vv:real^3->bool) SUBSET moi_s33_ww t l h` THEN
    UNDISCH_TAC `DISJOINT (moi_s33_ww t l h) (IMAGE (h:real^3->real^3) (UNIONS l))` THEN
    UNDISCH_TAC `DISJOINT (moi_s33_ww t l h) (ks:real^3->bool)` THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior (UNIONS x)` THEN
    UNDISCH_TAC `UNIONS (x:(real^3->bool)->bool) SUBSET
                 interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
    EXPAND_TAC "ks" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `euclidean_separates (UNIONS (m':(real^3->bool)->bool))
      (IMAGE (h:real^3->real^3) (UNIONS l)) ks`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `UNIONS (m':(real^3->bool)->bool) = frontier (UNIONS x'')` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S3L7_SEP_FRONTIER THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET
                    UNIONS (x'':(real^3->bool)->bool)` MP_TAC THENL
       [MP_TAC(ISPEC `UNIONS (x:(real^3->bool)->bool)` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `(UNIONS x DIFF UNIONS x'') UNION (UNIONS x'' DIFF UNIONS x) SUBSET
                     (vv:real^3->bool)` THEN
        UNDISCH_TAC `(vv:real^3->bool) SUBSET moi_s33_ww t l h` THEN
        UNDISCH_TAC `DISJOINT (moi_s33_ww t l h) (IMAGE (h:real^3->real^3) (UNIONS l))` THEN
        UNDISCH_TAC `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior (UNIONS x)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `DISJOINT (UNIONS (m':(real^3->bool)->bool))
                     (IMAGE (h:real^3->real^3) (UNIONS l))` THEN
      UNDISCH_TAC `frontier (UNIONS x'') = UNIONS (m':(real^3->bool)->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPEC `UNIONS (x'':(real^3->bool)->bool)` CLOSURE_SUBSET) THEN
      REWRITE_TAC[frontier] THEN SET_TAC[];
      UNDISCH_TAC `(UNIONS x DIFF UNIONS x'') UNION (UNIONS x'' DIFF UNIONS x) SUBSET
                   (vv:real^3->bool)` THEN
      UNDISCH_TAC `(vv:real^3->bool) SUBSET moi_s33_ww t l h` THEN
      UNDISCH_TAC `DISJOINT (moi_s33_ww t l h) (ks:real^3->bool)` THEN
      UNDISCH_TAC `UNIONS (x:(real^3->bool)->bool) SUBSET
                   interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
      EXPAND_TAC "ks" THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the kept piece *)
  USE_THEN "302" (fun th -> MP_TAC(SPECL
    [`boundary_complex (x:(real^3->bool)->bool)`; `a:real^3->bool`; `j:real^3->bool`;
     `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
     `m':(real^3->bool)->bool`; `IMAGE (h:real^3->real^3) (UNIONS l)`; `ks:real^3->bool`]
    (MP MOI_S3L7_KEPT th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `(a:real^3->bool) SUBSET UNIONS (boundary_complex x) INTER vv` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mb:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `UNIONS (m':(real^3->bool)->bool)`)) THEN
  (* K' inside, ks outside the kept piece *)
  SUBGOAL_THEN `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET inside (UNIONS mb) /\
                ks SUBSET outside (UNIONS (mb:(real^3->bool)->bool))` STRIP_ASSUME_TAC THENL
   [USE_THEN "cn" (MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[MOI_S3CP_SEP_UNIV] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3CP_COMPLEX_COMPACT THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`UNIONS (m':(real^3->bool)->bool)`; `UNIONS (mb:(real^3->bool)->bool)`]
        IN_COMPONENTS_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (UNIONS (m':(real^3->bool)->bool))
                     (IMAGE (h:real^3->real^3) (UNIONS l))` THEN SET_TAC[];
      MP_TAC(ISPECL [`UNIONS (m':(real^3->bool)->bool)`; `UNIONS (mb:(real^3->bool)->bool)`]
        IN_COMPONENTS_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (UNIONS (m':(real^3->bool)->bool)) ks` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the fill *)
  USE_THEN "266" (fun th -> MP_TAC(SPEC `mb:(real^3->bool)->bool`
    (MP MOI_S3L7_FILL th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `connected (UNIONS (mb:(real^3->bool)->bool) UNION inside (UNIONS mb))`
  ASSUME_TAC THENL
   [USE_THEN "cn" (MATCH_MP_TAC o el 3 o CONJUNCTS) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `closed (a UNION d1 UNION d2:real^3->bool) /\
    DISJOINT (a UNION d1 UNION d2:real^3->bool) (moi_s39_pcs l e) /\
    (a UNION d1 UNION d2:real^3->bool) SUBSET
    interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[CLOSED_UNION];
      UNDISCH_TAC `(a:real^3->bool) SUBSET UNIONS (boundary_complex x) INTER vv` THEN
      UNDISCH_TAC `(d1:real^3->bool) SUBSET vv` THEN
      UNDISCH_TAC `(d2:real^3->bool) SUBSET vv` THEN
      UNDISCH_TAC `DISJOINT (vv:real^3->bool) (moi_s39_pcs l e)` THEN SET_TAC[];
      UNDISCH_TAC `(a:real^3->bool) SUBSET UNIONS (boundary_complex x) INTER vv` THEN
      UNDISCH_TAC `(d1:real^3->bool) SUBSET vv` THEN
      UNDISCH_TAC `(d2:real^3->bool) SUBSET vv` THEN
      UNDISCH_TAC `(vv:real^3->bool) SUBSET moi_s33_ww t l h` THEN
      REWRITE_TAC[moi_s33_ww] THEN SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `x':(real^3->bool)->bool` THEN CONJ_TAC THENL
   [USE_THEN "cn" (fun cn -> MATCH_MP_TAC(MP MOI_S3L7_NEW_INV
      (CONJ (el 0 (CONJUNCTS cn)) (el 1 (CONJUNCTS cn))))) THEN
    MAP_EVERY EXISTS_TAC [`c:real^3->real^3->bool`; `x:(real^3->bool)->bool`;
                          `UNIONS (m':(real^3->bool)->bool)`;
                          `a UNION d1 UNION d2:real^3->bool`;
                          `UNIONS (mb:(real^3->bool)->bool)`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `complex_euler (boundary_complex (x:(real^3->bool)->bool)) + &1 <=
                 complex_euler (mb:(real^3->bool)->bool)` THEN
    REAL_ARITH_TAC]);;

let MOI_S3L7_LTD_STEP_COND = prove
 (mk_imp(list_mk_conj [MOI_FND_SPLIT_DISK_R3; MOI_S39_PUSH_BODY; MOI_S3L7_CN],
         MOI_S33_LTD_STEP),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "split") (CONJUNCTS_THEN2 (LABEL_TAC "push")
    (LABEL_TAC "cn"))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "302") (CONJUNCTS_THEN2 (LABEL_TAC "266")
    (LABEL_TAC "tf"))) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                       `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`;
                       `v:real^3`; `d:real^3->bool`] THEN
  STRIP_TAC THEN
  USE_THEN "tf" (fun tf -> USE_THEN "push" (fun pu ->
    MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                  `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                  `x:(real^3->bool)->bool`; `v:real^3`; `d:real^3->bool`]
                 (MP MOI_S3L7_PUSHED (CONJ tf pu))))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d':real^3->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "split" (fun sp -> USE_THEN "cn" (fun cn -> USE_THEN "302" (fun s302 ->
    USE_THEN "266" (fun s266 -> USE_THEN "tf" (fun tf ->
      MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                    `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                    `x:(real^3->bool)->bool`; `d':real^3->bool`]
        (MP MOI_S3L7_SPLIT_STEP (CONJ sp (CONJ cn (CONJ s302 (CONJ s266 tf))))))))))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

(* ========================================================================= *)
(* Part 7: MOI_FND_SPLIT_DISK_R3 (pc_moi_fnd_split) is SPLIT_SURFACE_DISK_3 *)
(* with its two antecedents (DERIVED_NBHD_BALL_2 of pc_moi_fnd_rnb2; the    *)
(* trace annulus of pc_moi_fnd_sptrace from DERIVED_NBHD_POLYGON_2 at N =   *)
(* 3).  This leaves PUSH_BODY and the four s33_conn statements as           *)
(* antecedents (MOI_S3L7_LTD_STEP_PUSH).                                    *)
(* ========================================================================= *)

let MOI_S3L7_SPLIT_DISK =
  MP SPLIT_SURFACE_DISK_3
     (CONJ DERIVED_NBHD_BALL_2
           (MP MOI_FSTR_SPLIT_TRACE_COND (INST_TYPE [`:3`,`:N`] DERIVED_NBHD_POLYGON_2)));;

let MOI_S3L7_LTD_STEP_PUSH = prove
 (mk_imp(mk_conj(MOI_S39_PUSH_BODY, MOI_S3L7_CN), MOI_S33_LTD_STEP),
  DISCH_THEN(fun th ->
    ACCEPT_TAC(MP MOI_S3L7_LTD_STEP_COND (CONJ MOI_S3L7_SPLIT_DISK th))));;

(* ========================================================================= *)
(* Part 8: the four lemmas of pc_moi_s33_conn are theorems; their           *)
(* conjunction is MOI_S3L7_CN (MP checks the statement up to alpha          *)
(* conversion), which leaves MOI_S39_PUSH_BODY (pc_moi_s33_push) as the     *)
(* only antecedent (MOI_S3L7_LTD_STEP_PB).                                  *)
(* ========================================================================= *)

let MOI_S3L7_CN_THM =
  end_itlist CONJ [MOI_S3CN_CROSSING_LOCAL; MOI_S3CN_TRACE_KEEP;
                   MOI_S3CN_SEP_INSIDE; MOI_S3CN_INSIDE_UNION_CONNECTED];;

let MOI_S3L7_LTD_STEP_PB = prove
 (mk_imp(MOI_S39_PUSH_BODY, MOI_S33_LTD_STEP),
  DISCH_THEN(fun th ->
    ACCEPT_TAC(MP MOI_S3L7_LTD_STEP_PUSH (CONJ th MOI_S3L7_CN_THM))));;

(* ========================================================================= *)
(* Part 9: the theorem LTD_STEP.  S39_PUSH : |- MOI_S39_PUSH_BODY of        *)
(* pc_moi_s33_push discharges the last antecedent of MOI_S3L7_LTD_STEP_PB.  *)
(* ========================================================================= *)

let LTD_STEP = prove
 (MOI_S33_LTD_STEP,
  ACCEPT_TAC(MP MOI_S3L7_LTD_STEP_PB S39_PUSH));;


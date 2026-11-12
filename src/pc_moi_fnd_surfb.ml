needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_surfb0.ml";;
needs "src/pc_moi_fnd_surfa.ml";;
needs "src/pc_moi_fnd_euler.ml";;
needs "src/pc_moi_real.ml";;
needs "src/pc_moi_pl1m.ml";;
needs "src/pc_moi_s28_trib.ml";;
needs "src/pc_moi_s35_minc.ml";;
needs "src/pc_moi_sch3_amb2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_fnd_surfb: foundations of the Moise PL core, planar surfaces      *)
(* (Moise, Geometric Topology in Dimensions 2 and 3, GTM 47, Sec 22,        *)
(* pp.150 and 161).  Main theorem (the statement term                        *)
(* MOI_FND_SURFACE_PLANAR of pc_moi_fnd_stmt.ml):                            *)
(*   SURFACE_EULER_PLANAR: a finite connected nonempty combinatorial        *)
(*   2-manifold with boundary has finitely many boundary circles, chi + b   *)
(*   is at most 2, and when b = k + 1 and chi = 1 - k it is PL homeomorphic *)
(*   to holed_disk_model k with the model frontier on its boundary.         *)
(* Route: the boundary is a disjoint union of PL circles; the circles are   *)
(* capped abstractly (one apex each); MOI_FSA_COUNT on the capped closed    *)
(* abstract surface gives chi + b <= 2; in the equality case the capped     *)
(* surface is realized in real^5, the surface with all caps but one is a PL *)
(* disk (MOI_FSA_DISK_PIECE) with the other caps disjoint PL disks inside   *)
(* it, and a planar holed-disk theorem (disk moves in the plane) gives the  *)
(* model.  The boundary circles (MOI_FSB_BD_DEGREE, MOI_FSB_BD_CIRCLES) and *)
(* the chart facts (MOI_FSB_SC_CHARTS, MOI_FSB_DIM, MOI_FSB_PURE,           *)
(* MOI_FSB_VTRI) are in pc_moi_fnd_surfb0.                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The abstract surface (vertex sets of the triangles, moi_fsa_abs          *)
(* of pc_moi_fnd_surfa) of a finite combinatorial 2-manifold with boundary: *)
(* edges, counts and complex_euler c = V - E + F.  The proofs are those of  *)
(* MOI_FSA_ABS_EDGE, MOI_FSA_ABS_COUNTS and MOI_FSA_CM_EULER for closed      *)
(* surfaces, with purity and the dimension bound taken from the charts      *)
(* (MOI_FSB_PURE, MOI_FSB_DIM of pc_moi_fnd_surfb0).                        *)
(* ------------------------------------------------------------------------- *)

let MOI_FSB_ABS_EDGE = prove
 (`!c e:real^N->bool.
        FINITE c /\ combinatorial_manifold_with_boundary 2 c
        ==> (e IN moi_fsa_edges (moi_fsa_abs c) <=>
             ?E. E IN c /\ aff_dim E = &1 /\ e = moi_fsa_vs E)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_edges; moi_fsa_abs; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t':real^N->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC))) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `convex hull (e:real^N->bool)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    SUBGOAL_THEN `~affine_dependent (e:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
    UNDISCH_TAC `(e:real^N->bool) HAS_SIZE 2` THEN SIMP_TAC[HAS_SIZE] THEN
    STRIP_TAC THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`; `1`]
        MOI_FSA_VS_SIZE) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?tr:real^N->bool. tr IN c /\ aff_dim tr = &2 /\ E SUBSET tr`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FSB_PURE THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `moi_fsa_vs (tr:real^N->bool)` THEN CONJ_TAC THENL
     [EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`] MOI_FSA_VS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `{x:real^N} IN c` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tr:real^N->bool`; `x:real^N`]
      MOI_FSA_VS_MEM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(E:real^N->bool) SUBSET tr` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[extreme_point_of; moi_fsa_vs;
      IN_ELIM_THM]);;

let MOI_FSB_ABS_NTRI = prove
 (`!c e:real^N->bool.
        FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
        e IN moi_fsa_edges (moi_fsa_abs c)
        ==> ?E. E IN c /\ aff_dim E = &1 /\ e = moi_fsa_vs E /\
                CARD {t | t IN moi_fsa_abs c /\ e SUBSET t} =
                CARD {tr | tr IN c /\ aff_dim tr = &2 /\ E SUBSET tr}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSB_ABS_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `E:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `{t | t IN moi_fsa_abs c /\ moi_fsa_vs E SUBSET t} =
    IMAGE moi_fsa_vs {tr:real^N->bool | tr IN c /\ aff_dim tr = &2 /\ E SUBSET tr}`
  SUBST1_TAC THENL
   [REWRITE_TAC[MOI_FSA_ABS_IMAGE] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `t:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `tr:real^N->bool`
        STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`;
                     `tr:real^N->bool`] MOI_FSA_ABS_SUB) THEN
      ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`;
                       `tr:real^N->bool`] MOI_FSA_ABS_SUB) THEN
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fsa_vs:(real^N->bool)->real^N->bool`;
                 `{tr:real^N->bool | tr IN c /\ aff_dim tr = &2 /\ E SUBSET tr}`]
    CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MOI_FSA_VS_INJ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[]);;

let MOI_FSB_ABS_COUNTS = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold_with_boundary 2 c
        ==> UNIONS (moi_fsa_abs c) = {v | {v} IN c} /\
            CARD (moi_fsa_abs c) = CARD {t | t IN c /\ aff_dim t = &2} /\
            CARD (moi_fsa_edges (moi_fsa_abs c)) =
            CARD {e | e IN c /\ aff_dim e = &1}`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[MOI_FSA_ABS_IMAGE; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_FSB_VTRI) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `x:real^N`]
        MOI_FSA_VS_MEM) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    REWRITE_TAC[MOI_FSA_ABS_IMAGE] THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSA_VS_INJ THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `moi_fsa_edges (moi_fsa_abs c) =
                  IMAGE moi_fsa_vs {e:real^N->bool | e IN c /\ aff_dim e = &1}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
      ASM_SIMP_TAC[MOI_FSB_ABS_EDGE] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      MESON_TAC[];
      MATCH_MP_TAC CARD_IMAGE_INJ THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSA_VS_INJ THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]]);;

let MOI_FSB_EULER = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold_with_boundary 2 c
        ==> complex_euler c =
            &(CARD {v | {v} IN c}) - &(CARD {e | e IN c /\ aff_dim e = &1}) +
            &(CARD {t | t IN c /\ aff_dim t = &2})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN c /\ ~(s = {})} =
    ({s | s IN c /\ aff_dim s = &0} UNION {e | e IN c /\ aff_dim e = &1}) UNION
    {t | t IN c /\ aff_dim t = &2}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
    ASM_CASES_TAC `(s:real^N->bool) IN c` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FSB_DIM) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THENL
     [CONV_TAC INT_REDUCE_CONV;
      MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN ASM_REWRITE_TAC[] THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT {s:real^N->bool | s IN c /\ aff_dim s = &0}
             {e | e IN c /\ aff_dim e = &1} /\
    DISJOINT ({s:real^N->bool | s IN c /\ aff_dim s = &0} UNION
              {e | e IN c /\ aff_dim e = &1})
             {t | t IN c /\ aff_dim t = &2}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN
    CONJ_TAC THEN X_GEN_TAC `s:real^N->bool` THEN
    ASM_CASES_TAC `aff_dim(s:real^N->bool) = &0` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `aff_dim(s:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION; FINITE_RESTRICT; FINITE_UNION] THEN
  SUBGOAL_THEN
   `sum {s:real^N->bool | s IN c /\ aff_dim s = &0}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {s:real^N->bool | s IN c /\ aff_dim s = &0} (\s. &1) /\
    sum {e:real^N->bool | e IN c /\ aff_dim e = &1}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {e:real^N->bool | e IN c /\ aff_dim e = &1} (\s. -- &1) /\
    sum {t:real^N->bool | t IN c /\ aff_dim t = &2}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {t:real^N->bool | t IN c /\ aff_dim t = &2} (\s. &1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; NUM_OF_INT_OF_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN c /\ aff_dim s = &0} =
    IMAGE (\u:real^N. {u}) {u | {u} IN c}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; AFF_DIM_EQ_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {u:real^N | {u} IN c}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:real^N. {u}`; `{u:real^N | {u} IN c}`] CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RNEG; GSYM real_sub]);;

(* ------------------------------------------------------------------------- *)
(* Local and dual connectivity of the abstract surface of a                 *)
(* finite connected combinatorial 2-manifold with boundary (adapted copies  *)
(* of MOI_FSA_ABS_SURF (lconn part), MOI_FSA_ABS_GEOM, MOI_FSA_ABS_POLY,     *)
(* MOI_FSA_GEOM_MEET and MOI_FSA_GEOM_DCONN of pc_moi_fnd_surfa, whose      *)
(* closedness hypothesis is used only for lconn and the triangle sizes).     *)
(* ------------------------------------------------------------------------- *)

(* Local connectivity of the triangles at a vertex (the form of            *)
(* MOI_FSA_CM_LCONN), from MOI_S8TB_VERTEX_CONNECTED with the charts.       *)

let MOI_FSB_LCONN = prove
 (`!c (v:real^N) Y.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ {v} IN c /\
     Y SUBSET {t | t IN c /\ aff_dim t = &2 /\ v IN t} /\ ~(Y = {}) /\
     (!t t' u. t IN Y /\ t' IN c /\ aff_dim t' = &2 /\ v IN t' /\
               ~(u = v) /\ {u} IN c /\ u IN t /\ u IN t'
               ==> t' IN Y)
     ==> Y = {t | t IN c /\ aff_dim t = &2 /\ v IN t}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast cs) THEN LABEL_TAC "YC" (last cs)) THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSB_SC_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH")) THEN
  MATCH_MP_TAC MOI_S8TB_VERTEX_CONNECTED THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSB_PURE THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TB_PUNCT THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "CH" MATCH_MP_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `t':real^N->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(t:real^N->bool) IN c` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^N) IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(t INTER t':real^N->bool) IN c` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[combinatorial_manifold_with_boundary];
        UNDISCH_TAC `simplicial_complex (c:(real^N->bool)->bool)` THEN
        REWRITE_TAC[simplicial_complex] THEN
        DISCH_THEN(MP_TAC o SPECL [`t:real^N->bool`; `t':real^N->bool`] o el 3 o CONJUNCTS) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t INTER t':real^N->bool`; `v:real^N`]
      MOI_FSB_EDGE_AT) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
    USE_THEN "YC" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `u:real^N`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(u:real^N) IN t INTER t'` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN SET_TAC[];
      SET_TAC[]]]);;

(* The abstract surface of c is locally connected at every point (the     *)
(* lconn part of MOI_FSA_ABS_SURF with MOI_FSB_LCONN).                       *)

let MOI_FSB_ABS_LCONN = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold_with_boundary 2 c
        ==> !x. moi_fsa_lconn (moi_fsa_abs c) x`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `{x:real^N} IN c` THENL
   [ALL_TAC;
    MATCH_MP_TAC MOI_FSA_LCONN_EMPTY THEN
    REWRITE_TAC[MOI_FSA_ABS_IMAGE; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]] THEN
  REWRITE_TAC[moi_fsa_lconn] THEN X_GEN_TAC `y:(real^N->bool)->bool` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!tr:real^N->bool. tr IN c ==> ((x:real^N) IN tr <=> x IN moi_fsa_vs tr)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSA_VS_MEM THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`;
                 `{tr:real^N->bool | tr IN c /\ aff_dim tr = &2 /\
                                     moi_fsa_vs tr IN y}`] MOI_FSB_LCONN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `tr:real^N->bool` THEN
      STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `y SUBSET {t | t IN moi_fsa_abs c /\ (x:real^N) IN t}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      UNDISCH_TAC `~(y:(real^N->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `t0:real^N->bool`) THEN
      SUBGOAL_THEN `(t0:real^N->bool) IN moi_fsa_abs c` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MOI_FSA_ABS_IMAGE; IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`t1:real^N->bool`; `t2:real^N->bool`; `u:real^N`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_fsa_lclosed (moi_fsa_abs c) (x:real^N) y` THEN
      REWRITE_TAC[moi_fsa_lclosed] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`moi_fsa_vs (t1:real^N->bool)`; `u:real^N`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(u:real^N) IN moi_fsa_vs t1 /\ u IN moi_fsa_vs t2 /\
                    (x:real^N) IN moi_fsa_vs t2`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t1:real^N->bool`; `u:real^N`]
            MOI_FSA_VS_MEM);
          MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t2:real^N->bool`; `u:real^N`]
            MOI_FSA_VS_MEM);
          MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t2:real^N->bool`; `x:real^N`]
            MOI_FSA_VS_MEM)] THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[MOI_FSA_ABS_IMAGE; IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `t2:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; MOI_FSA_ABS_IMAGE; IN_IMAGE] THEN
  X_GEN_TAC `t':real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `tr:real^N->bool`
    STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `t':real^N->bool`)) THEN
  UNDISCH_TAC `{tr:real^N->bool | tr IN c /\ aff_dim tr = &2 /\
                                  moi_fsa_vs tr IN y} =
               {t | t IN c /\ aff_dim t = &2 /\ x IN t}` THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `tr:real^N->bool`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_FSB_ABS_GEOM = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold_with_boundary 2 c ==> moi_fsa_geom (moi_fsa_abs c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_geom; MOI_FSA_ABS_IMAGE; FORALL_IN_IMAGE;
              EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s':real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t':real^N->bool`] MOI_FSA_VS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent (s:real^N->bool) /\ ~affine_dependent (s':real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (s:real^N->bool) IN c /\ convex hull (s':real^N->bool) IN c`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN
    SET_TAC[]] THEN
  SUBGOAL_THEN `(convex hull s INTER convex hull s':real^N->bool) face_of convex hull s /\
                (convex hull s INTER convex hull s') face_of convex hull s'`
  MP_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `A:real^N->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `B:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `A:real^N->bool = B` ASSUME_TAC THENL
   [SUBGOAL_THEN `~affine_dependent (A:real^N->bool) /\ ~affine_dependent (B:real^N->bool)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPEC `A:real^N->bool` MOI_FSA_VS_HULL) THEN
    MP_TAC(ISPEC `B:real^N->bool` MOI_FSA_VS_HULL) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `A:real^N->bool`)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]);;

let MOI_FSB_ABS_POLY = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold_with_boundary 2 c
        ==> moi_fsa_poly (moi_fsa_abs c) = UNIONS c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_poly; MOI_FSA_ABS_IMAGE] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; EXISTS_IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `t:real^N->bool` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FSB_PURE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^N->bool` THEN CONJ_TAC THENL
     [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ASM SET_TAC[]]]);;

let MOI_FSB_GEOM_MEET = prove
 (`!d y t1 t2 (x:real^N).
        FINITE d /\ (!t. t IN d ==> t HAS_SIZE 3) /\ (!z. moi_fsa_lconn d z) /\ moi_fsa_geom d /\ y SUBSET d /\
        moi_fsa_dclosed d y /\ t1 IN y /\ t2 IN d /\
        x IN convex hull t1 /\ x IN convex hull t2
        ==> t2 IN y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t1:real^N->bool) IN d` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull t1 INTER convex hull t2:real^N->bool =
                convex hull (t1 INTER t2)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fsa_geom (d:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_fsa_geom] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    CONJ_TAC THENL
     [EXISTS_TAC `t1:real^N->bool`; EXISTS_TAC `t2:real^N->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^N. w IN t1 /\ w IN t2` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `t1 INTER t2:real^N->bool = {}` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `convex hull t1 INTER convex hull t2:real^N->bool =
                 convex hull (t1 INTER t2)` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsa_lconn d (w:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `t1:real^N->bool`]
    MOI_FSA_LCONN_DCOMP) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `t1:real^N->bool`] MOI_FSA_DCOMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:(real^N->bool)->bool` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_FSB_GEOM_DCONN = prove
 (`!d:(real^N->bool)->bool.
        FINITE d /\ (!t. t IN d ==> t HAS_SIZE 3) /\ (!z. moi_fsa_lconn d z) /\ moi_fsa_geom d /\ connected (moi_fsa_poly d)
        ==> moi_fsa_dconn d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_FSA_DCONN_ALT] THEN
  X_GEN_TAC `y:(real^N->bool)->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE (d:(real^N->bool)->bool) /\
                (!t:real^N->bool. t IN d ==> FINITE t) /\
                (!t:real^N->bool. t IN d ==> ~(t = {}))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!t:real^N->bool. t HAS_SIZE 3 ==> FINITE t /\ ~(t = {})`
      (fun th -> ASM_MESON_TAC[th]) THEN
    GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `CARD({}:real^N->bool) = 3` THEN
    REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `connected (moi_fsa_poly (d:(real^N->bool)->bool))` THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC [`moi_fsa_poly (y:(real^N->bool)->bool)`;
                        `moi_fsa_poly ((d:(real^N->bool)->bool) DIFF y)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_FSA_POLY_COMPACT THEN
    ASM_MESON_TAC[FINITE_SUBSET; SUBSET];
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_FSA_POLY_COMPACT THEN
    ASM_SIMP_TAC[FINITE_DIFF; IN_DIFF];
    REWRITE_TAC[GSYM MOI_FSA_POLY_UNION] THEN
    SUBGOAL_THEN `(y:(real^N->bool)->bool) UNION (d DIFF y) = d`
     (fun th -> REWRITE_TAC[th; SUBSET_REFL]) THEN
    ASM SET_TAC[];
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[moi_fsa_poly; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `k1:real^N->bool` (CONJUNCTS_THEN2
         (X_CHOOSE_THEN `t1:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `k2:real^N->bool` (CONJUNCTS_THEN2
           (X_CHOOSE_THEN `t2:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))
        (K ALL_TAC))) THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `y:(real^N->bool)->bool`;
                   `t1:real^N->bool`; `t2:real^N->bool`; `x:real^N`]
      MOI_FSB_GEOM_MEET) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(t2:real^N->bool) IN d DIFF y` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_FSA_POLY_MEET_NE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FSA_POLY_MEET_NE THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[]]);;

let MOI_FSB_ABS_DCONN = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ connected (UNIONS c)
        ==> moi_fsa_dconn (moi_fsa_abs c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSB_GEOM_DCONN THEN
  ASM_SIMP_TAC[MOI_FSB_ABS_LCONN; MOI_FSB_ABS_GEOM; MOI_FSB_ABS_POLY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MOI_FSA_ABS_IMAGE] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
    REWRITE_TAC[MOI_FSA_ABS_IMAGE; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `2`]
      MOI_FSA_VS_SIZE) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The capped abstract surface over real^N + (real^N->bool): the            *)
(* triangles of c (vertices INL x) and, for each boundary circle J in a     *)
(* chosen set js of boundary circles, the cone triangles over its edges     *)
(* with the apex INR J.  All circles: a closed surface; all but one: a disk *)
(* piece.                                                                    *)
(* ------------------------------------------------------------------------- *)

let moi_fsb_bedges = new_definition
 `moi_fsb_bedges (c:(real^N->bool)->bool) =
    {e | e IN c /\ aff_dim e = &1 /\
         CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 1}`;;

let moi_fsb_cones = new_definition
 `moi_fsb_cones (c:(real^N->bool)->bool) (js:(real^N->bool)->bool) =
    {(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs e) |
     J IN js /\ e IN moi_fsb_bedges c /\ e SUBSET J}`;;

let moi_fsb_cap = new_definition
 `moi_fsb_cap (c:(real^N->bool)->bool) (js:(real^N->bool)->bool) =
    IMAGE (IMAGE (INL:real^N->real^N+(real^N->bool))) (moi_fsa_abs c) UNION
    moi_fsb_cones c js`;;

(* Boundary edges: in surface_boundary, each inside exactly one boundary     *)
(* circle, finitely many.                                                    *)

let MOI_FSB_BEDGE_COMPONENT = prove
 (`!c e:real^N->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ e IN moi_fsb_bedges c
     ==> e SUBSET surface_boundary c /\
         ?!J. J IN components (surface_boundary c) /\ e SUBSET J`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsb_bedges; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(e:real^N->bool) SUBSET surface_boundary c` ASSUME_TAC THENL
   [REWRITE_TAC[surface_boundary] THEN MATCH_MP_TAC(SET_RULE
      `!x:real^N->bool f. x IN f ==> x SUBSET UNIONS f`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `connected (e:real^N->bool) /\ ~(e = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[combinatorial_manifold_with_boundary];
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `e:real^N->bool`]
      EXISTS_COMPONENT_SUPERSET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`J1:real^N->bool`; `J2:real^N->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `J1:real^N->bool`;
                   `J2:real^N->bool`] COMPONENTS_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[]]);;

(* The capped surface is a finite set of 3-element vertex sets. *)

let MOI_FSB_CAP_BASIC = prove
 (`!c js:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c)
     ==> FINITE (moi_fsb_cap c js) /\ (!t. t IN moi_fsb_cap c js ==> t HAS_SIZE 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^N. (INL x:real^N+(real^N->bool)) = INL y <=> x = y`
  ASSUME_TAC THENL [REWRITE_TAC[injectivity "sum"]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_fsb_cap; FINITE_UNION] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[MOI_FSA_ABS_IMAGE] THEN
      MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\(J,e). (INR J:real^N+(real^N->bool)) INSERT
                                 IMAGE INL (moi_fsa_vs (e:real^N->bool)))
                        (components (surface_boundary c) CROSS moi_fsb_bedges c)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_CROSS THEN
        ASM_SIMP_TAC[MOI_FSB_BD_CIRCLES] THEN REWRITE_TAC[moi_fsb_bedges] THEN
        MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[moi_fsb_cones; SUBSET; IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM;
                    IN_CROSS] THEN
        X_GEN_TAC `t:real^N+(real^N->bool)->bool` THEN
        DISCH_THEN(X_CHOOSE_THEN `J:real^N->bool` (X_CHOOSE_THEN `e:real^N->bool`
          STRIP_ASSUME_TAC)) THEN
        MAP_EVERY EXISTS_TAC [`J:real^N->bool`; `e:real^N->bool`] THEN
        CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[]]];
    REWRITE_TAC[moi_fsb_cap; IN_UNION; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
                FORALL_AND_THM; FORALL_IN_IMAGE; MOI_FSA_ABS_IMAGE; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `2`] MOI_FSA_VS_SIZE) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
      REWRITE_TAC[moi_fsb_cones; IN_ELIM_THM; moi_fsb_bedges] THEN
      X_GEN_TAC `t:real^N+(real^N->bool)->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `J:real^N->bool` (X_CHOOSE_THEN `e:real^N->bool`
        STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `1`] MOI_FSA_VS_SIZE) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
      SUBGOAL_THEN `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs e) HAS_SIZE 2`
      MP_TAC THENL
       [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_INSERT] THEN
      REWRITE_TAC[IN_IMAGE; distinctness "sum"] THEN CONV_TAC NUM_REDUCE_CONV]]);;

(* INL and INR on vertex sets. *)

let MOI_FSB_INL_IMAGE = prove
 (`(!s t:real^N->bool.
      IMAGE (INL:real^N->real^N+(real^N->bool)) s SUBSET IMAGE INL t <=> s SUBSET t) /\
   (!s t:real^N->bool.
      IMAGE (INL:real^N->real^N+(real^N->bool)) s = IMAGE INL t <=> s = t) /\
   (!s (J:real^N->bool). ~((INR J:real^N+(real^N->bool)) IN IMAGE INL s)) /\
   (!s (x:real^N). (INL x:real^N+(real^N->bool)) IN IMAGE INL s <=> x IN s)`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE; injectivity "sum"] THEN MESON_TAC[];
    MP_TAC(ISPEC `INL:real^N->real^N+(real^N->bool)` INJECTIVE_IMAGE) THEN
    REWRITE_TAC[injectivity "sum"] THEN MESON_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[distinctness "sum"];
    REWRITE_TAC[IN_IMAGE; injectivity "sum"] THEN MESON_TAC[]]);;

(* The capped triangles through an edge IMAGE INL (vs E) of c: its one or   *)
(* two triangles of c, plus the cone over E when E is a boundary edge.       *)

let MOI_FSB_CAP_EDGE_OLD = prove
 (`!c js E:real^N->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c) /\ E IN c /\ aff_dim E = &1
     ==> CARD {t | t IN moi_fsb_cap c js /\
                   IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs E) SUBSET t} =
         (if E IN moi_fsb_bedges c /\ ~(?J. J IN js /\ E SUBSET J) then 1 else 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSB_SC_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH")) THEN
  ABBREV_TAC `TE = {tr:real^N->bool | tr IN c /\ aff_dim tr = &2 /\ E SUBSET tr}` THEN
  SUBGOAL_THEN `FINITE (TE:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "TE" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD (TE:(real^N->bool)->bool) = 1 \/ CARD TE = 2` ASSUME_TAC THENL
   [EXPAND_TAC "TE" THEN MATCH_MP_TAC MOI_S8TB_EDGE_CARD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the edges of c inside an edge E are E itself *)
  SUBGOAL_THEN `!E':real^N->bool. E' IN c /\ aff_dim E' = &1 /\ E SUBSET E' ==> E' = E`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`E:real^N->bool`; `E':real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `convex (E':real^N->bool) /\ E face_of E'` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[combinatorial_manifold_with_boundary];
        UNDISCH_TAC `simplicial_complex (c:(real^N->bool)->bool)` THEN
        REWRITE_TAC[simplicial_complex] THEN
        DISCH_THEN(MP_TAC o SPECL [`E:real^N->bool`; `E':real^N->bool`] o el 3 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(E:real^N->bool) INTER E' = E` (fun th -> SIMP_TAC[th]) THEN
        ASM SET_TAC[]];
      INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{t | t IN moi_fsb_cap c js /\
         IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs E) SUBSET t} =
    IMAGE (\tr. IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)) TE UNION
    {(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs E) | J |
     J IN js /\ E IN moi_fsb_bedges c /\ E SUBSET J}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N+(real^N->bool)->bool` THEN
    REWRITE_TAC[moi_fsb_cap; moi_fsb_cones; MOI_FSA_ABS_IMAGE; IN_UNION; IN_IMAGE;
                IN_ELIM_THM] THEN
    EXPAND_TAC "TE" THEN REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN STRIP_TAC THENL
       [DISJ1_TAC THEN EXISTS_TAC `x':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs E) SUBSET t` THEN
        ASM_REWRITE_TAC[MOI_FSB_INL_IMAGE] THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`; `x':real^N->bool`]
          MOI_FSA_ABS_SUB) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        DISJ2_TAC THEN EXISTS_TAC `J:real^N->bool` THEN
        SUBGOAL_THEN `(e:real^N->bool) = E` SUBST_ALL_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN
          UNDISCH_TAC `(e:real^N->bool) IN moi_fsb_bedges c` THEN
          REWRITE_TAC[moi_fsb_bedges; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs E) SUBSET t` THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[SET_RULE `!s t a:real^N+(real^N->bool).
                         s SUBSET a INSERT t <=> s DELETE a SUBSET t`] THEN
          SUBGOAL_THEN `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs E) DELETE INR J =
                        IMAGE INL (moi_fsa_vs E)` SUBST1_TAC THENL
           [REWRITE_TAC[SET_RULE `!s a:real^N+(real^N->bool). s DELETE a = s <=> ~(a IN s)`;
                        MOI_FSB_INL_IMAGE];
            ALL_TAC] THEN
          REWRITE_TAC[MOI_FSB_INL_IMAGE] THEN
          MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`; `e:real^N->bool`]
            MOI_FSA_ABS_SUB) THEN
          ASM_REWRITE_TAC[] THEN SIMP_TAC[];
          ASM_REWRITE_TAC[]]];
      STRIP_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [DISJ1_TAC THEN EXISTS_TAC `moi_fsa_vs (x:real^N->bool)` THEN
          REWRITE_TAC[] THEN EXISTS_TAC `x:real^N->bool` THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[MOI_FSB_INL_IMAGE] THEN
          MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`; `x:real^N->bool`]
            MOI_FSA_ABS_SUB) THEN
          ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`J:real^N->bool`; `E:real^N->bool`] THEN
          ASM_REWRITE_TAC[];
          SET_TAC[]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD (IMAGE (\tr. IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)) TE) =
    CARD (TE:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[MOI_FSB_INL_IMAGE] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N->bool`; `y:real^N->bool`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FSA_VS_INJ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N->bool) IN TE` THEN UNDISCH_TAC `(y:real^N->bool) IN TE` THEN
    EXPAND_TAC "TE" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE (IMAGE (\tr. IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)) TE)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FINITE_IMAGE]; ALL_TAC] THEN
  ASM_CASES_TAC `(E:real^N->bool) IN moi_fsb_bedges c` THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `{(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs E) | J |
       J IN js /\ E IN moi_fsb_bedges c /\ E SUBSET J} = {}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[UNION_EMPTY] THEN
    UNDISCH_TAC `CARD (TE:(real^N->bool)->bool) = 1 \/ CARD TE = 2` THEN
    MATCH_MP_TAC(TAUT `~p ==> (p \/ q ==> q)`) THEN
    UNDISCH_TAC `~((E:real^N->bool) IN moi_fsb_bedges c)` THEN
    EXPAND_TAC "TE" THEN REWRITE_TAC[moi_fsb_bedges; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`] MOI_FSB_BEDGE_COMPONENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[EXISTS_UNIQUE_THM]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `J0:real^N->bool` STRIP_ASSUME_TAC) (LABEL_TAC "UJ"))) THEN
  SUBGOAL_THEN `!J:real^N->bool. J IN js /\ E SUBSET J ==> J = J0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "UJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (TE:(real^N->bool)->bool) = 1` ASSUME_TAC THENL
   [EXPAND_TAC "TE" THEN UNDISCH_TAC `(E:real^N->bool) IN moi_fsb_bedges c` THEN
    REWRITE_TAC[moi_fsb_bedges; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(J0:real^N->bool) IN js` THENL
   [SUBGOAL_THEN `?J:real^N->bool. J IN js /\ E SUBSET J` (fun th -> REWRITE_TAC[th]) THENL
     [EXISTS_TAC `J0:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `{(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs E) | J |
       J IN js /\ E IN moi_fsb_bedges c /\ E SUBSET J} =
      {INR J0 INSERT IMAGE INL (moi_fsa_vs E)}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `t:real^N+(real^N->bool)->bool` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `J:real^N->bool` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `J:real^N->bool = J0` SUBST_ALL_TAC THENL
         [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
        DISCH_TAC THEN EXISTS_TAC `J0:real^N->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[SET_RULE `!s a:real^N+(real^N->bool)->bool. s UNION {a} = a INSERT s`] THEN
    SIMP_TAC[CARD_CLAUSES; ASSUME
     `FINITE (IMAGE (\tr. IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)) TE)`] THEN
    SUBGOAL_THEN
     `~((INR J0:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs E) IN
        IMAGE (\tr. IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)) TE)`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` MP_TAC) THEN
      DISCH_THEN(MP_TAC o AP_TERM `\s. (INR J0:real^N+(real^N->bool)) IN s` o CONJUNCT1) THEN
      REWRITE_TAC[IN_INSERT; MOI_FSB_INL_IMAGE];
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    SUBGOAL_THEN `~(?J:real^N->bool. J IN js /\ E SUBSET J)` (fun th -> REWRITE_TAC[th]) THENL
     [STRIP_TAC THEN UNDISCH_TAC `~((J0:real^N->bool) IN js)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `J:real^N->bool = J0` (SUBST1_TAC o SYM) THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs E) | J |
       J IN js /\ E IN moi_fsb_bedges c /\ E SUBSET J} = {}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `t:real^N+(real^N->bool)->bool` THEN STRIP_TAC THEN
      UNDISCH_TAC `~((J0:real^N->bool) IN js)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `J:real^N->bool = J0` (SUBST1_TAC o SYM) THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[UNION_EMPTY]]);;

(* Boundary edges: basic facts. *)

let MOI_FSB_SB_UNIONS = prove
 (`!c:(real^N->bool)->bool. surface_boundary c = UNIONS (moi_fsb_bedges c)`,
  REWRITE_TAC[surface_boundary; moi_fsb_bedges]);;

let MOI_FSB_BEDGE_IN = prove
 (`!c e:real^N->bool. e IN moi_fsb_bedges c ==> e IN c /\ aff_dim e = &1`,
  SIMP_TAC[moi_fsb_bedges; IN_ELIM_THM]);;

let MOI_FSB_BEDGE_VS_IFF = prove
 (`!c e (x:real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ e IN moi_fsb_bedges c
     ==> (x IN moi_fsa_vs e <=> {x} IN c /\ x IN e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_BEDGE_IN]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `{x:real^N} IN c` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSA_VS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N` o el 4 o CONJUNCTS) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `x:real^N`] MOI_FSA_VS_MEM) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `x:real^N`] MOI_FSA_VS_MEM) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let MOI_FSB_BEDGE_BASIC = prove
 (`!c e:real^N->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ e IN moi_fsb_bedges c
     ==> e IN c /\ aff_dim e = &1 /\ moi_fsa_vs e HAS_SIZE 2 /\
         e SUBSET surface_boundary c /\
         ?tr. tr IN c /\ aff_dim tr = &2 /\ e SUBSET tr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSB_BEDGE_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  UNDISCH_TAC `(e:real^N->bool) IN moi_fsb_bedges c` THEN
  REWRITE_TAC[moi_fsb_bedges; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `1`] MOI_FSA_VS_SIZE) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    UNDISCH_TAC `CARD {t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 1` THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `{t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = {}`
    SUBST1_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC]]);;

(* A boundary vertex: its boundary circle and its two boundary edges. *)

let MOI_FSB_BVERT = prove
 (`!c (x:real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ {x} IN c /\
     x IN surface_boundary c
     ==> connected_component (surface_boundary c) x IN components (surface_boundary c) /\
         x IN connected_component (surface_boundary c) x /\
         (!J. J IN components (surface_boundary c) /\ x IN J
              ==> J = connected_component (surface_boundary c) x) /\
         {e | e IN moi_fsb_bedges c /\ x IN moi_fsa_vs e} HAS_SIZE 2 /\
         (!e J. e IN moi_fsb_bedges c /\ x IN moi_fsa_vs e /\
                J IN components (surface_boundary c) /\ x IN J ==> e SUBSET J)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN connected_component (surface_boundary c) x` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `connected_component (surface_boundary c) (x:real^N) IN components (surface_boundary c)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS]; ALL_TAC] THEN
  SUBGOAL_THEN `!J:real^N->bool. J IN components (surface_boundary c) /\ x IN J
                  ==> J = connected_component (surface_boundary c) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `J:real^N->bool`;
                   `connected_component (surface_boundary c) (x:real^N)`] COMPONENTS_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `{e | e IN moi_fsb_bedges c /\ (x:real^N) IN moi_fsa_vs e} =
      {e | e IN c /\ aff_dim e = &1 /\ x IN e /\
           CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 1}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `e:real^N->bool` THEN
      ASM_CASES_TAC `(e:real^N->bool) IN moi_fsb_bedges c` THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `x:real^N`]
          MOI_FSB_BEDGE_VS_IFF) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        UNDISCH_TAC `(e:real^N->bool) IN moi_fsb_bedges c` THEN
        REWRITE_TAC[moi_fsb_bedges; IN_ELIM_THM] THEN SIMP_TAC[];
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~((e:real^N->bool) IN moi_fsb_bedges c)` THEN
        REWRITE_TAC[moi_fsb_bedges; IN_ELIM_THM] THEN CONV_TAC TAUT];
      ALL_TAC] THEN
    REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FSB_BD_DEGREE THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`e:real^N->bool`; `J:real^N->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN e` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `x:real^N`]
        MOI_FSB_BEDGE_VS_IFF) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSB_BEDGE_COMPONENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[EXISTS_UNIQUE_THM]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `J':real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `J:real^N->bool = J'` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `J:real^N->bool`;
                   `J':real^N->bool`] COMPONENTS_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[]]);;

(* Cone triangles determine apex and base; they are not old triangles. *)

let MOI_FSB_CONE_INJ = prove
 (`(!(J:real^N->bool) J' s s'.
      (INR J:real^N+(real^N->bool)) INSERT IMAGE INL s = INR J' INSERT IMAGE INL s' <=>
      J = J' /\ s = s') /\
   (!(J:real^N->bool) s t.
      ~((INR J:real^N+(real^N->bool)) INSERT IMAGE INL s = IMAGE INL t))`,
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `J:real^N->bool = J'` SUBST_ALL_TAC THENL
       [FIRST_ASSUM(MP_TAC o AP_TERM `\u. (INR J:real^N+(real^N->bool)) IN u`) THEN
        REWRITE_TAC[IN_INSERT; MOI_FSB_INL_IMAGE; injectivity "sum"];
        ALL_TAC] THEN
      REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2 MOI_FSB_INL_IMAGE))] THEN
      MATCH_MP_TAC(SET_RULE `!a s t:real^N+(real^N->bool)->bool.
          ~(a IN s) /\ ~(a IN t) /\ a INSERT s = a INSERT t ==> s = t`) THEN
      EXISTS_TAC `INR J':real^N+(real^N->bool)` THEN ASM_REWRITE_TAC[MOI_FSB_INL_IMAGE];
      SIMP_TAC[]];
    REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `\u. (INR J:real^N+(real^N->bool)) IN u`) THEN
    REWRITE_TAC[IN_INSERT; MOI_FSB_INL_IMAGE]]);;

(* Membership in the capped surface. *)

let MOI_FSB_IN_CAP = prove
 (`!c js (t:real^N+(real^N->bool)->bool).
     t IN moi_fsb_cap c js <=>
     (?tr. tr IN c /\ aff_dim tr = &2 /\ t = IMAGE INL (moi_fsa_vs tr)) \/
     (?J e. J IN js /\ e IN moi_fsb_bedges c /\ e SUBSET J /\
            t = INR J INSERT IMAGE INL (moi_fsa_vs e))`,
  REWRITE_TAC[moi_fsb_cap; moi_fsb_cones; IN_UNION; IN_IMAGE; MOI_FSA_ABS_IMAGE;
              IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* Two-element subsets of an insertion containing the new point. *)

let MOI_FSB_PAIR_SUB = prove
 (`!(a:A) s e. e HAS_SIZE 2 /\ e SUBSET a INSERT s /\ a IN e
               ==> ?z. z IN s /\ ~(z = a) /\ e = {a,z}`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV(LAND_CONV HAS_SIZE_CONV)) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `z1:A` (X_CHOOSE_THEN `z2:A` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `a:A = z1` THENL
   [EXISTS_TAC `z2:A` THEN ASM SET_TAC[];
    EXISTS_TAC `z1:A` THEN ASM SET_TAC[]]);;

(* The capped triangles through an apex edge {INR J, INL x}: the cones over *)
(* the two boundary edges at x.                                              *)

let MOI_FSB_CAP_EDGE_APEX = prove
 (`!c js J (x:real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c) /\ J IN js /\ {x} IN c /\ x IN J
     ==> CARD {t | t IN moi_fsb_cap c js /\
                   {(INR J:real^N+(real^N->bool)),INL x} SUBSET t} = 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^N->bool) IN components (surface_boundary c)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN surface_boundary c` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_FSB_BVERT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `{t | t IN moi_fsb_cap c js /\ {(INR J:real^N+(real^N->bool)),INL x} SUBSET t} =
    IMAGE (\e. (INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs e))
          {e | e IN moi_fsb_bedges c /\ x IN moi_fsa_vs e}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N+(real^N->bool)->bool` THEN
    REWRITE_TAC[MOI_FSB_IN_CAP; IN_IMAGE; IN_ELIM_THM; INSERT_SUBSET; EMPTY_SUBSET] THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      DISCH_THEN(DISJ_CASES_THEN2
       (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `J':real^N->bool` (X_CHOOSE_THEN `b:real^N->bool`
          STRIP_ASSUME_TAC))) THENL
       [UNDISCH_TAC `(INR J:real^N+(real^N->bool)) IN t` THEN
        ASM_REWRITE_TAC[MOI_FSB_INL_IMAGE];
        EXISTS_TAC `b:real^N->bool` THEN
        UNDISCH_TAC `(INR J:real^N+(real^N->bool)) IN t` THEN
        UNDISCH_TAC `(INL x:real^N+(real^N->bool)) IN t` THEN
        ASM_REWRITE_TAC[IN_INSERT; MOI_FSB_INL_IMAGE; injectivity "sum";
                        distinctness "sum"] THEN
        DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[IN_INSERT; MOI_FSB_INL_IMAGE] THEN
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`J:real^N->bool`; `b:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\e. (INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs e))
          {e | e IN moi_fsb_bedges c /\ (x:real^N) IN moi_fsa_vs e} HAS_SIZE 2`
  (fun th -> REWRITE_TAC[REWRITE_RULE[HAS_SIZE] th]) THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[MOI_FSB_CONE_INJ; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FSA_VS_INJ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_MESON_TAC[MOI_FSB_BEDGE_IN]);;

(* ------------------------------------------------------------------------- *)
(* Edges of the capped surface (old edges IMAGE INL (vs E) and apex          *)
(* edges {INR J, INL x}), their triangle counts, the boundary of a partial  *)
(* capping, and dual and local connectivity.                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_FSB_CAP_EDGES = prove
 (`!c js (e:real^N+(real^N->bool)->bool).
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c)
     ==> (e IN moi_fsa_edges (moi_fsb_cap c js) <=>
          (?E. E IN c /\ aff_dim E = &1 /\ e = IMAGE INL (moi_fsa_vs E)) \/
          (?J x. J IN js /\ {x} IN c /\ x IN J /\ e = {INR J, INL x}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^N+(real^N->bool)->bool`
      (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))) THEN
    REWRITE_TAC[MOI_FSB_IN_CAP] THEN
    DISCH_THEN(DISJ_CASES_THEN2
     (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `J:real^N->bool` (X_CHOOSE_THEN `b:real^N->bool`
        STRIP_ASSUME_TAC))) THENL
     [DISJ1_TAC THEN
      UNDISCH_TAC `(e:real^N+(real^N->bool)->bool) SUBSET t` THEN
      ASM_REWRITE_TAC[SUBSET_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `e0:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tr:real^N->bool`] MOI_FSA_VS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
                           ASSUME_TAC(last(CONJUNCTS th))) THEN
      EXISTS_TAC `convex hull e0:real^N->bool` THEN
      SUBGOAL_THEN `convex hull e0 IN c /\ moi_fsa_vs (convex hull e0:real^N->bool) = e0`
      STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(e0:real^N->bool) HAS_SIZE 2` ASSUME_TAC THENL
       [UNDISCH_TAC `(e:real^N+(real^N->bool)->bool) HAS_SIZE 2` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ_EQ THEN
        SIMP_TAC[injectivity "sum"];
        ALL_TAC] THEN
      SUBGOAL_THEN `~affine_dependent (e0:real^N->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[AFFINE_DEPENDENT_MONO]; ALL_TAC] THEN
      ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
      SUBGOAL_THEN `CARD (e0:real^N->bool) = 2` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[HAS_SIZE]; INT_ARITH_TAC];
      SUBGOAL_THEN `(b:real^N->bool) IN c /\ aff_dim b = &1` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[MOI_FSB_BEDGE_IN]; ALL_TAC] THEN
      ASM_CASES_TAC `(INR J:real^N+(real^N->bool)) IN e` THENL
       [DISJ2_TAC THEN
        MP_TAC(ISPECL [`INR J:real^N+(real^N->bool)`;
                       `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs b)`;
                       `e:real^N+(real^N->bool)->bool`] MOI_FSB_PAIR_SUB) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `(e:real^N+(real^N->bool)->bool) SUBSET t` THEN
          ASM_REWRITE_TAC[] THEN SIMP_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^N+(real^N->bool)` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
        MAP_EVERY EXISTS_TAC [`J:real^N->bool`; `y:real^N`] THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`; `y:real^N`]
          MOI_FSB_BEDGE_VS_IFF) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        DISJ1_TAC THEN EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`] MOI_FSB_BEDGE_BASIC) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        SUBGOAL_THEN `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs b) HAS_SIZE 2`
        ASSUME_TAC THENL
         [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_SIMP_TAC[injectivity "sum"];
          ALL_TAC] THEN
        MATCH_MP_TAC CARD_SUBSET_EQ THEN REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[HAS_SIZE];
          UNDISCH_TAC `(e:real^N+(real^N->bool)->bool) SUBSET t` THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `~((INR J:real^N+(real^N->bool)) IN e)` THEN SET_TAC[];
          ASM_MESON_TAC[HAS_SIZE]]]];
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN SIMP_TAC[injectivity "sum"] THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`; `1`] MOI_FSA_VS_SIZE) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`] MOI_FSB_PURE) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
          UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
          REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)` THEN
        REWRITE_TAC[MOI_FSB_IN_CAP; MOI_FSB_INL_IMAGE] THEN CONJ_TAC THENL
         [DISJ1_TAC THEN EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[];
          MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`; `tr:real^N->bool`]
            MOI_FSA_ABS_SUB) THEN
          ASM_REWRITE_TAC[]]];
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[HAS_SIZE; FINITE_INSERT; FINITE_EMPTY] THEN
        SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY;
                 GSYM(distinctness "sum")] THEN
        CONV_TAC NUM_REDUCE_CONV;
        SUBGOAL_THEN `(J:real^N->bool) IN components (surface_boundary c)` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `(x:real^N) IN surface_boundary c` ASSUME_TAC THENL
         [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_FSB_BVERT) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        UNDISCH_TAC `(x:real^N) IN surface_boundary c` THEN
        REWRITE_TAC[MOI_FSB_SB_UNIONS; IN_UNIONS] THEN
        DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(x:real^N) IN moi_fsa_vs b` ASSUME_TAC THENL
         [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`; `x:real^N`]
            MOI_FSB_BEDGE_VS_IFF) THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        EXISTS_TAC `(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b)` THEN
        REWRITE_TAC[MOI_FSB_IN_CAP] THEN CONJ_TAC THENL
         [DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`J:real^N->bool`; `b:real^N->bool`] THEN
          ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; MOI_FSB_INL_IMAGE;
                      distinctness "sum"] THEN
          ASM_REWRITE_TAC[]]]]]);;

(* Triangle counts of the edges of a partial capping: 1 exactly for the old *)
(* boundary edges of the uncapped circles, 2 otherwise.                      *)

let MOI_FSB_CAP_EDGE_COUNT = prove
 (`!c js (e:real^N+(real^N->bool)->bool).
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c) /\ e IN moi_fsa_edges (moi_fsb_cap c js)
     ==> CARD {t | t IN moi_fsb_cap c js /\ e SUBSET t} =
         (if ?E. E IN moi_fsb_bedges c /\ ~(?J. J IN js /\ E SUBSET J) /\
                 e = IMAGE INL (moi_fsa_vs E) then 1 else 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  UNDISCH_TAC `(e:real^N+(real^N->bool)->bool) IN moi_fsa_edges (moi_fsb_cap c js)` THEN
  ASM_SIMP_TAC[MOI_FSB_CAP_EDGES] THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `js:(real^N->bool)->bool`; `E:real^N->bool`]
      MOI_FSB_CAP_EDGE_OLD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `E:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `E':real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `E:real^N->bool = E'` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC MOI_FSA_VS_INJ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_FSB_BEDGE_IN];
        UNDISCH_TAC `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs E) =
                     IMAGE INL (moi_fsa_vs E')` THEN
        REWRITE_TAC[MOI_FSB_INL_IMAGE]]];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `js:(real^N->bool)->bool`; `J:real^N->bool`;
                   `x:real^N`] MOI_FSB_CAP_EDGE_APEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `E:real^N->bool` (MP_TAC o last o CONJUNCTS)) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\u. (INR J:real^N+(real^N->bool)) IN u`) THEN
    REWRITE_TAC[IN_INSERT; MOI_FSB_INL_IMAGE]]);;

(* Small helpers: the other point of a 2-set; a common vertex of meeting   *)
(* simplices; boundary edges are nonempty and closed; the old triangle on a *)
(* boundary edge.                                                            *)

let MOI_FSB_OTHER = prove
 (`!(v:A) s. s HAS_SIZE 2 /\ v IN s ==> ?w. w IN s /\ ~(w = v)`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV(LAND_CONV HAS_SIZE_CONV)) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `z1:A` (X_CHOOSE_THEN `z2:A` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  ASM_CASES_TAC `v:A = z1` THENL
   [EXISTS_TAC `z2:A` THEN ASM SET_TAC[];
    EXISTS_TAC `z1:A` THEN ASM SET_TAC[]]);;

let MOI_FSB_SHARED_VERTEX = prove
 (`!c s t:real^N->bool.
     simplicial_complex c /\ s IN c /\ t IN c /\ ~(s INTER t = {})
     ==> ?w. w IN moi_fsa_vs s /\ w IN moi_fsa_vs t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s INTER t:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s INTER t:real^N->bool`] MOI_FSA_VS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(el 1 (CONJUNCTS th)) THEN ASSUME_TAC(el 4 (CONJUNCTS th))) THEN
  ASM_CASES_TAC `moi_fsa_vs (s INTER t:real^N->bool) = {}` THENL
   [ASM_REWRITE_TAC[CONVEX_HULL_EMPTY]; DISCH_THEN(K ALL_TAC)] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `w:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  EXISTS_TAC `w:real^N` THEN
  SUBGOAL_THEN `{w:real^N} IN c` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN s INTER t` MP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s INTER t:real^N->bool`; `w:real^N`]
      MOI_FSA_VS_MEM) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `w:real^N`] MOI_FSA_VS_MEM) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `w:real^N`] MOI_FSA_VS_MEM) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let MOI_FSB_BEDGE_NE_CLOSED = prove
 (`!c e:real^N->bool.
     simplicial_complex c /\ e IN moi_fsb_bedges c ==> ~(e = {}) /\ closed e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSB_BEDGE_IN) THEN CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CLOSED]]);;

let MOI_FSB_BEDGE_OLD_TRI = prove
 (`!c js b:real^N->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ b IN moi_fsb_bedges c
     ==> IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs b) HAS_SIZE 2 /\
         ?tr. tr IN c /\ aff_dim tr = &2 /\ b SUBSET tr /\
              moi_fsa_vs tr IN moi_fsa_abs c /\
              IMAGE INL (moi_fsa_vs tr) IN moi_fsb_cap c js /\
              IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs b) SUBSET
              IMAGE INL (moi_fsa_vs tr)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`] MOI_FSB_BEDGE_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC))))) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_SIMP_TAC[injectivity "sum"]; ALL_TAC] THEN
  EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_fsa_vs (tr:real^N->bool) IN moi_fsa_abs c` ASSUME_TAC THENL
   [REWRITE_TAC[moi_fsa_abs; IN_ELIM_THM] THEN EXISTS_TAC `tr:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_FSB_INL_IMAGE] THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_fsb_cap; IN_UNION] THEN DISJ1_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`; `tr:real^N->bool`]
      MOI_FSA_ABS_SUB) THEN
    ASM_REWRITE_TAC[]]);;

(* Dual connectivity of any partial capping of a connected surface. *)

let MOI_FSB_CAP_DCONN = prove
 (`!c js:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ connected (UNIONS c) /\
     js SUBSET components (surface_boundary c)
     ==> moi_fsa_dconn (moi_fsb_cap c js)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[moi_fsa_dconn] THEN X_GEN_TAC `X:(real^N+(real^N->bool)->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "XC"))) THEN
  ABBREV_TAC `Y = {tr:real^N->bool | tr IN moi_fsa_abs c /\
                                     IMAGE (INL:real^N->real^N+(real^N->bool)) tr IN X}` THEN
  SUBGOAL_THEN `Y = moi_fsa_abs (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSB_ABS_DCONN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[moi_fsa_dconn]] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Y" THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      UNDISCH_TAC `~(X:(real^N+(real^N->bool)->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `t:real^N+(real^N->bool)->bool`) THEN
      SUBGOAL_THEN `(t:real^N+(real^N->bool)->bool) IN moi_fsb_cap (c:(real^N->bool)->bool) js` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MOI_FSB_IN_CAP] THEN
      DISCH_THEN(DISJ_CASES_THEN2
       (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `J:real^N->bool` (X_CHOOSE_THEN `b:real^N->bool`
          STRIP_ASSUME_TAC))) THENL
       [EXISTS_TAC `moi_fsa_vs (tr:real^N->bool)` THEN EXPAND_TAC "Y" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
         [REWRITE_TAC[moi_fsa_abs; IN_ELIM_THM] THEN EXISTS_TAC `tr:real^N->bool` THEN
          ASM_REWRITE_TAC[];
          UNDISCH_TAC `(t:real^N+(real^N->bool)->bool) IN X` THEN ASM_REWRITE_TAC[]];
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `js:(real^N->bool)->bool`;
                       `b:real^N->bool`] MOI_FSB_BEDGE_OLD_TRI) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)) THEN
        EXISTS_TAC `moi_fsa_vs (tr:real^N->bool)` THEN EXPAND_TAC "Y" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "XC" (MATCH_MP_TAC o SPECL
          [`t:real^N+(real^N->bool)->bool`;
           `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)`;
           `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs b)`]) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      MAP_EVERY X_GEN_TAC [`t1:real^N->bool`; `t2:real^N->bool`; `e:real^N->bool`] THEN
      EXPAND_TAC "Y" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "XC" (MATCH_MP_TAC o SPECL
        [`IMAGE (INL:real^N->real^N+(real^N->bool)) t1`;
         `IMAGE (INL:real^N->real^N+(real^N->bool)) t2`;
         `IMAGE (INL:real^N->real^N+(real^N->bool)) e`]) THEN
      ASM_REWRITE_TAC[MOI_FSB_INL_IMAGE] THEN CONJ_TAC THENL
       [REWRITE_TAC[moi_fsb_cap; IN_UNION] THEN DISJ1_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_SIMP_TAC[injectivity "sum"]]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `t:real^N+(real^N->bool)->bool` THEN
  REWRITE_TAC[MOI_FSB_IN_CAP] THEN
  DISCH_THEN(DISJ_CASES_THEN2
   (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `J:real^N->bool` (X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC))) THENL
   [SUBGOAL_THEN `moi_fsa_vs (tr:real^N->bool) IN Y` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_fsa_abs; IN_ELIM_THM] THEN
      EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "Y" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `js:(real^N->bool)->bool`; `b:real^N->bool`]
      MOI_FSB_BEDGE_OLD_TRI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `moi_fsa_vs (tr:real^N->bool) IN Y` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "Y" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "XC" (MATCH_MP_TAC o SPECL
      [`IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)`;
       `t:real^N+(real^N->bool)->bool`;
       `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs b)`]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[MOI_FSB_IN_CAP] THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`J:real^N->bool`; `b:real^N->bool`] THEN ASM_REWRITE_TAC[];
      SET_TAC[]]]);;

(* Local connectivity at an old vertex INL v: the old triangles at v form a *)
(* connected fan (MOI_FSB_ABS_LCONN) and each cone at v is adjacent to the  *)
(* old triangle on its base edge.                                            *)

let MOI_FSB_CAP_LCONN_INL = prove
 (`!c js (v:real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c)
     ==> moi_fsa_lconn (moi_fsb_cap c js) (INL v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_lconn; moi_fsa_lclosed] THEN
  X_GEN_TAC `y:(real^N+(real^N->bool)->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LC"))) THEN
  ABBREV_TAC `Yo = {tr:real^N->bool | tr IN moi_fsa_abs c /\ v IN tr /\
                                      IMAGE (INL:real^N->real^N+(real^N->bool)) tr IN y}` THEN
  SUBGOAL_THEN `Yo = {tr:real^N->bool | tr IN moi_fsa_abs c /\ v IN tr}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSB_ABS_LCONN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN
    REWRITE_TAC[moi_fsa_lconn; moi_fsa_lclosed] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Yo" THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      UNDISCH_TAC `~(y:(real^N+(real^N->bool)->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `t:real^N+(real^N->bool)->bool`) THEN
      SUBGOAL_THEN `(t:real^N+(real^N->bool)->bool) IN moi_fsb_cap (c:(real^N->bool)->bool) js /\
                    (INL v:real^N+(real^N->bool)) IN t` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MOI_FSB_IN_CAP] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN2
       (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `J:real^N->bool` (X_CHOOSE_THEN `b:real^N->bool`
          STRIP_ASSUME_TAC))) ASSUME_TAC) THENL
       [SUBGOAL_THEN `(v:real^N) IN moi_fsa_vs tr` ASSUME_TAC THENL
         [UNDISCH_TAC `(INL v:real^N+(real^N->bool)) IN t` THEN
          ASM_REWRITE_TAC[MOI_FSB_INL_IMAGE];
          ALL_TAC] THEN
        SUBGOAL_THEN `moi_fsa_vs (tr:real^N->bool) IN moi_fsa_abs c` ASSUME_TAC THENL
         [REWRITE_TAC[moi_fsa_abs; IN_ELIM_THM] THEN EXISTS_TAC `tr:real^N->bool` THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        EXISTS_TAC `moi_fsa_vs (tr:real^N->bool)` THEN EXPAND_TAC "Yo" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(t:real^N+(real^N->bool)->bool) IN y` THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(v:real^N) IN moi_fsa_vs b` ASSUME_TAC THENL
         [UNDISCH_TAC `(INL v:real^N+(real^N->bool)) IN t` THEN
          ASM_REWRITE_TAC[IN_INSERT; MOI_FSB_INL_IMAGE; distinctness "sum"];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `js:(real^N->bool)->bool`;
                       `b:real^N->bool`] MOI_FSB_BEDGE_OLD_TRI) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)) THEN
        MP_TAC(ISPECL [`v:real^N`; `moi_fsa_vs (b:real^N->bool)`] MOI_FSB_OTHER) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL [ASM_MESON_TAC[MOI_FSB_BEDGE_BASIC]; ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `moi_fsa_vs (b:real^N->bool) SUBSET moi_fsa_vs tr` ASSUME_TAC THENL
         [UNDISCH_TAC `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs b) SUBSET
                       IMAGE INL (moi_fsa_vs tr)` THEN
          REWRITE_TAC[MOI_FSB_INL_IMAGE];
          ALL_TAC] THEN
        EXISTS_TAC `moi_fsa_vs (tr:real^N->bool)` THEN EXPAND_TAC "Yo" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        USE_THEN "LC" (MATCH_MP_TAC o SPECL
          [`t:real^N+(real^N->bool)->bool`;
           `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)`;
           `INL w:real^N+(real^N->bool)`]) THEN
        ASM_REWRITE_TAC[IN_INSERT; MOI_FSB_INL_IMAGE; injectivity "sum";
                        distinctness "sum"] THEN
        ASM SET_TAC[]];
      MAP_EVERY X_GEN_TAC [`t1:real^N->bool`; `t2:real^N->bool`; `u:real^N`] THEN
      EXPAND_TAC "Yo" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "LC" (MATCH_MP_TAC o SPECL
        [`IMAGE (INL:real^N->real^N+(real^N->bool)) t1`;
         `IMAGE (INL:real^N->real^N+(real^N->bool)) t2`;
         `INL u:real^N+(real^N->bool)`]) THEN
      ASM_REWRITE_TAC[MOI_FSB_INL_IMAGE; injectivity "sum"] THEN
      REWRITE_TAC[moi_fsb_cap; IN_UNION] THEN DISJ1_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N+(real^N->bool)->bool` THEN
  EQ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; MOI_FSB_IN_CAP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN2
     (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `J:real^N->bool` (X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC)))
     ASSUME_TAC) THENL
   [SUBGOAL_THEN `moi_fsa_vs (tr:real^N->bool) IN Yo` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [REWRITE_TAC[moi_fsa_abs; IN_ELIM_THM] THEN EXISTS_TAC `tr:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(INL v:real^N+(real^N->bool)) IN t` THEN
        ASM_REWRITE_TAC[MOI_FSB_INL_IMAGE]];
      EXPAND_TAC "Yo" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]];
    SUBGOAL_THEN `(v:real^N) IN moi_fsa_vs b` ASSUME_TAC THENL
     [UNDISCH_TAC `(INL v:real^N+(real^N->bool)) IN t` THEN
      ASM_REWRITE_TAC[IN_INSERT; MOI_FSB_INL_IMAGE; distinctness "sum"];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `js:(real^N->bool)->bool`; `b:real^N->bool`]
      MOI_FSB_BEDGE_OLD_TRI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`v:real^N`; `moi_fsa_vs (b:real^N->bool)`] MOI_FSB_OTHER) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[MOI_FSB_BEDGE_BASIC]; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_fsa_vs (b:real^N->bool) SUBSET moi_fsa_vs tr` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs b) SUBSET
                   IMAGE INL (moi_fsa_vs tr)` THEN
      REWRITE_TAC[MOI_FSB_INL_IMAGE];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr) IN y`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `moi_fsa_vs (tr:real^N->bool) IN Yo` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[];
        EXPAND_TAC "Yo" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "LC" (MATCH_MP_TAC o SPECL
      [`IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)`;
       `t:real^N+(real^N->bool)->bool`; `INL w:real^N+(real^N->bool)`]) THEN
    ASM_REWRITE_TAC[IN_INSERT; MOI_FSB_INL_IMAGE; injectivity "sum"; distinctness "sum"] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MOI_FSB_IN_CAP] THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`J:real^N->bool`; `b:real^N->bool`] THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]]]);;

(* Local connectivity at an apex INR Jk: the cones over the boundary edges  *)
(* of the circle Jk, adjacent through shared vertices; a split into two     *)
(* classes would split Jk into two disjoint closed pieces.                   *)

let MOI_FSB_CAP_LCONN_INR = prove
 (`!c js (Jk:real^N->bool).
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c)
     ==> moi_fsa_lconn (moi_fsb_cap c js) (INR Jk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsa_lconn; moi_fsa_lclosed] THEN
  X_GEN_TAC `y:(real^N+(real^N->bool)->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LC"))) THEN
  SUBGOAL_THEN
   `!t. t IN moi_fsb_cap c js /\ (INR Jk:real^N+(real^N->bool)) IN t <=>
        Jk IN js /\ ?b. b IN moi_fsb_bedges c /\ b SUBSET Jk /\
                        t = INR Jk INSERT IMAGE INL (moi_fsa_vs b)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MOI_FSB_IN_CAP] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN2
        (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `J:real^N->bool` (X_CHOOSE_THEN `b:real^N->bool`
           STRIP_ASSUME_TAC))) MP_TAC) THEN
      ASM_REWRITE_TAC[MOI_FSB_INL_IMAGE; IN_INSERT; injectivity "sum"] THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[IN_INSERT] THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`Jk:real^N->bool`; `b:real^N->bool`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(Jk:real^N->bool) IN js` THENL
   [ALL_TAC;
    UNDISCH_TAC `~(y:(real^N+(real^N->bool)->bool)->bool = {})` THEN
    UNDISCH_TAC `y SUBSET {t | t IN moi_fsb_cap (c:(real^N->bool)->bool) js /\
                               (INR Jk:real^N+(real^N->bool)) IN t}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]] THEN
  SUBGOAL_THEN `(Jk:real^N->bool) IN components (surface_boundary c)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `B1 = {b:real^N->bool | b IN moi_fsb_bedges c /\ b SUBSET Jk /\
                    (INR Jk:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b) IN y}` THEN
  ABBREV_TAC `B2 = {b:real^N->bool | b IN moi_fsb_bedges c /\ b SUBSET Jk /\
                    ~((INR Jk:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b) IN y)}` THEN
  SUBGOAL_THEN `B2:(real^N->bool)->bool = {}` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPEC `Jk:real^N->bool` CONNECTED_CLOSED) THEN
    SUBGOAL_THEN `connected (Jk:real^N->bool)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`UNIONS B1:real^N->bool`; `UNIONS B2:real^N->bool`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "B1" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        MESON_TAC[MOI_FSB_BEDGE_IN];
        EXPAND_TAC "B1" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_MESON_TAC[MOI_FSB_BEDGE_NE_CLOSED]];
      MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "B2" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        MESON_TAC[MOI_FSB_BEDGE_IN];
        EXPAND_TAC "B2" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_MESON_TAC[MOI_FSB_BEDGE_NE_CLOSED]];
      REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS] THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(p:real^N) IN surface_boundary c` MP_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[MOI_FSB_SB_UNIONS; IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(b:real^N->bool) SUBSET Jk` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`]
          MOI_FSB_BEDGE_COMPONENT) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[EXISTS_UNIQUE_THM]] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `J':real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
        SUBGOAL_THEN `J':real^N->bool = Jk` (SUBST1_TAC o SYM) THENL
         [MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `J':real^N->bool`;
                         `Jk:real^N->bool`] COMPONENTS_EQ) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[];
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      ASM_CASES_TAC
       `(INR Jk:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b) IN y` THENL
       [DISJ1_TAC; DISJ2_TAC] THEN
      EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[] THENL
       [EXPAND_TAC "B1"; EXPAND_TAC "B2"] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS] THEN
      X_GEN_TAC `p:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `b1:real^N->bool` STRIP_ASSUME_TAC)
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `b2:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      UNDISCH_TAC `(b2:real^N->bool) IN B2` THEN UNDISCH_TAC `(b1:real^N->bool) IN B1` THEN
      EXPAND_TAC "B1" THEN EXPAND_TAC "B2" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b1:real^N->bool`; `b2:real^N->bool`]
        MOI_FSB_SHARED_VERTEX) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[MOI_FSB_BEDGE_IN]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[MOI_FSB_BEDGE_IN]; ASM SET_TAC[]];
        DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)] THEN
      UNDISCH_TAC
       `~((INR Jk:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b2) IN y)` THEN
      REWRITE_TAC[] THEN
      USE_THEN "LC" (MATCH_MP_TAC o SPECL
        [`(INR Jk:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b1)`;
         `(INR Jk:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b2)`;
         `INL w:real^N+(real^N->bool)`]) THEN
      ASM_REWRITE_TAC[IN_INSERT; MOI_FSB_INL_IMAGE; distinctness "sum"] THEN
      REWRITE_TAC[MOI_FSB_IN_CAP] THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`Jk:real^N->bool`; `b2:real^N->bool`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      UNDISCH_TAC `~(y:(real^N+(real^N->bool)->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `t:real^N+(real^N->bool)->bool`) THEN
      SUBGOAL_THEN `(t:real^N+(real^N->bool)->bool) IN moi_fsb_cap (c:(real^N->bool)->bool) js /\
                    (INR Jk:real^N+(real^N->bool)) IN t` MP_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`] MOI_FSB_BEDGE_NE_CLOSED) THEN
      ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `p:real^N` o CONJUNCT1) THEN
      EXISTS_TAC `p:real^N` THEN REWRITE_TAC[IN_INTER; IN_UNIONS] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "B1" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
        ASM SET_TAC[]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      UNDISCH_TAC `~(B2:(real^N->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `b:real^N->bool`) THEN
      SUBGOAL_THEN `(b:real^N->bool) IN moi_fsb_bedges c /\ b SUBSET Jk` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(b:real^N->bool) IN B2` THEN EXPAND_TAC "B2" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`] MOI_FSB_BEDGE_NE_CLOSED) THEN
      ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `p:real^N` o CONJUNCT1) THEN
      EXISTS_TAC `p:real^N` THEN REWRITE_TAC[IN_INTER; IN_UNIONS] THEN
      CONJ_TAC THENL [EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N+(real^N->bool)->bool` THEN
  EQ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(b:real^N->bool) IN B2` MP_TAC THENL
   [EXPAND_TAC "B2" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[NOT_IN_EMPTY]]);;

let MOI_FSB_CAP_LCONN = prove
 (`!c js:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c)
     ==> !z. moi_fsa_lconn (moi_fsb_cap c js) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `z:real^N+(real^N->bool)` (cases "sum")) THEN
  ASM_SIMP_TAC[MOI_FSB_CAP_LCONN_INL; MOI_FSB_CAP_LCONN_INR]);;

(* Capping every boundary circle gives a closed abstract surface. *)

let MOI_FSB_CAP_SURF = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c
     ==> moi_fsa_surf (moi_fsb_cap c (components (surface_boundary c)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fsa_surf] THEN
  SUBGOAL_THEN `components (surface_boundary (c:(real^N->bool)->bool)) SUBSET
                components (surface_boundary c)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FSB_CAP_BASIC; MOI_FSB_CAP_LCONN] THEN
  TRY(CONJ_TAC THENL [ASM_MESON_TAC[MOI_FSB_CAP_BASIC]; ALL_TAC]) THEN
  X_GEN_TAC `e:real^N+(real^N->bool)->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `components (surface_boundary (c:(real^N->bool)->bool))`;
                 `e:real^N+(real^N->bool)->bool`] MOI_FSB_CAP_EDGE_COUNT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~(?J:real^N->bool. J IN components (surface_boundary c) /\ E SUBSET J)` THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`] MOI_FSB_BEDGE_COMPONENT) THEN
  ASM_REWRITE_TAC[EXISTS_UNIQUE_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Counting the partial cappings (V + b, F + #bedges, E + #bverts,          *)
(* with #bverts = #bedges by double counting) and the Euler bound           *)
(* complex_euler c + b <= 2 (MOI_FSA_COUNT on the closed capped surface).   *)
(* ------------------------------------------------------------------------- *)

let MOI_FSB_BEDGE_IN_CIRCLE = prove
 (`!c b J:real^N->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ b IN moi_fsb_bedges c /\
     J IN components (surface_boundary c) /\ ~(b INTER J = {})
     ==> b SUBSET J`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`] MOI_FSB_BEDGE_COMPONENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[EXISTS_UNIQUE_THM]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `J':real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `J':real^N->bool = J` (SUBST1_TAC o SYM) THENL
   [MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `J':real^N->bool`;
                   `J:real^N->bool`] COMPONENTS_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[]]);;

let MOI_FSB_CIRCLE_EDGE = prove
 (`!c J:real^N->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     J IN components (surface_boundary c)
     ==> ?b. b IN moi_fsb_bedges c /\ b SUBSET J`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `p:real^N`) THEN
  SUBGOAL_THEN `(p:real^N) IN surface_boundary c` MP_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[MOI_FSB_SB_UNIONS; IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FSB_BEDGE_IN_CIRCLE THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FSB_CIRCLE_SELECT = prove
 (`!c js e J:real^N->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c) /\
     e IN moi_fsb_bedges c /\ J IN js /\ e SUBSET J
     ==> (@J. J IN js /\ e SUBSET J) = J`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `J':real^N->bool` THEN REWRITE_TAC[] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSB_BEDGE_COMPONENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[EXISTS_UNIQUE_THM]] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_FSB_VCIRCLE_SELECT = prove
 (`!c js J (x:real^N).
     js SUBSET components (surface_boundary c) /\ J IN js /\ x IN J
     ==> (@J. J IN js /\ x IN J) = J`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `J':real^N->bool` THEN REWRITE_TAC[] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`surface_boundary (c:(real^N->bool)->bool)`; `J':real^N->bool`;
                   `J:real^N->bool`] COMPONENTS_EQ) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* Vertices of a partial capping. *)

let MOI_FSB_CAP_UNIONS = prove
 (`!c js:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c)
     ==> UNIONS (moi_fsb_cap c js) =
         IMAGE (INL:real^N->real^N+(real^N->bool)) {v | {v} IN c} UNION IMAGE INR js`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N+(real^N->bool)` THEN
  REWRITE_TAC[IN_UNIONS; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^N+(real^N->bool)->bool` MP_TAC) THEN
    REWRITE_TAC[MOI_FSB_IN_CAP] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN2
     (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `J:real^N->bool` (X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC)))
     MP_TAC) THEN
    ASM_REWRITE_TAC[IN_INSERT; IN_IMAGE] THENL
     [DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN DISJ1_TAC THEN
      EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tr:real^N->bool`] MOI_FSA_VS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o el 4 o CONJUNCTS) THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC THENL
       [DISJ2_TAC THEN EXISTS_TAC `J:real^N->bool` THEN ASM_REWRITE_TAC[];
        DISJ1_TAC THEN EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[MOI_FSB_BEDGE_VS_IFF]]];
    STRIP_TAC THENL
     [MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSB_ABS_COUNTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE (INL:real^N->real^N+(real^N->bool)) u` THEN
      ASM_REWRITE_TAC[MOI_FSB_INL_IMAGE] THEN
      REWRITE_TAC[moi_fsb_cap; IN_UNION] THEN DISJ1_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(x:real^N->bool) IN components (surface_boundary c)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N->bool`] MOI_FSB_CIRCLE_EDGE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(INR x:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b)` THEN
      ASM_REWRITE_TAC[IN_INSERT; MOI_FSB_IN_CAP] THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:real^N->bool`; `b:real^N->bool`] THEN ASM_REWRITE_TAC[]]]);;

let MOI_FSB_CAP_VCARD = prove
 (`!c js:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c)
     ==> CARD (UNIONS (moi_fsb_cap c js)) = CARD {v:real^N | {v} IN c} + CARD js`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[MOI_FSB_CAP_UNIONS] THEN
  SUBGOAL_THEN `FINITE {v:real^N | {v} IN c}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (js:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `components (surface_boundary (c:(real^N->bool)->bool))` THEN
    ASM_SIMP_TAC[MOI_FSB_BD_CIRCLES];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) CARD_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    MESON_TAC[distinctness "sum"];
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
  ASM_SIMP_TAC[injectivity "sum"]);;

(* Triangles of a partial capping: those of c and one cone per boundary   *)
(* edge of a capped circle.                                                *)

let MOI_FSB_CAP_FCARD = prove
 (`!c js:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c)
     ==> CARD (moi_fsb_cap c js) =
         CARD {t:real^N->bool | t IN c /\ aff_dim t = &2} +
         CARD {e | e IN moi_fsb_bedges c /\ ?J. J IN js /\ e SUBSET J}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  ABBREV_TAC `BE = {e:real^N->bool | e IN moi_fsb_bedges c /\ ?J. J IN js /\ e SUBSET J}` THEN
  SUBGOAL_THEN `FINITE (BE:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "BE" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[MOI_FSB_BEDGE_IN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fsb_cones c js =
    IMAGE (\e. (INR (@J. J IN js /\ e SUBSET J):real^N+(real^N->bool)) INSERT
               IMAGE INL (moi_fsa_vs e)) BE`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N+(real^N->bool)->bool` THEN
    REWRITE_TAC[moi_fsb_cones; IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `J:real^N->bool` (X_CHOOSE_THEN `e:real^N->bool`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `e:real^N->bool` THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `js:(real^N->bool)->bool`; `e:real^N->bool`;
                     `J:real^N->bool`] MOI_FSB_CIRCLE_SELECT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "BE" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(e:real^N->bool) IN BE` THEN EXPAND_TAC "BE" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `J:real^N->bool` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`J:real^N->bool`; `e:real^N->bool`] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `js:(real^N->bool)->bool`; `e:real^N->bool`;
                     `J:real^N->bool`] MOI_FSB_CIRCLE_SELECT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_fsb_cap] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) CARD_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[MOI_FSA_ABS_IMAGE] THEN
      MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[FINITE_IMAGE]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `u:real^N+(real^N->bool)->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `u = IMAGE (INL:real^N->real^N+(real^N->bool)) s` THEN
    ASM_REWRITE_TAC[MOI_FSB_CONE_INJ];
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `CARD (moi_fsa_abs (c:(real^N->bool)->bool))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[MOI_FSB_INL_IMAGE] THEN
      SIMP_TAC[] THEN REWRITE_TAC[MOI_FSA_ABS_IMAGE] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[MOI_FSB_ABS_COUNTS]];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[MOI_FSB_CONE_INJ] THEN
    MAP_EVERY X_GEN_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN
    EXPAND_TAC "BE" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FSA_VS_INJ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[MOI_FSB_BEDGE_IN]]);;

(* Edges of a partial capping: those of c and one apex edge per boundary   *)
(* vertex of a capped circle.                                              *)

let MOI_FSB_CAP_ECARD = prove
 (`!c js:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c)
     ==> CARD (moi_fsa_edges (moi_fsb_cap c js)) =
         CARD {e:real^N->bool | e IN c /\ aff_dim e = &1} +
         CARD {x:real^N | {x} IN c /\ ?J. J IN js /\ x IN J}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  ABBREV_TAC `BV = {x:real^N | {x} IN c /\ ?J. J IN js /\ x IN J}` THEN
  ABBREV_TAC `EE = {e:real^N->bool | e IN c /\ aff_dim e = &1}` THEN
  SUBGOAL_THEN `FINITE (EE:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "EE" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (BV:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:real^N | {x} IN c}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      EXPAND_TAC "BV" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fsa_edges (moi_fsb_cap c js) =
    IMAGE (\E. IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs E)) EE UNION
    IMAGE (\x. {(INR (@J. J IN js /\ x IN J):real^N+(real^N->bool)), INL x}) BV`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N+(real^N->bool)->bool` THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `js:(real^N->bool)->bool`;
                   `e:real^N+(real^N->bool)->bool`] MOI_FSB_CAP_EDGES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
    EXPAND_TAC "EE" THEN EXPAND_TAC "BV" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EQ_TAC THEN STRIP_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `E:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `x:real^N` THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `js:(real^N->bool)->bool`;
                     `J:real^N->bool`; `x:real^N`] MOI_FSB_VCIRCLE_SELECT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `J:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISJ1_TAC THEN EXISTS_TAC `x:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`J:real^N->bool`; `x:real^N`] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `js:(real^N->bool)->bool`;
                     `J:real^N->bool`; `x:real^N`] MOI_FSB_VCIRCLE_SELECT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) CARD_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `u:real^N+(real^N->bool)->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `u = IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs E)` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM
      `\s. (INR (@J. J IN js /\ (x:real^N) IN J):real^N+(real^N->bool)) IN s`) THEN
    REWRITE_TAC[IN_INSERT; MOI_FSB_INL_IMAGE];
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THENL
   [MAP_EVERY X_GEN_TAC [`E1:real^N->bool`; `E2:real^N->bool`] THEN
    EXPAND_TAC "EE" THEN REWRITE_TAC[IN_ELIM_THM; MOI_FSB_INL_IMAGE] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FSA_VS_INJ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x1:real^N`; `x2:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\s. (INL x1:real^N+(real^N->bool)) IN s`) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; injectivity "sum"; distinctness "sum"] THEN
    MESON_TAC[]]);;

(* Each capped circle has as many vertices as edges (double counting the   *)
(* incidences; every boundary vertex lies on two boundary edges).          *)

let MOI_FSB_HANDSHAKE = prove
 (`!c js:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c)
     ==> CARD {x:real^N | {x} IN c /\ ?J. J IN js /\ x IN J} =
         CARD {e | e IN moi_fsb_bedges c /\ ?J. J IN js /\ e SUBSET J}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  ABBREV_TAC `BV = {x:real^N | {x} IN c /\ ?J. J IN js /\ x IN J}` THEN
  ABBREV_TAC `BE = {e:real^N->bool | e IN moi_fsb_bedges c /\ ?J. J IN js /\ e SUBSET J}` THEN
  SUBGOAL_THEN `FINITE (BV:real^N->bool) /\ FINITE (BE:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:real^N | {x} IN c}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        EXPAND_TAC "BV" THEN SET_TAC[]];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "BE" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[MOI_FSB_BEDGE_IN]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN BV ==> CARD {y | y IN BE /\ x IN moi_fsa_vs y} = 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN EXPAND_TAC "BV" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `J:real^N->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(J:real^N->bool) IN components (surface_boundary c)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN surface_boundary c` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_FSB_BVERT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `{y | y IN BE /\ (x:real^N) IN moi_fsa_vs y} =
                  {e | e IN moi_fsb_bedges c /\ x IN moi_fsa_vs e}`
    SUBST1_TAC THENL
     [EXPAND_TAC "BE" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      X_GEN_TAC `e:real^N->bool` THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `J:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[HAS_SIZE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e:real^N->bool. e IN BE ==> CARD {x | x IN BV /\ x IN moi_fsa_vs e} = 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN EXPAND_TAC "BE" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `J:real^N->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `{x | x IN BV /\ (x:real^N) IN moi_fsa_vs e} = moi_fsa_vs e`
    SUBST1_TAC THENL
     [EXPAND_TAC "BV" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
      EQ_TAC THENL [SIMP_TAC[]; DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `x:real^N`]
        MOI_FSB_BEDGE_VS_IFF) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `J:real^N->bool` THEN ASM SET_TAC[];
      ASM_MESON_TAC[MOI_FSB_BEDGE_BASIC; HAS_SIZE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(x:real^N) (e:real^N->bool). x IN moi_fsa_vs e`;
                 `\(x:real^N) (e:real^N->bool). 1`;
                 `BV:real^N->bool`; `BE:(real^N->bool)->bool`] NSUM_NSUM_RESTRICT) THEN
  ASM_SIMP_TAC[GSYM CARD_EQ_NSUM; FINITE_RESTRICT] THEN
  SUBGOAL_THEN
   `nsum BV (\x:real^N. CARD {y | y IN BE /\ x IN moi_fsa_vs y}) = nsum BV (\x. 2) /\
    nsum BE (\y:real^N->bool. CARD {x | x IN BV /\ x IN moi_fsa_vs y}) = nsum BE (\y. 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[NSUM_CONST] THEN ARITH_TAC]);;

(* V + F - E of a partial capping is chi(c) + #js. *)

let MOI_FSB_CAP_EULER = prove
 (`!c js:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c)
     ==> &(CARD (UNIONS (moi_fsb_cap c js))) + &(CARD (moi_fsb_cap c js)) =
         &(CARD (moi_fsa_edges (moi_fsb_cap c js))) + complex_euler c + &(CARD js)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FSB_CAP_VCARD; MOI_FSB_CAP_FCARD; MOI_FSB_CAP_ECARD; MOI_FSB_HANDSHAKE;
               MOI_FSB_EULER] THEN
  (* the atoms are alpha-equivalent but not identical: match a generic identity *)
  MATCH_ACCEPT_TAC(prove
   (`!V j Fc B E. &(V + j) + &(Fc + B):real = &(E + B) + (&V - &E + &Fc) + &j`,
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC)));;

(* The second conclusion of the main theorem: chi + b <= 2. *)

let MOI_FSB_EULER_BOUND = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ connected (UNIONS c) /\
     ~(UNIONS c = {})
     ==> complex_euler c + &(CARD (components (surface_boundary c))) <= &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `components (surface_boundary (c:(real^N->bool)->bool)) SUBSET
                components (surface_boundary c)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `components (surface_boundary (c:(real^N->bool)->bool))`]
    MOI_FSB_CAP_EULER) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `moi_fsb_cap (c:(real^N->bool)->bool) (components (surface_boundary c))`
    MOI_FSA_COUNT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FSB_CAP_BASIC];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      UNDISCH_TAC `~(UNIONS c:real^N->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `s:real^N->bool`
        STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FSB_PURE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)` THEN
      REWRITE_TAC[MOI_FSB_IN_CAP] THEN DISJ1_TAC THEN EXISTS_TAC `tr:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[MOI_FSB_CAP_BASIC];
      MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FSB_CAP_SURF) THEN
      ASM_REWRITE_TAC[moi_fsa_surf] THEN STRIP_TAC THEN ASM_SIMP_TAC[LE_REFL];
      MATCH_MP_TAC MOI_FSB_CAP_DCONN THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Transfer of the abstract surface notions of pc_moi_fnd_surfa             *)
(* (moi_fsa_edges, _surf, _dconn, _lconn, _bd, _good) along a map f that is *)
(* injective on the vertices, the geometry of a realized abstract surface,  *)
(* and its polyhedron.                                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_FSB_TR_SUB = prove
 (`!(f:A->B) u s t.
     (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\ s SUBSET u /\ t SUBSET u
     ==> (IMAGE f s SUBSET IMAGE f t <=> s SUBSET t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[IMAGE_SUBSET]] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN DISCH_TAC THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `x:A = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let MOI_FSB_TR_EQ = prove
 (`!(f:A->B) u s t.
     (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\ s SUBSET u /\ t SUBSET u
     ==> (IMAGE f s = IMAGE f t <=> s = t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  BINOP_TAC THEN MATCH_MP_TAC MOI_FSB_TR_SUB THEN EXISTS_TAC `u:A->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_FSB_TR_INJ_ON = prove
 (`!(f:A->B) d t s.
     (!x y. x IN UNIONS d /\ y IN UNIONS d /\ f x = f y ==> x = y) /\
     t IN d /\ s SUBSET t
     ==> (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)`,
  REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[SUBSET]);;

let MOI_FSB_TR_EDGES = prove
 (`!(f:A->B) d.
     (!x y. x IN UNIONS d /\ y IN UNIONS d /\ f x = f y ==> x = y)
     ==> moi_fsa_edges (IMAGE (IMAGE f) d) = IMAGE (IMAGE f) (moi_fsa_edges d)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `e:B->bool` THEN
  REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM; IN_IMAGE; EXISTS_IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `(e:B->bool) SUBSET IMAGE f (t:A->bool)` THEN REWRITE_TAC[SUBSET_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `e0:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e0:A->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(e:B->bool) HAS_SIZE 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ_EQ THEN
      MATCH_MP_TAC MOI_FSB_TR_INJ_ON THEN
      MAP_EVERY EXISTS_TAC [`d:(A->bool)->bool`; `t:A->bool`] THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `e0:A->bool` (CONJUNCTS_THEN2 SUBST1_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC)))) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FSB_TR_INJ_ON THEN
      MAP_EVERY EXISTS_TAC [`d:(A->bool)->bool`; `t:A->bool`] THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `t:A->bool` THEN ASM_SIMP_TAC[IMAGE_SUBSET]]]);;

let MOI_FSB_TR_STAR = prove
 (`!(f:A->B) d e.
     (!x y. x IN UNIONS d /\ y IN UNIONS d /\ f x = f y ==> x = y) /\
     e SUBSET UNIONS d
     ==> {t | t IN IMAGE (IMAGE f) d /\ IMAGE f e SUBSET t} =
         IMAGE (IMAGE f) {t | t IN d /\ e SUBSET t}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t':B->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:A->B) e SUBSET IMAGE f t` THEN
    MP_TAC(ISPECL [`f:A->B`; `UNIONS d:A->bool`; `e:A->bool`; `t:A->bool`] MOI_FSB_TR_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]]]);;

let MOI_FSB_TR_CARD = prove
 (`!(f:A->B) d X.
     (!x y. x IN UNIONS d /\ y IN UNIONS d /\ f x = f y ==> x = y) /\
     FINITE X /\ (!t. t IN X ==> t SUBSET UNIONS d)
     ==> CARD (IMAGE (IMAGE f) X) = CARD X`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:A->bool`; `y:A->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `UNIONS d:A->bool`; `x:A->bool`; `y:A->bool`] MOI_FSB_TR_EQ) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]);;

(* Local connectivity transfers (at the image vertices; elsewhere the star  *)
(* is empty).                                                                *)

let MOI_FSB_TR_LCONN = prove
 (`!(f:A->B) d.
     (!x y. x IN UNIONS d /\ y IN UNIONS d /\ f x = f y ==> x = y) /\
     (!x. moi_fsa_lconn d x)
     ==> !y. moi_fsa_lconn (IMAGE (IMAGE f) d) y`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LD")) THEN
  X_GEN_TAC `y:B` THEN REWRITE_TAC[moi_fsa_lconn; moi_fsa_lclosed] THEN
  X_GEN_TAC `Y:(B->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LC"))) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `t1:B->bool` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `?x:A. x IN UNIONS (d:(A->bool)->bool) /\ (y:B) = (f:A->B) x` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(t1:B->bool) IN IMAGE (IMAGE (f:A->B)) (d:(A->bool)->bool) /\ (y:B) IN t1` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `!t:A->bool. t IN d ==> ((f:A->B) x IN IMAGE f t <=> x IN t)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `x:A = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
      MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Y0 = {t:A->bool | t IN d /\ x IN t /\ IMAGE (f:A->B) t IN Y}` THEN
  SUBGOAL_THEN `Y0 = {t:A->bool | t IN d /\ x IN t}` ASSUME_TAC THENL
   [USE_THEN "LD" (MP_TAC o SPEC `x:A`) THEN REWRITE_TAC[moi_fsa_lconn; moi_fsa_lclosed] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Y0" THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      SUBGOAL_THEN `(t1:B->bool) IN IMAGE (IMAGE (f:A->B)) (d:(A->bool)->bool) /\ (f:A->B) x IN t1` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `t:A->bool` THEN
      EXPAND_TAC "Y0" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[IN_IMAGE]; ASM_MESON_TAC[]];
      MAP_EVERY X_GEN_TAC [`ta:A->bool`; `tb:A->bool`; `u:A`] THEN
      EXPAND_TAC "Y0" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "LC" (MATCH_MP_TAC o SPECL
        [`IMAGE (f:A->B) ta`; `IMAGE (f:A->B) tb`; `(f:A->B) u`]) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[];
        DISCH_TAC THEN UNDISCH_TAC `~(u:A = x)` THEN REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
        ASM_REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t':B->bool` THEN
  EQ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t:A->bool) IN Y0` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    EXPAND_TAC "Y0" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]]);;

let MOI_FSB_TR_DCONN = prove
 (`!(f:A->B) d.
     (!x y. x IN UNIONS d /\ y IN UNIONS d /\ f x = f y ==> x = y) /\
     moi_fsa_dconn d
     ==> moi_fsa_dconn (IMAGE (IMAGE f) d)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[moi_fsa_dconn] THEN DISCH_TAC THEN
  X_GEN_TAC `X:(B->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "XC"))) THEN
  ABBREV_TAC `X0 = {t:A->bool | t IN d /\ IMAGE (f:A->B) t IN X}` THEN
  SUBGOAL_THEN `X0:(A->bool)->bool = d` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "X0" THEN SET_TAC[];
      UNDISCH_TAC `~(X:(B->bool)->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `t':B->bool`) THEN
      SUBGOAL_THEN `(t':B->bool) IN IMAGE (IMAGE (f:A->B)) (d:(A->bool)->bool)` MP_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[IN_IMAGE]] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t:A->bool` THEN EXPAND_TAC "X0" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`ta:A->bool`; `tb:A->bool`; `e:A->bool`] THEN
      EXPAND_TAC "X0" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "XC" (MATCH_MP_TAC o SPECL
        [`IMAGE (f:A->B) ta`; `IMAGE (f:A->B) tb`; `IMAGE (f:A->B) e`]) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MOI_FSB_TR_INJ_ON THEN
        MAP_EVERY EXISTS_TAC [`d:(A->bool)->bool`; `ta:A->bool`] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `t:A->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t:A->bool) IN X0` MP_TAC THENL
   [ASM_REWRITE_TAC[]; EXPAND_TAC "X0" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]]);;

let MOI_FSB_TR_ECOUNT = prove
 (`!(f:A->B) d e.
     (!x y. x IN UNIONS d /\ y IN UNIONS d /\ f x = f y ==> x = y) /\ FINITE d /\
     e IN moi_fsa_edges d
     ==> CARD {t | t IN IMAGE (IMAGE f) d /\ IMAGE f e SUBSET t} =
         CARD {t | t IN d /\ e SUBSET t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e:A->bool) SUBSET UNIONS d` ASSUME_TAC THENL
   [UNDISCH_TAC `(e:A->bool) IN moi_fsa_edges d` THEN
    REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:A->B`; `d:(A->bool)->bool`; `e:A->bool`] MOI_FSB_TR_STAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MOI_FSB_TR_CARD THEN EXISTS_TAC `d:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[]]);;

let MOI_FSB_TR_SURF = prove
 (`!(f:A->B) d.
     (!x y. x IN UNIONS d /\ y IN UNIONS d /\ f x = f y ==> x = y) /\ moi_fsa_surf d
     ==> moi_fsa_surf (IMAGE (IMAGE f) d)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[moi_fsa_surf] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `d:(A->bool)->bool`] MOI_FSB_TR_EDGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `t:A->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSB_TR_INJ_ON THEN
      MAP_EVERY EXISTS_TAC [`d:(A->bool)->bool`; `t:A->bool`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `e:A->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:A->B`; `d:(A->bool)->bool`; `e:A->bool`] MOI_FSB_TR_ECOUNT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FSB_TR_LCONN THEN ASM_REWRITE_TAC[]]);;

let MOI_FSB_IN_BD = prove
 (`!(d:(A->bool)->bool) e.
     e IN moi_fsa_bd d <=> e IN moi_fsa_edges d /\ CARD {t | t IN d /\ e SUBSET t} = 1`,
  REWRITE_TAC[moi_fsa_bd; IN_ELIM_THM]);;

let MOI_FSB_TR_BD = prove
 (`!(f:A->B) d.
     (!x y. x IN UNIONS d /\ y IN UNIONS d /\ f x = f y ==> x = y) /\ FINITE d
     ==> moi_fsa_bd (IMAGE (IMAGE f) d) = IMAGE (IMAGE f) (moi_fsa_bd d)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `u:B->bool` THEN
  REWRITE_TAC[MOI_FSB_IN_BD] THEN
  MP_TAC(ISPECL [`f:A->B`; `d:(A->bool)->bool`] MOI_FSB_TR_EDGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `e:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:A->bool` THEN ASM_REWRITE_TAC[MOI_FSB_IN_BD] THEN
    UNDISCH_TAC `CARD {t | t IN IMAGE (IMAGE (f:A->B)) d /\ u SUBSET t} = 1` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:A->B`; `d:(A->bool)->bool`; `e:A->bool`] MOI_FSB_TR_ECOUNT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN SIMP_TAC[];
    GEN_REWRITE_TAC LAND_CONV [IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:A->bool` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
    REWRITE_TAC[MOI_FSB_IN_BD] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:A->B`; `d:(A->bool)->bool`; `e:A->bool`] MOI_FSB_TR_ECOUNT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let MOI_FSB_TR_GOOD = prove
 (`!(f:A->B) d s.
     (!x y. x IN UNIONS d /\ y IN UNIONS d /\ f x = f y ==> x = y) /\
     FINITE d /\ (!t. t IN d ==> FINITE t) /\ moi_fsa_good d s
     ==> moi_fsa_good (IMAGE (IMAGE f) d) (IMAGE (IMAGE f) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_good] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN UNIONS s /\ y IN UNIONS s /\ (f:A->B) x = f y ==> x = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (s:(A->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:A->bool. t IN s ==> FINITE t` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:A->B`; `s:(A->bool)->bool`] MOI_FSB_TR_BD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`f:A->B`; `s:(A->bool)->bool`] MOI_FSB_TR_EDGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY; GSYM IMAGE_UNIONS] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FSB_TR_DCONN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FSB_TR_LCONN THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `CARD (IMAGE (f:A->B) (UNIONS s)) = CARD (UNIONS s)` SUBST1_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[FINITE_UNIONS];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:A->B`; `s:(A->bool)->bool`; `s:(A->bool)->bool`] MOI_FSB_TR_CARD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`f:A->B`; `s:(A->bool)->bool`; `moi_fsa_edges (s:(A->bool)->bool)`]
      MOI_FSB_TR_CARD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FSA_EDGES_FINITE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[moi_fsa_edges; IN_ELIM_THM] THEN SET_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FSB_TR_POLY = prove
 (`!(f:A->real^M) s.
     moi_fsa_poly (IMAGE (IMAGE f) s) = UNIONS {convex hull (IMAGE f t) | t IN s}`,
  REWRITE_TAC[moi_fsa_poly] THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; EXISTS_IN_IMAGE] THEN MESON_TAC[]);;

(* The abstract complex of all nonempty faces of a family of triangles and  *)
(* its realization in real^5.                                                *)

let moi_fsb_faces = new_definition
 `moi_fsb_faces (d:(A->bool)->bool) = {u | ~(u = {}) /\ ?t. t IN d /\ u SUBSET t}`;;

let MOI_FSB_FACES = prove
 (`!d:(A->bool)->bool.
     FINITE d /\ (!t. t IN d ==> FINITE t)
     ==> FINITE (moi_fsb_faces d) /\ abstract_complex (moi_fsb_faces d) /\
         UNIONS (moi_fsb_faces d) = UNIONS d`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `UNIONS (IMAGE (\t:A->bool. {u | u SUBSET t}) d)` THEN CONJ_TAC THENL
     [REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[FINITE_POWERSET];
      REWRITE_TAC[moi_fsb_faces; SUBSET; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      MESON_TAC[]];
    REWRITE_TAC[abstract_complex; moi_fsb_faces; IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; MESON_TAC[SUBSET_TRANS]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[moi_fsb_faces; IN_UNIONS; IN_ELIM_THM] THEN
    EQ_TAC THENL [MESON_TAC[SUBSET]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{x:A}` THEN REWRITE_TAC[IN_SING; NOT_INSERT_EMPTY] THEN
    EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[SING_SUBSET]]);;

let MOI_FSB_REALIZE = prove
 (`!d:(A->bool)->bool.
     FINITE d /\ (!t. t IN d ==> t HAS_SIZE 3)
     ==> ?f:A->real^5. abstract_realizes f (moi_fsb_faces d)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t:A->bool. t IN d ==> FINITE t` ASSUME_TAC THENL
   [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
  MP_TAC(ISPEC `d:(A->bool)->bool` MOI_FSB_FACES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC ABSTRACT_REALIZES_EXISTS THEN EXISTS_TAC `2` THEN
  ASM_REWRITE_TAC[DIMINDEX_CONV `dimindex(:5)`] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[moi_fsb_faces; IN_ELIM_THM] THEN
  X_GEN_TAC `u:A->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `CARD (u:A->bool) <= CARD (t:A->bool)` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC[]; ASM_MESON_TAC[HAS_SIZE]]);;

let MOI_FSB_REAL_FACTS = prove
 (`!(f:A->real^M) d.
     FINITE d /\ (!t. t IN d ==> FINITE t) /\ abstract_realizes f (moi_fsb_faces d)
     ==> (!x y. x IN UNIONS d /\ y IN UNIONS d /\ f x = f y ==> x = y) /\
         (!t u. t IN d /\ u SUBSET t ==> ~affine_dependent (IMAGE f u)) /\
         (!t t' u u'. t IN d /\ t' IN d /\ u SUBSET t /\ u' SUBSET t'
                      ==> convex hull (IMAGE f u) INTER convex hull (IMAGE f u') =
                          convex hull (IMAGE f (u INTER u')))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `d:(A->bool)->bool` MOI_FSB_FACES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `abstract_realizes (f:A->real^M) (moi_fsb_faces d)` THEN
  ASM_REWRITE_TAC[abstract_realizes] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "R1") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R3"))) THEN
  SUBGOAL_THEN `!t u:A->bool. t IN d /\ u SUBSET t /\ ~(u = {}) ==> u IN moi_fsb_faces d`
  ASSUME_TAC THENL [REWRITE_TAC[moi_fsb_faces; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:A->bool`; `u:A->bool`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `u:A->bool = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; AFFINE_INDEPENDENT_EMPTY] THEN
    USE_THEN "R1" MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`t:A->bool`; `t':A->bool`; `u:A->bool`; `u':A->bool`] THEN
    STRIP_TAC THEN
    ASM_CASES_TAC `u:A->bool = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; INTER_EMPTY; CONVEX_HULL_EMPTY] THEN
    ASM_CASES_TAC `u':A->bool = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; INTER_EMPTY; CONVEX_HULL_EMPTY] THEN
    USE_THEN "R3" MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
     [EXISTS_TAC `t:A->bool`; EXISTS_TAC `t':A->bool`] THEN ASM_REWRITE_TAC[]]);;

let MOI_FSB_TR_GEOM = prove
 (`!(f:A->real^M) d.
     FINITE d /\ (!t. t IN d ==> FINITE t) /\ abstract_realizes f (moi_fsb_faces d)
     ==> moi_fsa_geom (IMAGE (IMAGE f) d)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_FSB_REAL_FACTS) THEN
  REWRITE_TAC[moi_fsa_geom; FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^M->bool`; `s':real^M->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `t':A->bool` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(s:real^M->bool) SUBSET IMAGE (f:A->real^M) t` THEN
  REWRITE_TAC[SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  UNDISCH_TAC `(s':real^M->bool) SUBSET IMAGE (f:A->real^M) t'` THEN
  REWRITE_TAC[SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `IMAGE (f:A->real^M) u INTER IMAGE f u' = IMAGE f (u INTER u')`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!(f:A->real^M) w s t. (!x y. x IN w /\ y IN w /\ f x = f y ==> x = y) /\
         s SUBSET w /\ t SUBSET w ==> IMAGE f s INTER IMAGE f t = IMAGE f (s INTER t)`) THEN
    EXISTS_TAC `UNIONS d:A->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`t:A->bool`; `t':A->bool`] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A realization f (in some real^M) of the closed capped surface:           *)
(* the realized c-part moi_fsb_rp, the realized boundary circles moi_fsb_rc *)
(* and the realized cones moi_fsb_rk, with their intersections.            *)
(* ------------------------------------------------------------------------- *)

let moi_fsb_rhyp = new_definition
 `moi_fsb_rhyp (f:real^N+(real^N->bool)->real^M) c <=>
    FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
    abstract_realizes f (moi_fsb_faces (moi_fsb_cap c (components (surface_boundary c))))`;;

let moi_fsb_rc = new_definition
 `moi_fsb_rc (f:real^N+(real^N->bool)->real^M) c J =
    UNIONS {convex hull (IMAGE f (IMAGE INL (moi_fsa_vs e))) |
            e IN moi_fsb_bedges c /\ e SUBSET J}`;;

let moi_fsb_rk = new_definition
 `moi_fsb_rk (f:real^N+(real^N->bool)->real^M) c J =
    UNIONS {convex hull (IMAGE f t) | t IN moi_fsb_cones c {J}}`;;

let moi_fsb_rp = new_definition
 `moi_fsb_rp (f:real^N+(real^N->bool)->real^M) c =
    UNIONS {convex hull (IMAGE f (IMAGE INL t)) | t IN moi_fsa_abs c}`;;

let MOI_FSB_IN_RC = prove
 (`!(f:real^N+(real^N->bool)->real^M) c J x.
     x IN moi_fsb_rc f c J <=>
     ?b. b IN moi_fsb_bedges c /\ b SUBSET J /\
         x IN convex hull (IMAGE f (IMAGE INL (moi_fsa_vs b)))`,
  REWRITE_TAC[moi_fsb_rc; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FSB_IN_RK = prove
 (`!(f:real^N+(real^N->bool)->real^M) c J x.
     x IN moi_fsb_rk f c J <=>
     ?b. b IN moi_fsb_bedges c /\ b SUBSET J /\
         x IN convex hull (IMAGE f (INR J INSERT IMAGE INL (moi_fsa_vs b)))`,
  REWRITE_TAC[moi_fsb_rk; moi_fsb_cones; IN_UNIONS; IN_ELIM_THM; IN_SING] THEN
  MESON_TAC[]);;

let MOI_FSB_IN_RP = prove
 (`!(f:real^N+(real^N->bool)->real^M) c x.
     x IN moi_fsb_rp f c <=>
     ?tr. tr IN c /\ aff_dim tr = &2 /\
          x IN convex hull (IMAGE f (IMAGE INL (moi_fsa_vs tr)))`,
  REWRITE_TAC[moi_fsb_rp; MOI_FSA_ABS_IMAGE; IN_UNIONS; IN_ELIM_THM; EXISTS_IN_IMAGE] THEN
  MESON_TAC[]);;

let MOI_FSB_RHYP = prove
 (`!(f:real^N+(real^N->bool)->real^M) c.
     moi_fsb_rhyp f c
     ==> FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ simplicial_complex c /\
         (!x y. x IN UNIONS (moi_fsb_cap c (components (surface_boundary c))) /\
                y IN UNIONS (moi_fsb_cap c (components (surface_boundary c))) /\
                f x = f y ==> x = y) /\
         (!t u. t IN moi_fsb_cap c (components (surface_boundary c)) /\ u SUBSET t
                ==> ~affine_dependent (IMAGE f u)) /\
         (!t t' u u'. t IN moi_fsb_cap c (components (surface_boundary c)) /\
                      t' IN moi_fsb_cap c (components (surface_boundary c)) /\
                      u SUBSET t /\ u' SUBSET t'
                      ==> convex hull (IMAGE f u) INTER convex hull (IMAGE f u') =
                          convex hull (IMAGE f (u INTER u')))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsb_rhyp] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FSB_REAL_FACTS THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `components (surface_boundary (c:(real^N->bool)->bool))`]
    MOI_FSB_CAP_BASIC) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN MESON_TAC[HAS_SIZE]);;

let MOI_FSB_OLD_IN = prove
 (`!(c:(real^N->bool)->bool) js tr.
     tr IN c /\ aff_dim tr = &2
     ==> IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr) IN moi_fsb_cap c js`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_FSB_IN_CAP] THEN DISJ1_TAC THEN
  EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_FSB_CONE_IN = prove
 (`!(c:(real^N->bool)->bool) js J b.
     J IN js /\ b IN moi_fsb_bedges c /\ b SUBSET J
     ==> (INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b) IN moi_fsb_cap c js`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_FSB_IN_CAP] THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`J:real^N->bool`; `b:real^N->bool`] THEN ASM_REWRITE_TAC[]);;

let MOI_FSB_INL_INTER = prove
 (`(!s t:real^N->bool.
      IMAGE (INL:real^N->real^N+(real^N->bool)) s INTER IMAGE INL t = IMAGE INL (s INTER t)) /\
   (!s t (J:real^N->bool).
      IMAGE (INL:real^N->real^N+(real^N->bool)) s INTER (INR J INSERT IMAGE INL t) =
      IMAGE INL (s INTER t)) /\
   (!s t (J:real^N->bool) J'.
      ~(J = J')
      ==> ((INR J:real^N+(real^N->bool)) INSERT IMAGE INL s) INTER
          (INR J' INSERT IMAGE INL t) = IMAGE INL (s INTER t))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_INSERT; IN_IMAGE] THEN
  X_GEN_TAC `z:real^N+(real^N->bool)` THEN
  STRUCT_CASES_TAC(ISPEC `z:real^N+(real^N->bool)` (cases "sum")) THEN
  REWRITE_TAC[injectivity "sum"; distinctness "sum"; GSYM(distinctness "sum");
              UNWIND_THM1; UNWIND_THM2] THEN
  ASM_MESON_TAC[]);;

(* Realized circles lie in the c-part and in their cones; the c-part meets *)
(* a cone exactly in its circle; different cones are disjoint.             *)

let MOI_FSB_RC_SUB = prove
 (`!(f:real^N+(real^N->bool)->real^M) c J.
     moi_fsb_rhyp f c /\ J IN components (surface_boundary c)
     ==> moi_fsb_rc f c J SUBSET moi_fsb_rp f c /\
         moi_fsb_rc f c J SUBSET moi_fsb_rk f c J`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP MOI_FSB_RHYP) ASSUME_TAC) THEN
  REWRITE_TAC[SUBSET; MOI_FSB_IN_RC; MOI_FSB_IN_RP; MOI_FSB_IN_RK] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^M` THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`] MOI_FSB_BEDGE_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^M) IN convex hull (IMAGE (f:real^N+(real^N->bool)->real^M) (IMAGE INL (moi_fsa_vs (b:real^N->bool))))` THEN
    MATCH_MP_TAC(SET_RULE `!s t (x:real^M). s SUBSET t ==> x IN s ==> x IN t`) THEN
    MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`; `tr:real^N->bool`]
      MOI_FSA_ABS_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^M) IN convex hull (IMAGE (f:real^N+(real^N->bool)->real^M) (IMAGE INL (moi_fsa_vs (b:real^N->bool))))` THEN
    MATCH_MP_TAC(SET_RULE `!s t (x:real^M). s SUBSET t ==> x IN s ==> x IN t`) THEN
    MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]);;

let MOI_FSB_RP_RK = prove
 (`!(f:real^N+(real^N->bool)->real^M) c J.
     moi_fsb_rhyp f c /\ J IN components (surface_boundary c)
     ==> moi_fsb_rp f c INTER moi_fsb_rk f c J = moi_fsb_rc f c J`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^M`; `c:(real^N->bool)->bool`;
                 `J:real^N->bool`] MOI_FSB_RC_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSB_RHYP) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[IN_INTER; MOI_FSB_IN_RP; MOI_FSB_IN_RK; MOI_FSB_IN_RC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(x:real^M) IN convex hull (IMAGE f (IMAGE INL (moi_fsa_vs tr) INTER
                    ((INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b))))`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL
     [`IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)`;
      `(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b)`;
      `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)`;
      `(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b)`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SUBSET_REFL; MOI_FSB_OLD_IN; MOI_FSB_CONE_IN];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[MOI_FSB_INL_INTER] THEN
    MATCH_MP_TAC(SET_RULE `!s t (x:real^M). s SUBSET t ==> x IN s ==> x IN t`) THEN
    MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]);;

let MOI_FSB_RK_DISJ = prove
 (`!(f:real^N+(real^N->bool)->real^M) c J J'.
     moi_fsb_rhyp f c /\ J IN components (surface_boundary c) /\
     J' IN components (surface_boundary c) /\ ~(J = J')
     ==> moi_fsb_rk f c J INTER moi_fsb_rk f c J' = {} /\
         moi_fsb_rk f c J INTER moi_fsb_rc f c J' = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^M`; `c:(real^N->bool)->bool`;
                 `J':real^N->bool`] MOI_FSB_RC_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!a b c:real^M->bool.
     a INTER b = {} /\ c SUBSET b ==> a INTER b = {} /\ a INTER c = {}`) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSB_RHYP) THEN
  SUBGOAL_THEN `(J:real^N->bool) INTER J' = {}` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPONENTS_NONOVERLAP]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTER; NOT_IN_EMPTY; MOI_FSB_IN_RK] THEN
  X_GEN_TAC `x:real^M` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `b':real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(x:real^M) IN convex hull (IMAGE f
       (((INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b)) INTER
        (INR J' INSERT IMAGE INL (moi_fsa_vs b'))))`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL
     [`(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b)`;
      `(INR J':real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b')`;
      `(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b)`;
      `(INR J':real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b')`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SUBSET_REFL; MOI_FSB_CONE_IN];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[IN_INTER];
    ASM_SIMP_TAC[MOI_FSB_INL_INTER] THEN
    SUBGOAL_THEN `moi_fsa_vs (b:real^N->bool) INTER moi_fsa_vs b' = {}`
      (fun th -> REWRITE_TAC[th; IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY]) THEN
    SUBGOAL_THEN `moi_fsa_vs (b:real^N->bool) SUBSET J /\ moi_fsa_vs (b':real^N->bool) SUBSET J'`
      MP_TAC THENL
     [REWRITE_TAC[SUBSET] THEN CONJ_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`; `y:real^N`]
          MOI_FSB_BEDGE_VS_IFF);
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b':real^N->bool`; `y:real^N`]
          MOI_FSB_BEDGE_VS_IFF)] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM SET_TAC[]]]);;

(* The polyhedron of a partial capping, and the boundary of the disk piece. *)

let MOI_FSB_PIECE_POLY = prove
 (`!(f:real^N+(real^N->bool)->real^M) c js.
     moi_fsa_poly (IMAGE (IMAGE f) (moi_fsb_cap c js)) =
     moi_fsb_rp f c UNION UNIONS {moi_fsb_rk f c J | J IN js}`,
  REWRITE_TAC[MOI_FSB_TR_POLY] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM; MOI_FSB_IN_RP; MOI_FSB_IN_CAP] THEN
  MESON_TAC[MOI_FSB_IN_RK]);;

let MOI_FSB_CAP_BD = prove
 (`!c js (e:real^N+(real^N->bool)->bool).
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     js SUBSET components (surface_boundary c)
     ==> (e IN moi_fsa_bd (moi_fsb_cap c js) <=>
          ?E. E IN moi_fsb_bedges c /\ ~(?J. J IN js /\ E SUBSET J) /\
              e = IMAGE INL (moi_fsa_vs E))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_FSB_IN_BD] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `js:(real^N->bool)->bool`;
                   `e:real^N+(real^N->bool)->bool`] MOI_FSB_CAP_EDGE_COUNT) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN(X_CHOOSE_THEN `E:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(e:real^N+(real^N->bool)->bool) IN moi_fsa_edges (moi_fsb_cap c js)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `js:(real^N->bool)->bool`;
                     `e:real^N+(real^N->bool)->bool`] MOI_FSB_CAP_EDGES) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISJ1_TAC THEN
      EXISTS_TAC `E:real^N->bool` THEN ASM_MESON_TAC[MOI_FSB_BEDGE_IN];
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `js:(real^N->bool)->bool`;
                     `e:real^N+(real^N->bool)->bool`] MOI_FSB_CAP_EDGE_COUNT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]]]);;

let MOI_FSB_PIECE_BD = prove
 (`!(f:real^N+(real^N->bool)->real^M) c J0.
     moi_fsb_rhyp f c /\ J0 IN components (surface_boundary c)
     ==> moi_fsa_poly (moi_fsa_bd (IMAGE (IMAGE f)
            (moi_fsb_cap c (components (surface_boundary c) DELETE J0)))) =
         moi_fsb_rc f c J0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSB_RHYP) THEN
  SUBGOAL_THEN `components (surface_boundary (c:(real^N->bool)->bool)) DELETE J0 SUBSET
                components (surface_boundary c)` ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fsb_cap c (components (surface_boundary c) DELETE J0) SUBSET
    moi_fsb_cap (c:(real^N->bool)->bool) (components (surface_boundary c))`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_fsb_cap; moi_fsb_cones] THEN
    MATCH_MP_TAC(SET_RULE `!a b c:(real^N+(real^N->bool)->bool)->bool.
      b SUBSET c ==> a UNION b SUBSET a UNION c`) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^M`;
                 `moi_fsb_cap c (components (surface_boundary c) DELETE (J0:real^N->bool))`]
    MOI_FSB_TR_BD) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ASM_MESON_TAC[MOI_FSB_CAP_BASIC]];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!E:real^N->bool. E IN moi_fsb_bedges c
      ==> (~(?J. J IN components (surface_boundary c) DELETE J0 /\ E SUBSET J) <=>
           E SUBSET J0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `E:real^N->bool`] MOI_FSB_BEDGE_COMPONENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[EXISTS_UNIQUE_THM; IN_DELETE]] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `JE:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_FSB_TR_POLY] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; MOI_FSB_IN_RC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `components (surface_boundary c) DELETE (J0:real^N->bool)`]
    MOI_FSB_CAP_BD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

(* The realized c-part is PL homeomorphic to UNIONS c (both realize the     *)
(* vertex sets of c), each boundary circle going onto its realized circle.  *)

let MOI_FSB_CIRCLE_UNIONS = prove
 (`!c J:real^N->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     J IN components (surface_boundary c)
     ==> J = UNIONS {e | e IN moi_fsb_bedges c /\ e SUBSET J}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN surface_boundary c` MP_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[MOI_FSB_SB_UNIONS; IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FSB_BEDGE_IN_CIRCLE THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MESON_TAC[SUBSET]]);;

let MOI_FSB_RP_PLH = prove
 (`!(f:real^N+(real^N->bool)->real^M) c.
     moi_fsb_rhyp f c
     ==> ?h h'. pl_homeomorphism (UNIONS c,moi_fsb_rp f c) (h,h') /\
                (!J. J IN components (surface_boundary c)
                     ==> IMAGE h J = moi_fsb_rc f c J)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSB_RHYP) THEN
  ABBREV_TAC `kc = moi_real_vertex_sets (c:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `FINITE (kc:(real^N->bool)->bool) /\ abstract_complex kc /\
                abstract_realizes (\x:real^N. x) kc`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "kc" THEN
    ASM_SIMP_TAC[MOI_REAL_VERTEX_SETS_FINITE; MOI_REAL_VERTEX_SETS_ABSTRACT_COMPLEX;
                 MOI_REAL_VERTEX_SETS_REALIZES];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^N->bool. u IN kc
                  ==> ?tr. tr IN c /\ aff_dim tr = &2 /\ u SUBSET moi_fsa_vs tr`
  (LABEL_TAC "KT") THENL
   [EXPAND_TAC "kc" THEN REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN
    X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `convex hull u:real^N->bool`] MOI_FSB_PURE) THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `convex hull u:real^N->bool`; `tr:real^N->bool`]
      MOI_FSA_ABS_SUB) THEN
    ASM_SIMP_TAC[MOI_FSA_VS_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u z:real^N. u IN kc /\ z IN u
      ==> (INL z:real^N+(real^N->bool)) IN
          UNIONS (moi_fsb_cap c (components (surface_boundary c)))`
  (LABEL_TAC "KU") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "KT" (MP_TAC o SPEC `u:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)` THEN
    ASM_SIMP_TAC[MOI_FSB_OLD_IN; MOI_FSB_INL_IMAGE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abstract_realizes ((f:real^N+(real^N->bool)->real^M) o INL) kc`
  ASSUME_TAC THENL
   [REWRITE_TAC[abstract_realizes; IMAGE_o] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "KT" (MP_TAC o SPEC `u:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `affine_dependent:(real^M->bool)->bool`)) (concl th))) THEN
      EXISTS_TAC `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)` THEN
      ASM_SIMP_TAC[MOI_FSB_OLD_IN; IMAGE_SUBSET];
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN REWRITE_TAC[o_THM; IN_UNIONS] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      SUBGOAL_THEN `(INL x:real^N+(real^N->bool)) = INL y` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> t = `UNIONS:((real^N+(real^N->bool)->bool)->bool)->
                                         real^N+(real^N->bool)->bool`)) (concl th) &&
          is_forall (concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "KU" MATCH_MP_TAC THEN
        ASM_MESON_TAC[];
        REWRITE_TAC[injectivity "sum"]];
      MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `v:real^N->bool`] THEN STRIP_TAC THEN
      USE_THEN "KT" (MP_TAC o SPEC `u:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "KT" (MP_TAC o SPEC `v:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `tr':real^N->bool` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[GSYM(CONJUNCT1 MOI_FSB_INL_INTER)] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 4)) THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)`;
                            `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr')`] THEN
      ASM_SIMP_TAC[MOI_FSB_OLD_IN; IMAGE_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (abstract_realization ((f:real^N+(real^N->bool)->real^M) o INL) kc) =
    moi_fsb_rp f c`
  ASSUME_TAC THENL
   [REWRITE_TAC[abstract_realization; UNIONS_INSERT; UNION_EMPTY] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^M` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; MOI_FSB_IN_RP; IMAGE_o] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      USE_THEN "KT" (MP_TAC o SPEC `u:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^M) IN s` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!s t (x:real^M). s SUBSET t ==> x IN s ==> x IN t`) THEN
      MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `convex hull (IMAGE (f:real^N+(real^N->bool)->real^M)
                                (IMAGE INL (moi_fsa_vs tr)))` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `moi_fsa_vs (tr:real^N->bool)` THEN
      REWRITE_TAC[] THEN EXPAND_TAC "kc" THEN REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN
      SUBGOAL_THEN `~(moi_fsa_vs (tr:real^N->bool) = {})` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tr:real^N->bool`; `2`] MOI_FSA_VS_SIZE) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[HAS_SIZE] THEN MESON_TAC[CARD_CLAUSES; ARITH_RULE `~(0 = 3)`];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tr:real^N->bool`] MOI_FSA_VS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; GSYM(CONJUNCT1(CONJUNCT2 th))]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. x`; `(f:real^N+(real^N->bool)->real^M) o INL`;
                 `kc:(real^N->bool)->bool`] ABSTRACT_REALIZATIONS_PL_HOMEOMORPHIC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `UNIONS (abstract_realization (\x:real^N. x) kc) = UNIONS c`
  SUBST1_TAC THENL [EXPAND_TAC "kc" THEN ASM_SIMP_TAC[MOI_REAL_VERTEX_SETS_UNIONS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^M` (X_CHOOSE_THEN `h':real^M->real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^M`; `h':real^M->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `J:real^N->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `J:real^N->bool`] MOI_FSB_CIRCLE_UNIONS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[IMAGE_UNIONS; moi_fsb_rc] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^M->bool` THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `!e:real^N->bool. e IN moi_fsb_bedges c
      ==> IMAGE (h:real^N->real^M) e =
          convex hull (IMAGE (f:real^N+(real^N->bool)->real^M) (IMAGE INL (moi_fsa_vs e)))`
  (fun th -> MESON_TAC[th]) THEN
  X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSA_VS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_FSB_BEDGE_IN]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CONJUNCT1(CONJUNCT2 th)]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `moi_fsa_vs (e:real^N->bool)` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> t = `IMAGE:(real^N->real^M)->(real^N->bool)->real^M->bool`))
        (concl th))) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "kc" THEN REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSA_VS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_FSB_BEDGE_IN]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2 th))]) THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSB_BEDGE_BASIC) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[HAS_SIZE; CARD_CLAUSES; ARITH_RULE `~(0 = 2)`];
      ASM_MESON_TAC[MOI_FSB_BEDGE_IN]];
    REWRITE_TAC[IMAGE_ID; IMAGE_o] THEN SIMP_TAC[]]);;

(* The cone over a PL circle from a point seeing it injectively is a 2-cell *)
(* bounded by the circle (the boundary version of PL_BALL_CONE).            *)

let MOI_FSB_CONE_CELL = prove
 (`!(s:real^N->bool) v.
     pl_sphere 1 s /\ ~(v IN s) /\
     (!x y. x IN s /\ y IN s /\ y IN segment[v,x] ==> y = x)
     ==> pl_cell_with_boundary 2 (UNIONS {segment[v,x] | x IN s}) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
     (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC)))
   STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`relative_frontier k:real^N->bool`; `s:real^N->bool`;
                 `simplex_barycentre (k:real^N->bool)`; `v:real^N`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`k:real^N->bool`;
    `moi_con_conemap (relative_frontier k) (simplex_barycentre k) (v:real^N)
                     (f:real^N->real^N)`;
    `moi_con_conemap (s:real^N->bool) (v:real^N)
                     (simplex_barycentre (k:real^N->bool)) (g:real^N->real^N)`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (f:real^N->real^N) (relative_frontier k)` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism];
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]]);;

(* A realized cone is a 2-cell bounded by its realized circle. *)

let MOI_FSB_RK_CELL = prove
 (`!(f:real^N+(real^N->bool)->real^M) c J.
     moi_fsb_rhyp f c /\ J IN components (surface_boundary c) /\
     pl_sphere 1 (moi_fsb_rc f c J)
     ==> pl_cell_with_boundary 2 (moi_fsb_rk f c J) (moi_fsb_rc f c J)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSB_RHYP) THEN
  ABBREV_TAC `a = (f:real^N+(real^N->bool)->real^M) (INR J)` THEN
  SUBGOAL_THEN
   `!b:real^N->bool. b IN moi_fsb_bedges c
      ==> convex hull (IMAGE (f:real^N+(real^N->bool)->real^M)
                         (INR J INSERT IMAGE INL (moi_fsa_vs b))) =
          UNIONS {segment[a,x] | x IN convex hull (IMAGE f (IMAGE INL (moi_fsa_vs b)))}`
  (LABEL_TAC "CS") THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_INSERT_SEGMENTS] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^N+(real^N->bool)->real^M)
                       (IMAGE INL (moi_fsa_vs (b:real^N->bool))) = {}` THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`] MOI_FSB_BEDGE_BASIC) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[HAS_SIZE; CARD_CLAUSES; ARITH_RULE `~(0 = 2)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((a:real^M) IN moi_fsb_rc (f:real^N+(real^N->bool)->real^M) c J)` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_FSB_IN_RC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPECL
     [`(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b)`;
      `(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b)`;
      `{INR J:real^N+(real^N->bool)}`;
      `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs b)`] o
      check (fun th -> is_forall (concl th) &&
                       length(fst(strip_forall(concl th))) = 4)) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[MOI_FSB_CONE_IN] THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `{INR J:real^N+(real^N->bool)} INTER IMAGE INL (moi_fsa_vs b) = {}`
    SUBST1_TAC THENL
     [REWRITE_TAC[SET_RULE `!a:real^N+(real^N->bool) s. {a} INTER s = {} <=> ~(a IN s)`;
                  MOI_FSB_INL_IMAGE];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; CONVEX_HULL_SING] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^M`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fsb_rk (f:real^N+(real^N->bool)->real^M) c J = UNIONS {segment[a:real^M,x] | x IN moi_fsb_rc (f:real^N+(real^N->bool)->real^M) c J}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^M` THEN
    REWRITE_TAC[MOI_FSB_IN_RK; IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(z:real^M) IN convex hull (IMAGE (f:real^N+(real^N->bool)->real^M)
                                        (INR J INSERT IMAGE INL (moi_fsa_vs b)))` THEN
      USE_THEN "CS" (fun th -> ASM_SIMP_TAC[th]) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      EXISTS_TAC `t:real^M->bool` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:real^M` THEN
      ASM_REWRITE_TAC[MOI_FSB_IN_RC] THEN EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      UNDISCH_TAC `(x:real^M) IN moi_fsb_rc (f:real^N+(real^N->bool)->real^M) c J` THEN REWRITE_TAC[MOI_FSB_IN_RC] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "CS" (fun th -> ASM_SIMP_TAC[th]) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `t:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FSB_CONE_CELL THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN
  REWRITE_TAC[MOI_FSB_IN_RC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `b1:real^N->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `b2:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(y:real^M) IN convex hull (IMAGE (f:real^N+(real^N->bool)->real^M) (IMAGE INL (moi_fsa_vs (b1:real^N->bool))))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(y:real^M) IN convex hull (IMAGE f (IMAGE INL (moi_fsa_vs b2) INTER
         ((INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b1))))`
    MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL
       [`(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b2)`;
        `(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b1)`;
        `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs b2)`;
        `(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b1)`] o
        check (fun th -> is_forall (concl th) &&
                         length(fst(strip_forall(concl th))) = 4)) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[MOI_FSB_CONE_IN] THEN SET_TAC[];
                      DISCH_THEN(SUBST1_TAC o SYM)] THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `(y:real^M) IN segment[a,x]` THEN
      MATCH_MP_TAC(SET_RULE `!s t (y:real^M). s SUBSET t ==> y IN s ==> y IN t`) THEN
      MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HULL_INC THEN EXPAND_TAC "a" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[IN_INSERT];
        UNDISCH_TAC `(x:real^M) IN convex hull (IMAGE (f:real^N+(real^N->bool)->real^M)
                                          (IMAGE INL (moi_fsa_vs (b1:real^N->bool))))` THEN
        MATCH_MP_TAC(SET_RULE `!s t (y:real^M). s SUBSET t ==> y IN s ==> y IN t`) THEN
        MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
      REWRITE_TAC[MOI_FSB_INL_INTER] THEN
      MATCH_MP_TAC(SET_RULE `!s t (y:real^M). s SUBSET t ==> y IN s ==> y IN t`) THEN
      MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((a:real^M) IN affine hull (IMAGE (f:real^N+(real^N->bool)->real^M) (IMAGE INL (moi_fsa_vs (b1:real^N->bool)))))`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL
     [`(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b1)`;
      `(INR J:real^N+(real^N->bool)) INSERT IMAGE INL (moi_fsa_vs b1)`] o
      check (fun th -> is_forall (concl th) &&
                       length(fst(strip_forall(concl th))) = 2 &&
                       can (find_term (fun t -> t = `affine_dependent:(real^M->bool)->bool`))
                           (concl th))) THEN
    ASM_SIMP_TAC[MOI_FSB_CONE_IN; SUBSET_REFL; IMAGE_CLAUSES] THEN
    REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `a:real^M` THEN REWRITE_TAC[IN_INSERT] THEN
    SUBGOAL_THEN
     `((a:real^M) INSERT IMAGE (f:real^N+(real^N->bool)->real^M) (IMAGE INL (moi_fsa_vs (b1:real^N->bool)))) DELETE a =
      IMAGE f (IMAGE INL (moi_fsa_vs b1))`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(SET_RULE `!a:real^M s. ~(a IN s) ==> (a INSERT s) DELETE a = s`) THEN
    UNDISCH_TAC `~((a:real^M) IN moi_fsb_rc (f:real^N+(real^N->bool)->real^M) c J)` THEN
    REWRITE_TAC[MOI_FSB_IN_RC; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `b1:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[HULL_INC];
    ALL_TAC] THEN
  UNDISCH_TAC `(y:real^M) IN segment[a,x]` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `s = &1` THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC
   `~((a:real^M) IN affine hull (IMAGE (f:real^N+(real^N->bool)->real^M) (IMAGE INL (moi_fsa_vs (b1:real^N->bool)))))` THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  SUBGOAL_THEN `inv(&1 - s) * (&1 - s) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN
    REWRITE_TAC[REAL_ARITH `&1 - s = &0 <=> s = &1`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^M) = inv(&1 - s) % y + (--(inv(&1 - s) * s)) % x` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (f:real^N+(real^N->bool)->real^M) (IMAGE INL (moi_fsa_vs b1))`
    AFFINE_AFFINE_HULL) THEN
  REWRITE_TAC[affine] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET];
    ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET];
    REWRITE_TAC[REAL_ARITH `a + --(a * s) = a * (&1 - s)`] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The disk piece.  When chi = 1 - k and there are k + 1 boundary           *)
(* circles, capping all circles but J0 gives a good piece of the closed     *)
(* capped surface; realized, it is a PL disk bounded by the circle of J0.  *)
(* ------------------------------------------------------------------------- *)

let MOI_FSB_CAP_MONO = prove
 (`!c js js':(real^N->bool)->bool.
     js SUBSET js' ==> moi_fsb_cap c js SUBSET moi_fsb_cap c js'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fsb_cap; moi_fsb_cones] THEN
  MATCH_MP_TAC(SET_RULE `!a b c:(real^N+(real^N->bool)->bool)->bool.
      b SUBSET c ==> a UNION b SUBSET a UNION c`) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET]);;

let MOI_FSB_CAP_NONEMPTY = prove
 (`!c js:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ ~(UNIONS c = {})
     ==> ~(moi_fsb_cap c js = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `~(UNIONS c:real^N->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:real^N`; `s:real^N->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FSB_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs tr)` THEN
  ASM_SIMP_TAC[MOI_FSB_OLD_IN]);;

let MOI_FSB_PIECE_GOOD = prove
 (`!c (J0:real^N->bool) k.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ connected (UNIONS c) /\
     ~(UNIONS c = {}) /\ J0 IN components (surface_boundary c) /\
     CARD (components (surface_boundary c)) = k + 1 /\ complex_euler c = &1 - &k
     ==> moi_fsa_good (moi_fsb_cap c (components (surface_boundary c)))
                      (moi_fsb_cap c (components (surface_boundary c) DELETE J0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fsa_good] THEN
  SUBGOAL_THEN `components (surface_boundary (c:(real^N->bool)->bool)) DELETE J0 SUBSET
                components (surface_boundary c)` ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FSB_CAP_MONO THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FSB_CAP_NONEMPTY THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FSB_CAP_DCONN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FSB_CAP_LCONN THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `J0:real^N->bool`] MOI_FSB_CIRCLE_EDGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `IMAGE (INL:real^N->real^N+(real^N->bool)) (moi_fsa_vs b)` THEN
    ASM_SIMP_TAC[MOI_FSB_CAP_BD] THEN EXISTS_TAC `b:real^N->bool` THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `J:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`] MOI_FSB_BEDGE_COMPONENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[EXISTS_UNIQUE_THM]] THEN
    ASM_MESON_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                   `components (surface_boundary c) DELETE (J0:real^N->bool)`]
      MOI_FSB_CAP_EULER) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `CARD (components (surface_boundary (c:(real^N->bool)->bool)) DELETE J0) = k`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[CARD_DELETE; MOI_FSB_BD_CIRCLES] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_EQ] THEN REAL_ARITH_TAC]);;

(* The realized disk piece: a PL disk (moi_fsa_disk: a 2-simplex in real^2 *)
(* mapped onto it) bounded by the realized circle of J0.                    *)

let MOI_FSB_PIECE_DISK = prove
 (`!(f:real^N+(real^N->bool)->real^M) c J0 k.
     moi_fsb_rhyp f c /\ connected (UNIONS c) /\ ~(UNIONS c = {}) /\
     J0 IN components (surface_boundary c) /\
     CARD (components (surface_boundary c)) = k + 1 /\ complex_euler c = &1 - &k
     ==> moi_fsa_disk (moi_fsb_rp f c UNION
                       UNIONS {moi_fsb_rk f c J | J |
                               J IN components (surface_boundary c) DELETE J0})
                      (moi_fsb_rc f c J0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSB_RHYP) THEN
  MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^M`; `c:(real^N->bool)->bool`;
                 `components (surface_boundary c) DELETE (J0:real^N->bool)`]
    MOI_FSB_PIECE_POLY) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^M`; `c:(real^N->bool)->bool`;
                 `J0:real^N->bool`] MOI_FSB_PIECE_BD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MOI_FSA_DISK_PIECE THEN
  EXISTS_TAC `IMAGE (IMAGE (f:real^N+(real^N->bool)->real^M))
                    (moi_fsb_cap c (components (surface_boundary c)))` THEN
  SUBGOAL_THEN
   `FINITE (moi_fsb_cap c (components (surface_boundary (c:(real^N->bool)->bool)))) /\
    (!t. t IN moi_fsb_cap c (components (surface_boundary c)) ==> FINITE t)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                   `components (surface_boundary (c:(real^N->bool)->bool))`]
      MOI_FSB_CAP_BASIC) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN MESON_TAC[HAS_SIZE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FSB_TR_SURF THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ASM_SIMP_TAC[MOI_FSB_CAP_SURF]];
    MATCH_MP_TAC MOI_FSB_TR_GEOM THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[moi_fsb_rhyp];
    MATCH_MP_TAC MOI_FSB_TR_GOOD THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FSB_PIECE_GOOD THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]]]);;

(* Planar cells are filled circles. *)

let MOI_FSB_PLANE_CELL = prove
 (`!d j:real^2->bool.
     pl_cell_with_boundary 2 d j
     ==> d = j UNION inside j /\ interior d = inside j /\ pl_sphere 1 j /\
         j SUBSET d /\ compact d /\ frontier d = j`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_S5C_PLANE_CELL_FACTS) THEN
  MP_TAC(ISPECL [`d:real^2->bool`; `j:real^2->bool`] MOI_S5C_PLANE_FILL) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Planar tools. Polygons with interior as filled PL circles, and the        *)
(* exchange of two polygons inside a third one by a PL homeomorphism of the  *)
(* plane fixed off the interior of the third (annuli with prescribed outer   *)
(* boundary, MOI_S5C_ANN_OUTER, plus cell extension inside).                 *)
(* ------------------------------------------------------------------------- *)

(* Planar 2-simplices. *)

let MOI_FSB_SIMPLEX2 = prove
 (`!k0:real^2->bool.
     &2 simplex k0
     ==> relative_frontier k0 = frontier k0 /\ k0 DIFF relative_frontier k0 = interior k0 /\
         compact k0 /\ convex k0 /\ ~(interior k0 = {})`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `affine hull (k0:real^2->bool) = (:real^2)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_2] THEN ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (k0:real^2->bool) /\ convex k0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_FRONTIER] THEN
  REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
  CONJ_TAC THENL [MP_TAC(ISPEC `k0:real^2->bool` INTERIOR_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM RELATIVE_INTERIOR_INTERIOR; RELATIVE_INTERIOR_EQ_EMPTY] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `&2 simplex ({}:real^2->bool)` THEN REWRITE_TAC[SIMPLEX_EMPTY] THEN
  INT_ARITH_TAC);;

let MOI_FSB_POLY2 = prove
 (`!P:real^2->bool.
     polytope P /\ ~(interior P = {})
     ==> pl_cell_with_boundary 2 P (relative_frontier P) /\
         P = relative_frontier P UNION inside (relative_frontier P) /\
         interior P = inside (relative_frontier P) /\
         pl_sphere 1 (relative_frontier P) /\
         relative_frontier P = P DIFF interior P /\
         compact P /\ convex P /\ relative_frontier P SUBSET P`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 P (relative_frontier P:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5C_POLYTOPE_CELL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSB_PLANE_CELL) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `frontier P = relative_frontier (P:real^2->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[frontier] THEN
    SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED; ASSUME `compact (P:real^2->bool)`];
    FIRST_ASSUM ACCEPT_TAC;
    SIMP_TAC[POLYTOPE_IMP_CONVEX; ASSUME `polytope (P:real^2->bool)`];
    FIRST_ASSUM ACCEPT_TAC]);;

let MOI_FSB_POLY_ANN = prove
 (`!R P:real^2->bool.
     polytope R /\ polytope P /\ ~(interior P = {}) /\ P SUBSET interior R
     ==> pl_annulus_with_ends (R DIFF interior P) (relative_frontier P)
                              (relative_frontier R)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(interior R:real^2->bool = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `P:real^2->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `R:real^2->bool` MOI_FSB_POLY2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "R1" (el 1 cs) THEN LABEL_TAC "R2" (el 2 cs) THEN ASSUME_TAC(el 3 cs)) THEN
  MP_TAC(ISPEC `P:real^2->bool` MOI_FSB_POLY2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "P2" (el 2 cs) THEN ASSUME_TAC(el 3 cs) THEN ASSUME_TAC(el 7 cs)) THEN
  MP_TAC(ISPECL [`relative_frontier P:real^2->bool`; `relative_frontier R:real^2->bool`]
    MOI_S5C_ANN2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "R2" (SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "R1" (fun th -> REWRITE_TAC[GSYM th]) THEN
  USE_THEN "P2" (fun th -> REWRITE_TAC[GSYM th]));;

(* Instantiate the labelled polygon facts "PF" at a polygon with interior. *)

let MOI_FSB_PF_TAC tm =
  USE_THEN "PF" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME (mk_comb(`polytope:(real^2->bool)->bool`,tm)))
          (ASSUME (mk_neg(mk_eq(mk_comb(`interior:(real^2->bool)->real^2->bool`,tm),
                                `{}:real^2->bool`)))))));;

let MOI_FSB_POLY_SWAP = prove
 (`!R A B:real^2->bool.
     polytope R /\ polytope A /\ polytope B /\
     ~(interior A = {}) /\ ~(interior B = {}) /\
     A SUBSET interior R /\ B SUBSET interior R
     ==> ?h g. pl_homeomorphism ((:real^2),(:real^2)) (h,g) /\
               (!x. ~(x IN interior R) ==> h x = x) /\ IMAGE h A = B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(interior R:real^2->bool = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `A:real^2->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!P:real^2->bool. polytope P /\ ~(interior P = {})
      ==> pl_cell_with_boundary 2 P (relative_frontier P) /\
          pl_sphere 1 (relative_frontier P) /\ closed P /\
          relative_frontier P = P DIFF interior P`
  (LABEL_TAC "PF") THENL
   [GEN_TAC THEN STRIP_TAC THEN MP_TAC(ISPEC `P:real^2->bool` MOI_FSB_POLY2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> let cs = CONJUNCTS th in
      REPEAT CONJ_TAC THENL
       [ACCEPT_TAC (el 0 cs); ACCEPT_TAC (el 3 cs);
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN ACCEPT_TAC (el 5 cs);
        ACCEPT_TAC (el 4 cs)]);
    ALL_TAC] THEN
  MOI_FSB_PF_TAC `R:real^2->bool` THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "RS" (el 1 cs) THEN LABEL_TAC "RCL" (el 2 cs)) THEN
  MOI_FSB_PF_TAC `A:real^2->bool` THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "AC" (el 0 cs) THEN LABEL_TAC "AS" (el 1 cs) THEN
    LABEL_TAC "ACL" (el 2 cs)) THEN
  MOI_FSB_PF_TAC `B:real^2->bool` THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "BC" (el 0 cs) THEN LABEL_TAC "BS" (el 1 cs) THEN
    LABEL_TAC "BCL" (el 2 cs)) THEN
  (* the annulus R minus the open A *)
  MP_TAC(ISPECL [`R:real^2->bool`; `A:real^2->bool`] MOI_FSB_POLY_ANN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[pl_annulus_with_ends]] THEN
  DISCH_THEN(X_CHOOSE_THEN `fa:real^2->real^2` (X_CHOOSE_THEN `ga:real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "FA1") (LABEL_TAC "FA2"))))) THEN
  MP_TAC(CONJUNCT1(REWRITE_RULE[pl_homeomorphism] (ASSUME
   `pl_homeomorphism
     (interval[--vector[&2;&2],vector[&2;&2]] DIFF
      interval(--vector[&1;&1],vector[&1;&1]):real^2->bool,R DIFF interior A)
     (fa:real^2->real^2,ga)`))) THEN
  REWRITE_TAC[homeomorphism] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    LABEL_TAC "GFA" (el 0 cs) THEN LABEL_TAC "IFA" (el 1 cs) THEN
    LABEL_TAC "FGA" (el 3 cs)) THEN
  SUBGOAL_THEN
   `relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]) SUBSET
    interval[--vector[&2;&2],vector[&2;&2]] DIFF
    interval(--vector[&1;&1],vector[&1;&1]):real^2->bool /\
    relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]) SUBSET
    interval[--vector[&2;&2],vector[&2;&2]] DIFF
    interval(--vector[&1;&1],vector[&1;&1]):real^2->bool`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; MOI_S5C_IN_SQI; MOI_S5C_IN_SQO] THEN
    SIMP_TAC[MOI_S5C_SQ_RF; REAL_ARITH `&0 < &2 /\ &0 < &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism
      (relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]):real^2->bool,
       relative_frontier R) (fa:real^2->real^2,ga)`
  ASSUME_TAC THENL
   [USE_THEN "FA2" SUBST1_TAC THEN MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC
     [`interval[--vector[&2;&2],vector[&2;&2]] DIFF
       interval(--vector[&1;&1],vector[&1;&1]):real^2->bool`;
      `R DIFF interior A:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_S5C_SQ_RF_POLYHEDRON THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the annulus R minus the open B, with the same outer parametrization *)
  MP_TAC(ISPECL [`R DIFF interior B:real^2->bool`; `relative_frontier B:real^2->bool`;
                 `relative_frontier R:real^2->bool`; `fa:real^2->real^2`; `ga:real^2->real^2`]
    MOI_S5C_ANN_OUTER) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSB_POLY_ANN THEN ASM_REWRITE_TAC[]; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fb:real^2->real^2` (X_CHOOSE_THEN `gb:real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "FBA")
      (CONJUNCTS_THEN2 (LABEL_TAC "FB1") (LABEL_TAC "FB2")))))) THEN
  (* the annulus homeomorphism, the identity on the frontier of R *)
  SUBGOAL_THEN
   `pl_homeomorphism (R DIFF interior A,R DIFF interior B)
                     ((fb:real^2->real^2) o (ga:real^2->real^2),(fa:real^2->real^2) o (gb:real^2->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[--vector[&2;&2],vector[&2;&2]] DIFF
                interval(--vector[&1;&1],vector[&1;&1]):real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. y IN relative_frontier R ==> ((fb:real^2->real^2) o ga) y = y`
  (LABEL_TAC "F1R") THENL
   [GEN_TAC THEN USE_THEN "FA2" SUBST1_TAC THEN REWRITE_TAC[IN_IMAGE; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(ga:real^2->real^2) (fa x) = x` SUBST1_TAC THENL
     [USE_THEN "GFA" MATCH_MP_TAC THEN ASM SET_TAC[];
      USE_THEN "FBA" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((fb:real^2->real^2) o (ga:real^2->real^2)) (relative_frontier A) =
    relative_frontier B`
  ASSUME_TAC THENL
   [USE_THEN "FA1" SUBST1_TAC THEN USE_THEN "FB1" SUBST1_TAC THEN
    REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^2->real^2) g p t.
       (!x. x IN p ==> g (f x) = x) /\ t SUBSET p ==> IMAGE g (IMAGE f t) = t`) THEN
    EXISTS_TAC `interval[--vector[&2;&2],vector[&2;&2]] DIFF
                interval(--vector[&1;&1],vector[&1;&1]):real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "GFA" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(R DIFF interior A) INTER A = relative_frontier (A:real^2->bool) /\
                (R DIFF interior B) INTER B = relative_frontier (B:real^2->bool) /\
                (R DIFF interior A) UNION A = R /\ (R DIFF interior B) UNION B = R`
  STRIP_ASSUME_TAC THENL
   [MOI_FSB_PF_TAC `A:real^2->bool` THEN DISCH_THEN(SUBST1_TAC o last o CONJUNCTS) THEN
    MOI_FSB_PF_TAC `B:real^2->bool` THEN DISCH_THEN(SUBST1_TAC o last o CONJUNCTS) THEN
    MP_TAC(ISPEC `R:real^2->bool` INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `A:real^2->bool` INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `B:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(A:real^2->bool) SUBSET interior R` THEN
    UNDISCH_TAC `(B:real^2->bool) SUBSET interior R` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier A,relative_frontier B)
      ((fb:real^2->real^2) o (ga:real^2->real^2),(fa:real^2->real^2) o (gb:real^2->real^2))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE ((fb:real^2->real^2) o (ga:real^2->real^2)) (relative_frontier A) =
                  relative_frontier B`)) THEN
    MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`R DIFF interior A:real^2->bool`; `R DIFF interior B:real^2->bool`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(R DIFF interior A) INTER A = relative_frontier (A:real^2->bool)` THEN
      SET_TAC[];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `1` THEN
      USE_THEN "AS" ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `A:real^2->bool`; `relative_frontier A:real^2->bool`;
                 `B:real^2->bool`; `relative_frontier B:real^2->bool`;
                 `(fb:real^2->real^2) o (ga:real^2->real^2)`;
                 `(fa:real^2->real^2) o (gb:real^2->real^2)`] MOI_S5C_CELL_EXT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^2` (X_CHOOSE_THEN `g2:real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F2A")))) THEN
  MP_TAC(ISPECL [`R DIFF interior A:real^2->bool`; `A:real^2->bool`;
                 `R DIFF interior B:real^2->bool`; `B:real^2->bool`;
                 `(fb:real^2->real^2) o (ga:real^2->real^2)`;
                 `(fa:real^2->real^2) o (gb:real^2->real^2)`;
                 `f2:real^2->real^2`; `g2:real^2->real^2`] MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[OPEN_INTERIOR] THEN USE_THEN "RCL" ACCEPT_TAC;
      USE_THEN "ACL" ACCEPT_TAC;
      MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[OPEN_INTERIOR] THEN USE_THEN "RCL" ACCEPT_TAC;
      USE_THEN "BCL" ACCEPT_TAC;
      UNDISCH_TAC `(R DIFF interior A) INTER A = relative_frontier (A:real^2->bool)` THEN
      DISCH_THEN SUBST1_TAC THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "F2A" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(R DIFF interior A) INTER A = relative_frontier (A:real^2->bool)` THEN
      UNDISCH_TAC `(R DIFF interior B) INTER B = relative_frontier (B:real^2->bool)` THEN
      REPEAT(DISCH_THEN SUBST1_TAC) THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(R DIFF interior A) UNION A = (R:real^2->bool)` THEN
  UNDISCH_TAC `(R DIFF interior B) UNION B = (R:real^2->bool)` THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN DISCH_TAC THEN
  ABBREV_TAC `Fu = \x:real^2. if x IN R DIFF interior A then ((fb:real^2->real^2) o ga) x
                              else (f2:real^2->real^2) x` THEN
  ABBREV_TAC `Gu = \y:real^2. if y IN R DIFF interior B then ((fa:real^2->real^2) o gb) y
                              else (g2:real^2->real^2) y` THEN
  SUBGOAL_THEN `!x:real^2. x IN R /\ ~(x IN interior R) ==> (Fu:real^2->real^2) x = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN EXPAND_TAC "Fu" THEN
    SUBGOAL_THEN `(x:real^2) IN R DIFF interior A` (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(ISPEC `A:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(A:real^2->bool) SUBSET interior R` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "F1R" MATCH_MP_TAC THEN
    MOI_FSB_PF_TAC `R:real^2->bool` THEN DISCH_THEN(SUBST1_TAC o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R:real^2->bool`; `Fu:real^2->real^2`; `Gu:real^2->real^2`]
    MOI_SA2_PLH_EXTEND_ID) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^2. if x IN R then (Fu:real^2->real^2) x else x`;
    `\x:real^2. if x IN R then (Gu:real^2->real^2) x else x`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `Fu:real^2->real^2`)) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f2:real^2->real^2) A = B` (SUBST1_TAC o SYM) THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!f g:real^2->real^2 s. (!x. x IN s ==> f x = g x)
                          ==> IMAGE f s = IMAGE g s`) THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN R` (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ISPEC `R:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(A:real^2->bool) SUBSET interior R` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "Fu" THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN USE_THEN "F2A" MATCH_MP_TAC THEN
  UNDISCH_TAC `(R DIFF interior A) INTER A = relative_frontier (A:real^2->bool)` THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Ambient moves.  moi_fsb_amb w a b: some PL homeomorphism of the          *)
(* plane fixed off w maps a onto b (an equivalence relation); polygons have *)
(* polygon neighbourhoods inside any open superset; small squares.          *)
(* ------------------------------------------------------------------------- *)

let moi_fsb_amb = new_definition
 `moi_fsb_amb (w:real^2->bool) (a:real^2->bool) (b:real^2->bool) <=>
    ?h g. pl_homeomorphism ((:real^2),(:real^2)) (h,g) /\
          (!x. ~(x IN w) ==> h x = x) /\ IMAGE h a = b`;;

let MOI_FSB_AMB_REFL = prove
 (`!w a:real^2->bool. moi_fsb_amb w a a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsb_amb] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^2. x`; `\x:real^2. x`] THEN
  REWRITE_TAC[MOI_SA2_PLH_ID; IMAGE_ID]);;

let MOI_FSB_AMB_SYM = prove
 (`!w a b:real^2->bool. moi_fsb_amb w a b ==> moi_fsb_amb w b a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsb_amb] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`g:real^2->real^2`; `h:real^2->real^2`] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^2->real^2`; `g:real^2->real^2`; `w:real^2->bool`;
                 `{}:real^2->bool`] MOI_SA2_FIX_OFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SA2_PLH_UNIV) THEN
  UNDISCH_TAC `IMAGE (h:real^2->real^2) a = b` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM SET_TAC[]);;

let MOI_FSB_AMB_TRANS = prove
 (`!w a b c:real^2->bool. moi_fsb_amb w a b /\ moi_fsb_amb w b c ==> moi_fsb_amb w a c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsb_amb] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `h1:real^2->real^2` (X_CHOOSE_THEN `g1:real^2->real^2` STRIP_ASSUME_TAC))
   (X_CHOOSE_THEN `h2:real^2->real^2` (X_CHOOSE_THEN `g2:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`(h2:real^2->real^2) o (h1:real^2->real^2)`;
                        `(g1:real^2->real^2) o (g2:real^2->real^2)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[o_THM];
    ASM_REWRITE_TAC[IMAGE_o]]);;

let MOI_FSB_AMB_MONO = prove
 (`!w w' a b:real^2->bool. w SUBSET w' /\ moi_fsb_amb w a b ==> moi_fsb_amb w' a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsb_amb] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`h:real^2->real^2`; `g:real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FSB_AMB_POLY = prove
 (`!w R A B:real^2->bool.
     polytope R /\ polytope A /\ polytope B /\
     ~(interior A = {}) /\ ~(interior B = {}) /\
     A SUBSET interior R /\ B SUBSET interior R /\ interior R SUBSET w
     ==> moi_fsb_amb w A B`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSB_AMB_MONO THEN
  EXISTS_TAC `interior R:real^2->bool` THEN ASM_REWRITE_TAC[moi_fsb_amb] THEN
  MATCH_MP_TAC MOI_FSB_POLY_SWAP THEN ASM_REWRITE_TAC[]);;

(* Polygon neighbourhoods. *)

let MOI_FSB_POLY_NBHD = prove
 (`!K W:real^2->bool.
     polytope K /\ ~(interior K = {}) /\ open W /\ K SUBSET W
     ==> ?R. polytope R /\ K SUBSET interior R /\ R SUBSET W`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `p:real^2` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `compact (K:real^2->bool) /\ convex K /\ bounded K` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT; POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_BOUNDED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^2) IN K` ASSUME_TAC THENL
   [MP_TAC(ISPEC `K:real^2->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:real^2->bool`; `(:real^2) DIFF W`] SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)] THEN
  UNDISCH_TAC `bounded (K:real^2->bool)` THEN REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `l = &1 + d / (&4 * B)` THEN
  SUBGOAL_THEN `&1 < l` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[REAL_LT_ADDR] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\x:real^2. p + l % (x - p)) K` THEN
  SUBGOAL_THEN `linear (\x:real^2. l % x)` ASSUME_TAC THENL
   [REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^2. p + l % (x - p)) K =
    IMAGE (\x. (p - l % p) + x) (IMAGE (\x. l % x) K)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[POLYTOPE_TRANSLATION_EQ] THEN MATCH_MP_TAC POLYTOPE_LINEAR_IMAGE THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[INTERIOR_TRANSLATION] THEN
    MP_TAC(ISPECL [`\x:real^2. l % x`; `K:real^2->bool`] INTERIOR_INJECTIVE_LINEAR_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN ASM_SIMP_TAC[REAL_ARITH `&1 < l ==> ~(l = &0)`];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    EXISTS_TAC `l % (x - (&1 - inv l) % (x - p)):real^2` THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC; VECTOR_SUB_RDISTRIB] THEN
      SUBGOAL_THEN `l * inv l = &1` (fun th -> REWRITE_TAC[REAL_SUB_LDISTRIB; th]) THENL
       [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      VECTOR_ARITH_TAC;
      EXISTS_TAC `x - (&1 - inv l) % (x - p):real^2` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
      ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
      SUBGOAL_THEN `&0 < inv l /\ inv l < &1` MP_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
                        MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[]];
        REAL_ARITH_TAC]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `p + l % (x - p):real^2`]) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; dist; REAL_NOT_LE] THEN
    REWRITE_TAC[VECTOR_ARITH `x - (p + l % (x - p)):real^2 = (&1 - l) % (x - p)`] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `norm (x - p:real^2) <= &2 * B` ASSUME_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH `norm(x:real^2) <= B /\ norm(p:real^2) <= B
                               ==> norm(x - p) <= &2 * B`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(&1 - l) = d / (&4 * B)` SUBST1_TAC THENL
     [EXPAND_TAC "l" THEN REWRITE_TAC[REAL_ARITH `&1 - (&1 + x) = --x`; REAL_ABS_NEG] THEN
      REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d / (&4 * B) * &2 * B` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `d / (&4 * B) * &2 * B = d / &2` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < B` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]]]);;

(* Small closed squares. *)

let moi_fsb_sq = new_definition
 `moi_fsb_sq (x:real^2) r = interval[x - r % vector[&1;&1],x + r % vector[&1;&1]]`;;

let MOI_FSB_IN_SQ = prove
 (`!(x:real^2) r y.
     (y IN moi_fsb_sq x r <=> abs(y$1 - x$1) <= r /\ abs(y$2 - x$2) <= r) /\
     (y IN interior (moi_fsb_sq x r) <=> abs(y$1 - x$1) < r /\ abs(y$2 - x$2) < r)`,
  REWRITE_TAC[moi_fsb_sq; INTERIOR_CLOSED_INTERVAL; IN_INTERVAL; DIMINDEX_2; FORALL_2;
              VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let MOI_FSB_SQ = prove
 (`!(x:real^2) r.
     &0 < r
     ==> polytope (moi_fsb_sq x r) /\ ~(interior (moi_fsb_sq x r) = {}) /\
         x IN interior (moi_fsb_sq x r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN interior (moi_fsb_sq x r)` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_FSB_IN_SQ; REAL_SUB_REFL; REAL_ABS_0] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_fsb_sq; POLYTOPE_INTERVAL]; ASM SET_TAC[]]);;

let MOI_FSB_SQ_NEST = prove
 (`!(x:real^2) y r s.
     dist(x,y) + s < r ==> moi_fsb_sq y s SUBSET interior (moi_fsb_sq x r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; MOI_FSB_IN_SQ] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x - y:real^2`; `1`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`x - y:real^2`; `2`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT; GSYM dist] THEN ASM_REAL_ARITH_TAC);;

let MOI_FSB_SQ_MONO = prove
 (`!(x:real^2) r r'. r <= r' ==> moi_fsb_sq x r SUBSET moi_fsb_sq x r'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; MOI_FSB_IN_SQ] THEN ASM_REAL_ARITH_TAC);;

let MOI_FSB_SQ_IN_OPEN = prove
 (`!W (x:real^2). open W /\ x IN W ==> ?r. &0 < r /\ moi_fsb_sq x r SUBSET W`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / &3` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^2,e)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; MOI_FSB_IN_SQ; IN_BALL; dist] THEN
  X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `x - y:real^2` NORM_LE_L1) THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2; VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC);;

(* Straightening a filled PL circle to a triangle (AMB2_VERTEX). *)

let MOI_FSB_STRAIGHT = prove
 (`!W s:real^2->bool.
     open W /\ pl_sphere 1 s /\ s UNION inside s SUBSET W
     ==> ?t. &2 simplex t /\ t SUBSET W /\ moi_fsb_amb W (s UNION inside s) t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `p:real^2` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
              MATCH_MP MOI_SCD_PL_SPHERE_NONEMPTY) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `W:real^2->bool`; `p:real^2`] AMB2_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^2`
    (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^2) (s UNION inside s) = t` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_UNION] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SA2_PLH_UNIV) THEN
    MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`; `s:real^2->bool`]
      MOI_SCD_INSIDE_HOMEOMORPHISM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPEC `t:real^2->bool` MOI_FSB_POLY2) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; MOI_FSB_SIMPLEX2]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(el 1 (CONJUNCTS th))]);
    ALL_TAC] THEN
  EXISTS_TAC `t:real^2->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (f:real^2->real^2) (s UNION inside s) = t`)) THEN
    MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`; `W:real^2->bool`;
                   `s UNION inside s:real^2->bool`] MOI_SA2_FIX_OFF) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REWRITE_TAC[moi_fsb_amb] THEN
    MAP_EVERY EXISTS_TAC [`f:real^2->real^2`; `g:real^2->real^2`] THEN ASM_REWRITE_TAC[]]);;

let MOI_FSB_SQ_AMB = prove
 (`!W (x:real^2) y z r s s'.
     &0 < s /\ &0 < s' /\ dist(x,y) + s < r /\ dist(x,z) + s' < r /\
     moi_fsb_sq x r SUBSET W
     ==> moi_fsb_amb W (moi_fsb_sq y s) (moi_fsb_sq z s')`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSB_AMB_POLY THEN
  EXISTS_TAC `moi_fsb_sq (x:real^2) r` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x:real^2`; `y:real^2`] DIST_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FSB_SQ; MOI_FSB_SQ_NEST] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_fsb_sq (x:real^2) r` THEN
  ASM_REWRITE_TAC[INTERIOR_SUBSET]);;

let MOI_FSB_TRI_SQ = prove
 (`!W t:real^2->bool.
     open W /\ &2 simplex t /\ t SUBSET W
     ==> ?x r. x IN interior t /\ &0 < r /\ moi_fsb_sq x (&2 * r) SUBSET W /\
               moi_fsb_amb W (moi_fsb_sq x r) t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `polytope (t:real^2->bool) /\ ~(interior t = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN EXISTS_TAC `&2:int` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `t:real^2->bool` MOI_FSB_SIMPLEX2) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `W:real^2->bool`] MOI_FSB_POLY_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `R:real^2->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^2` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(interior t:real^2->bool = {})`)) THEN
  MP_TAC(ISPECL [`interior t:real^2->bool`; `x:real^2`] MOI_FSB_SQ_IN_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`x:real^2`; `r0 / &2`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&2 * r0 / &2 = r0`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `t:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `moi_fsb_sq (x:real^2) r0 SUBSET interior t` THEN
    UNDISCH_TAC `(t:real^2->bool) SUBSET W` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FSB_AMB_POLY THEN EXISTS_TAC `R:real^2->bool` THEN
  ASM_SIMP_TAC[MOI_FSB_SQ; REAL_ARITH `&0 < r0 ==> &0 < r0 / &2`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_fsb_sq (x:real^2) r0` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MOI_FSB_SQ_MONO THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `t:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `moi_fsb_sq (x:real^2) r0 SUBSET interior t` THEN SET_TAC[];
    MP_TAC(ISPEC `R:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(R:real^2->bool) SUBSET W` THEN SET_TAC[]]);;

(* Disk moving lemma: in a connected open subset of the plane any two      *)
(* filled PL circles are exchanged by a PL homeomorphism fixed off it      *)
(* (clopen argument on small squares).                                     *)

let MOI_FSB_DML = prove
 (`!W s s':real^2->bool.
     open W /\ connected W /\
     pl_sphere 1 s /\ s UNION inside s SUBSET W /\
     pl_sphere 1 s' /\ s' UNION inside s' SUBSET W
     ==> moi_fsb_amb W (s UNION inside s) (s' UNION inside s')`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `A = (s:real^2->bool) UNION inside s` THEN
  ABBREV_TAC `G = {x:real^2 | x IN W /\
                              ?r. &0 < r /\ moi_fsb_sq x (&2 * r) SUBSET W /\
                                  moi_fsb_amb W (moi_fsb_sq x r) A}` THEN
  SUBGOAL_THEN
   `!t:real^2->bool. &2 simplex t /\ t SUBSET W
      ==> ?x r. x IN interior t /\ &0 < r /\ moi_fsb_sq x (&2 * r) SUBSET W /\
                moi_fsb_amb W (moi_fsb_sq x r) t`
  (LABEL_TAC "TSQ") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSB_TRI_SQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* G is open *)
  SUBGOAL_THEN `open (G:real^2->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_CONTAINS_BALL] THEN EXPAND_TAC "G" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `r / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_BALL] THEN
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `moi_fsb_sq (y:real^2) (&2 * r / &4) SUBSET W` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_fsb_sq (x:real^2) (&2 * r)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `interior (moi_fsb_sq (x:real^2) (&2 * r))` THEN
      REWRITE_TAC[INTERIOR_SUBSET] THEN MATCH_MP_TAC MOI_FSB_SQ_NEST THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!a b c (y:real^2). y IN a /\ a SUBSET b /\ b SUBSET c
                                              ==> y IN c`) THEN
      MAP_EVERY EXISTS_TAC [`interior (moi_fsb_sq (y:real^2) (&2 * r / &4))`;
                            `moi_fsb_sq (y:real^2) (&2 * r / &4)`] THEN
      ASM_REWRITE_TAC[INTERIOR_SUBSET] THEN
      MP_TAC(ISPECL [`y:real^2`; `&2 * r / &4`] MOI_FSB_SQ) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    EXISTS_TAC `r / &4` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FSB_AMB_TRANS THEN
    EXISTS_TAC `moi_fsb_sq (x:real^2) r` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FSB_SQ_AMB THEN
    MAP_EVERY EXISTS_TAC [`x:real^2`; `&2 * r`] THEN
    ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the complement of G in W is open *)
  SUBGOAL_THEN `closure G INTER W SUBSET (G:real^2->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`W:real^2->bool`; `x:real^2`] MOI_FSB_SQ_IN_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(x:real^2) IN closure G` THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `r0 / &4`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(y:real^2) IN G` THEN EXPAND_TAC "G" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ry:real` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `~((x:real^2) IN G)` THEN EXPAND_TAC "G" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `r0 / &4` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_fsb_sq (x:real^2) r0` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSB_SQ_MONO THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `rho = min ry (r0 / &4) / &2` THEN
    SUBGOAL_THEN `&0 < rho /\ rho < ry /\ rho < r0 / &4` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FSB_AMB_TRANS THEN EXISTS_TAC `moi_fsb_sq (y:real^2) rho` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSB_SQ_AMB THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `&3 * r0 / &4`] THEN
      REWRITE_TAC[DIST_REFL] THEN
      UNDISCH_TAC `dist(y:real^2,x) < r0 / &4` THEN REWRITE_TAC[DIST_SYM] THEN
      DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_fsb_sq (x:real^2) r0` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSB_SQ_MONO THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC MOI_FSB_AMB_TRANS THEN EXISTS_TAC `moi_fsb_sq (y:real^2) ry` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSB_SQ_AMB THEN
      MAP_EVERY EXISTS_TAC [`y:real^2`; `&2 * ry`] THEN
      ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* G contains a point, hence all of W *)
  SUBGOAL_THEN `W SUBSET (G:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5C_CLOPEN_CONNECTED THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`W:real^2->bool`; `s:real^2->bool`] MOI_FSB_STRAIGHT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "TSQ" (MP_TAC o SPEC `t:real^2->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^2` THEN
    REWRITE_TAC[IN_INTER] THEN
    SUBGOAL_THEN `(x:real^2) IN W` ASSUME_TAC THENL
     [MP_TAC(ISPEC `t:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(x:real^2) IN interior t` THEN
      UNDISCH_TAC `(t:real^2->bool) SUBSET W` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FSB_AMB_TRANS THEN EXISTS_TAC `t:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSB_AMB_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the second circle *)
  MP_TAC(ISPECL [`W:real^2->bool`; `s':real^2->bool`] MOI_FSB_STRAIGHT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t':real^2->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "TSQ" (MP_TAC o SPEC `t':real^2->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^2) IN G` MP_TAC THENL
   [MP_TAC(ISPEC `t':real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(x:real^2) IN interior t'` THEN
    UNDISCH_TAC `(t':real^2->bool) SUBSET W` THEN
    UNDISCH_TAC `(W:real^2->bool) SUBSET G` THEN SET_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "G" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `rho = min r r' / &2` THEN
  SUBGOAL_THEN `&0 < rho /\ rho < r /\ rho < r'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FSB_AMB_SYM THEN
  MATCH_MP_TAC MOI_FSB_AMB_TRANS THEN EXISTS_TAC `t':real^2->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FSB_AMB_TRANS THEN EXISTS_TAC `moi_fsb_sq (x:real^2) rho` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FSB_AMB_SYM THEN
    MATCH_MP_TAC MOI_FSB_AMB_TRANS THEN EXISTS_TAC `moi_fsb_sq (x:real^2) r` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSB_SQ_AMB THEN
    MAP_EVERY EXISTS_TAC [`x:real^2`; `&2 * r`] THEN
    ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MOI_FSB_AMB_TRANS THEN EXISTS_TAC `moi_fsb_sq (x:real^2) r'` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSB_SQ_AMB THEN
    MAP_EVERY EXISTS_TAC [`x:real^2`; `&2 * r'`] THEN
    ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Removing filled PL circles from a connected open subset of the           *)
(* plane leaves it connected; moving finitely many disjoint disks onto      *)
(* disjoint target disks by one PL homeomorphism fixed off the open set.    *)
(* ------------------------------------------------------------------------- *)

let MOI_FSB_SQANN2_CONNECTED = prove
 (`connected (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
              interval[--vector[&1;&1],vector[&1;&1]])`,
  ABBREV_TAC `Q = interval[--vector[&2;&2]:real^2,vector[&2;&2]]` THEN
  SUBGOAL_THEN
   `Q DIFF interval[--vector[&1;&1]:real^2,vector[&1;&1]] =
    ((Q INTER {x:real^2 | x$1 > &1}) UNION (Q INTER {x | x$2 > &1})) UNION
    ((Q INTER {x | x$1 < -- &1}) UNION (Q INTER {x | x$2 < -- &1}))`
  SUBST1_TAC THENL
   [EXPAND_TAC "Q" THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_INTER; IN_ELIM_THM; IN_INTERVAL;
                DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!a k. connected (Q INTER {x:real^2 | x$k > a}) /\
                      connected (Q INTER {x:real^2 | x$k < a})`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC CONVEX_CONNECTED THEN
    MATCH_MP_TAC CONVEX_INTER THEN EXPAND_TAC "Q" THEN
    REWRITE_TAC[CONVEX_INTERVAL; CONVEX_HALFSPACE_COMPONENT_GT; CONVEX_HALFSPACE_COMPONENT_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^2. v IN Q <=> abs(v$1) <= &2 /\ abs(v$2) <= &2`
  ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vector[&3 / &2; &3 / &2]:real^2` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; VECTOR_2] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `vector[-- &3 / &2; -- &3 / &2]:real^2` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; VECTOR_2] THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vector[&3 / &2; -- &3 / &2]:real^2` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_UNION; IN_ELIM_THM; VECTOR_2] THEN REAL_ARITH_TAC]);;

let MOI_FSB_CONN_POLY = prove
 (`!W t:real^2->bool.
     open W /\ connected W /\ polytope t /\ ~(interior t = {}) /\ t SUBSET W
     ==> connected (W DIFF t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `W:real^2->bool`] MOI_FSB_POLY_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `R:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `connected (R DIFF t:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`R:real^2->bool`; `t:real^2->bool`] MOI_FSB_POLY_ANN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[pl_annulus_with_ends]] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
    FIRST_ASSUM(MP_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
                REWRITE_RULE[pl_homeomorphism]) THEN
    DISCH_THEN(fun th -> let cs = CONJUNCTS th in
      ASSUME_TAC(el 0 cs) THEN ASSUME_TAC(el 1 cs) THEN ASSUME_TAC(el 2 cs)) THEN
    SUBGOAL_THEN
     `R DIFF t =
      IMAGE (f:real^2->real^2)
       (interval[--vector[&2;&2],vector[&2;&2]] DIFF interval[--vector[&1;&1],vector[&1;&1]])`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `interval[--vector[&2;&2],vector[&2;&2]] DIFF interval[--vector[&1;&1],vector[&1;&1]] =
        (interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&1;&1],vector[&1;&1]))
        DIFF relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]):real^2->bool`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_DIFF; MOI_S5C_IN_SQI; MOI_S5C_IN_SQO] THEN
        SIMP_TAC[MOI_S5C_SQ_RF; REAL_ARITH `&0 < &1`] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `(R DIFF interior t) DIFF relative_frontier (t:real^2->bool)` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPEC `t:real^2->bool` MOI_FSB_POLY2) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o el 4 o CONJUNCTS) THEN
        MP_TAC(ISPEC `t:real^2->bool` INTERIOR_SUBSET) THEN SET_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `IMAGE (f:real^2->real^2)
                      (interval[--vector[&2;&2],vector[&2;&2]] DIFF
                       interval(--vector[&1;&1],vector[&1;&1])) = R DIFF interior t`)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        lhs(concl th) = `relative_frontier (t:real^2->bool)`)) THEN
      MATCH_MP_TAC(SET_RULE `!(f:real^2->real^2) (g:real^2->real^2) p q.
          (!x. x IN p ==> g (f x) = x) /\ q SUBSET p
          ==> IMAGE f p DIFF IMAGE f q = IMAGE f (p DIFF q)`) THEN
      EXISTS_TAC `g:real^2->real^2` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_DIFF; MOI_S5C_IN_SQI; MOI_S5C_IN_SQO] THEN
      SIMP_TAC[MOI_S5C_SQ_RF; REAL_ARITH `&0 < &1`] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[MOI_FSB_SQANN2_CONNECTED] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[--vector[&2;&2],vector[&2;&2]] DIFF
                  interval(--vector[&1;&1],vector[&1;&1]):real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`--vector[&1;&1]:real^2`; `vector[&1;&1]:real^2`]
        INTERVAL_OPEN_SUBSET_CLOSED) THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[connected] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^2->bool` (X_CHOOSE_THEN `e2:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(R DIFF t:real^2->bool) SUBSET e1 \/ (R DIFF t) SUBSET e2` MP_TAC THENL
   [UNDISCH_TAC `connected (R DIFF t:real^2->bool)` THEN REWRITE_TAC[connected] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`e1:real^2->bool`; `e2:real^2->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(R DIFF t:real^2->bool) SUBSET W DIFF t` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(W DIFF t:real^2->bool) SUBSET e1 UNION e2` THEN
    UNDISCH_TAC `e1 INTER e2 INTER (W DIFF t:real^2->bool) = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p ==> F) /\ (q ==> F) ==> p \/ q ==> F`) THEN CONJ_TAC THEN DISCH_TAC THENL
   [UNDISCH_TAC `connected (W:real^2->bool)` THEN REWRITE_TAC[connected] THEN
    MAP_EVERY EXISTS_TAC [`e1 UNION interior R:real^2->bool`; `e2 DIFF R:real^2->bool`] THEN
    ASM_SIMP_TAC[OPEN_UNION; OPEN_INTERIOR; OPEN_DIFF; POLYTOPE_IMP_CLOSED];
    UNDISCH_TAC `connected (W:real^2->bool)` THEN REWRITE_TAC[connected] THEN
    MAP_EVERY EXISTS_TAC [`e2 UNION interior R:real^2->bool`; `e1 DIFF R:real^2->bool`] THEN
    ASM_SIMP_TAC[OPEN_UNION; OPEN_INTERIOR; OPEN_DIFF; POLYTOPE_IMP_CLOSED]] THEN
  MP_TAC(ISPEC `R:real^2->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `t:real^2->bool` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `(t:real^2->bool) SUBSET interior R` THEN
  UNDISCH_TAC `(R:real^2->bool) SUBSET W` THEN
  UNDISCH_TAC `~(interior t:real^2->bool = {})` THEN
  ASM SET_TAC[]);;

let MOI_FSB_AMB_IMAGE = prove
 (`!(h:real^2->real^2) g w.
     pl_homeomorphism ((:real^2),(:real^2)) (h,g) /\ (!x. ~(x IN w) ==> h x = x)
     ==> IMAGE h w = w /\ IMAGE g w = w /\
         (!s. IMAGE h (w DIFF s) = w DIFF IMAGE h s) /\
         (!s. IMAGE g (w DIFF s) = w DIFF IMAGE g s) /\
         (!x. g (h x) = x) /\ (!y. h (g y) = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SA2_PLH_UNIV) THEN
  MP_TAC(ISPECL [`h:real^2->real^2`; `g:real^2->real^2`; `w:real^2->bool`; `w:real^2->bool`]
    MOI_SA2_FIX_OFF) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^2) w SUBSET w` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^2->real^2) ((g:real^2->real^2) (y:real^2)) = g y` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^2->real^2) w = w /\ IMAGE (g:real^2->real^2) w = w`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THENL
     [EXISTS_TAC `(g:real^2->real^2) y`; EXISTS_TAC `(h:real^2->real^2) y`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC(SET_RULE `!(f:real^2->real^2) g w s.
      (!x. g (f x) = x) /\ IMAGE f w = w ==> IMAGE f (w DIFF s) = w DIFF IMAGE f s`) THEN
  ASM_MESON_TAC[]);;

let MOI_FSB_CONN_DISK = prove
 (`!W s:real^2->bool.
     open W /\ connected W /\ pl_sphere 1 s /\ s UNION inside s SUBSET W
     ==> open (W DIFF (s UNION inside s)) /\ connected (W DIFF (s UNION inside s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MP_TAC(ISPEC `s:real^2->bool` MOI_S5C_PLANE_DISK) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[MOI_S5C_CELL_COMPACT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^2->bool`; `s:real^2->bool`] MOI_FSB_STRAIGHT) THEN
  ASM_REWRITE_TAC[moi_fsb_amb] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `h:real^2->real^2`
      (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`h:real^2->real^2`; `g:real^2->real^2`; `W:real^2->bool`]
    MOI_FSB_AMB_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `W DIFF (s UNION inside s) = IMAGE (g:real^2->real^2) (W DIFF t)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (h:real^2->real^2) (s UNION inside s) = t` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE `!f:real^2->real^2 s. (!x. f x = x) ==> s = IMAGE f s`) THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    ASM_MESON_TAC[pl_homeomorphism; homeomorphism];
    MATCH_MP_TAC MOI_FSB_CONN_POLY THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN EXISTS_TAC `&2:int` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `t:real^2->bool` MOI_FSB_SIMPLEX2) THEN ASM_SIMP_TAC[]]]);;

let MOI_FSB_CONN_DISKS = prove
 (`!k W (X:num->real^2->bool).
     open W /\ connected W /\
     (!i. i < k ==> pl_sphere 1 (X i) /\ X i UNION inside (X i) SUBSET W) /\
     (!i j. i < k /\ j < k /\ ~(i = j)
            ==> DISJOINT (X i UNION inside (X i)) (X j UNION inside (X j)))
     ==> open (W DIFF UNIONS {X i UNION inside (X i) | i < k}) /\
         connected (W DIFF UNIONS {X i UNION inside (X i) | i < k})`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `{(X:num->real^2->bool) i UNION inside (X i) | i < 0} = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; LT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[UNIONS_0; DIFF_EMPTY];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{(X:num->real^2->bool) i UNION inside (X i) | i < SUC k} =
    (X k UNION inside (X k)) INSERT {X i UNION inside (X i) | i < k}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; LT] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[UNIONS_INSERT] THEN
  SUBGOAL_THEN
   `W DIFF (((X:num->real^2->bool) k UNION inside (X k)) UNION
            UNIONS {X i UNION inside (X i) | i < k}) =
    (W DIFF UNIONS {X i UNION inside (X i) | i < k}) DIFF (X k UNION inside (X k))`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`W:real^2->bool`; `X:num->real^2->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        length(fst(strip_forall(concl th))) = 1)) THEN ASM_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        length(fst(strip_forall(concl th))) = 2)) THEN ASM_ARITH_TAC];
    STRIP_TAC] THEN
  MATCH_MP_TAC MOI_FSB_CONN_DISK THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    length(fst(strip_forall(concl th))) = 1)) THEN
  REWRITE_TAC[LT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `u:real^2->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  SUBGOAL_THEN
   `DISJOINT ((X:num->real^2->bool) k UNION inside (X k)) (X i UNION inside (X i))`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      length(fst(strip_forall(concl th))) = 2)) THEN ASM_ARITH_TAC;
    ASM SET_TAC[]]);;

(* Moving finitely many disjoint disks onto disjoint targets (each target   *)
(* disjoint from the other source disks) by one PL homeomorphism fixed off  *)
(* the connected open set W: the last disk inside W minus the other source *)
(* disks, then induction inside W minus the last target.                    *)

let MOI_FSB_MDE0 = prove
 (`!k W (X:num->real^2->bool) (Y:num->real^2->bool).
     open W /\ connected W /\
     (!i. i < k ==> pl_sphere 1 (X i) /\ X i UNION inside (X i) SUBSET W /\
                    pl_sphere 1 (Y i) /\ Y i UNION inside (Y i) SUBSET W) /\
     (!i j. i < k /\ j < k /\ ~(i = j)
            ==> DISJOINT (X i UNION inside (X i)) (X j UNION inside (X j)) /\
                DISJOINT (Y i UNION inside (Y i)) (Y j UNION inside (Y j)) /\
                DISJOINT (X i UNION inside (X i)) (Y j UNION inside (Y j)))
     ==> ?h g. pl_homeomorphism ((:real^2),(:real^2)) (h,g) /\
               (!x. ~(x IN W) ==> h x = x) /\
               (!i. i < k ==> IMAGE h (X i UNION inside (X i)) = Y i UNION inside (Y i))`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`\x:real^2. x`; `\x:real^2. x`] THEN
    REWRITE_TAC[MOI_SA2_PLH_ID; LT];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "H1") (LABEL_TAC "H2")))) THEN
  SUBGOAL_THEN
   `pl_sphere 1 ((X:num->real^2->bool) k) /\ X k UNION inside (X k) SUBSET W /\
    pl_sphere 1 ((Y:num->real^2->bool) k) /\ Y k UNION inside (Y k) SUBSET W`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "H1" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < k ==> DISJOINT ((X:num->real^2->bool) i UNION inside (X i)) (X k UNION inside (X k)) /\
                  DISJOINT ((Y:num->real^2->bool) i UNION inside (Y i)) (Y k UNION inside (Y k)) /\
                  DISJOINT (X i UNION inside (X i)) (Y k UNION inside (Y k)) /\
                  DISJOINT (X k UNION inside (X k)) (Y i UNION inside (Y i))`
  (LABEL_TAC "DK") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "H2" (MP_TAC o SPECL [`i:num`; `k:num`]) THEN
    USE_THEN "H2" (MP_TAC o SPECL [`k:num`; `i:num`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `W:real^2->bool`; `X:num->real^2->bool`] MOI_FSB_CONN_DISKS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      USE_THEN "H1" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN USE_THEN "H2" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`W DIFF UNIONS {(X:num->real^2->bool) i UNION inside (X i) | i < k}`;
                 `(X:num->real^2->bool) k`; `(Y:num->real^2->bool) k`] MOI_FSB_DML) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `y:real^2` THEN DISCH_THEN(LABEL_TAC "yin") THEN
    (CONJ_TAC THENL
      [USE_THEN "yin" MP_TAC THEN
       MAP_EVERY UNDISCH_TAC [`(X:num->real^2->bool) k UNION inside (X k) SUBSET W`;
                              `(Y:num->real^2->bool) k UNION inside (Y k) SUBSET W`] THEN
       SET_TAC[];
       ALL_TAC]) THEN
    X_GEN_TAC `u:real^2->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    USE_THEN "DK" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
    USE_THEN "yin" MP_TAC THEN
    UNDISCH_TAC `(y:real^2) IN u` THEN
    UNDISCH_TAC `u = (X:num->real^2->bool) i UNION inside (X i)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fsb_amb] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^2->real^2` (X_CHOOSE_THEN `g1:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`W:real^2->bool`; `(Y:num->real^2->bool) k`] MOI_FSB_CONN_DISK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`W DIFF ((Y:num->real^2->bool) k UNION inside (Y k))`;
    `X:num->real^2->bool`; `Y:num->real^2->bool`] o check (fun th ->
      length(fst(strip_forall(concl th))) = 3)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      USE_THEN "H1" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "DK" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      SET_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "H2" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      (ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]])];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:real^2->real^2` (X_CHOOSE_THEN `g2:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(h2:real^2->real^2) o (h1:real^2->real^2)`;
                        `(g1:real^2->real^2) o (g2:real^2->real^2)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(h1:real^2->real^2) x = x` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `h1:real^2->real^2`)) (concl th) &&
        is_forall (concl th))) THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `h2:real^2->real^2`)) (concl th) &&
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
        not (can (find_term (fun t -> t = `IMAGE:(real^2->real^2)->(real^2->bool)->real^2->bool`)) (concl th)))) THEN
      ASM SET_TAC[]];
    X_GEN_TAC `i:num` THEN REWRITE_TAC[LT] THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[IMAGE_o] THEN
      MATCH_MP_TAC(SET_RULE `!f:real^2->real^2 s. (!x. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `h2:real^2->real^2`)) (concl th) &&
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
        not (can (find_term (fun t -> t = `IMAGE:(real^2->real^2)->(real^2->bool)->real^2->bool`)) (concl th)))) THEN
      ASM SET_TAC[];
      REWRITE_TAC[IMAGE_o] THEN
      SUBGOAL_THEN `IMAGE (h1:real^2->real^2) ((X:num->real^2->bool) i UNION inside (X i)) =
                    X i UNION inside (X i)` SUBST1_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!f:real^2->real^2 s. (!x. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
        X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> t = `h1:real^2->real^2`)) (concl th) &&
          is_forall (concl th))) THEN
        REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* The holed disk model.  The outer rectangle moi_fsb_hq k, the             *)
(* closed holes moi_fsb_hc i and a rectangle moi_fsb_hr k around all holes  *)
(* inside the outer one; the model is a polyhedron and its frontier is the  *)
(* outer boundary plus the hole boundaries.                                  *)
(* ------------------------------------------------------------------------- *)

let moi_fsb_hq = new_definition
 `moi_fsb_hq k = interval[vec 0:real^2,vector[&4 * &k + &4; &4]]`;;

let moi_fsb_hc = new_definition
 `moi_fsb_hc i = interval[vector[&4 * &i + &2; &1]:real^2,vector[&4 * &i + &4; &3]]`;;

let moi_fsb_hr = new_definition
 `moi_fsb_hr k = interval[vector[&1; &1 / &2]:real^2,vector[&4 * &k + &3; &7 / &2]]`;;

let MOI_FSB_HD_EQ = prove
 (`!k. holed_disk_model k =
       moi_fsb_hq k DIFF UNIONS {interior (moi_fsb_hc i) | i < k}`,
  REWRITE_TAC[holed_disk_model; moi_fsb_hq; moi_fsb_hc; INTERIOR_CLOSED_INTERVAL]);;

let MOI_FSB_HD_FACTS = prove
 (`!k. polytope (moi_fsb_hq k) /\ polytope (moi_fsb_hr k) /\
       ~(interior (moi_fsb_hr k) = {}) /\
       moi_fsb_hr k SUBSET interior (moi_fsb_hq k) /\
       (!i. i < k ==> polytope (moi_fsb_hc i) /\ ~(interior (moi_fsb_hc i) = {}) /\
                      moi_fsb_hc i SUBSET interior (moi_fsb_hr k)) /\
       (!i j. ~(i = j) ==> DISJOINT (moi_fsb_hc i) (moi_fsb_hc j))`,
  GEN_TAC THEN
  REWRITE_TAC[moi_fsb_hq; moi_fsb_hr; moi_fsb_hc; POLYTOPE_INTERVAL;
              INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; SUBSET_INTERVAL;
              DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
  SUBGOAL_THEN `&0 <= &k` ASSUME_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&i + &1 <= &k` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `i:num` REAL_POS) THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
    REWRITE_TAC[DISJOINT; DISJOINT_INTERVAL; DIMINDEX_2] THEN
    EXISTS_TAC `1` THEN REWRITE_TAC[VECTOR_2; ARITH] THEN
    SUBGOAL_THEN `(i:num) + 1 <= j \/ j + 1 <= i` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC]);;

(* The model is a finite union of rectangles: bottom and top strips, the    *)
(* last column and the columns left of the holes.                          *)

let MOI_FSB_HD_UNION = prove
 (`!k. holed_disk_model k =
       UNIONS ({interval[vec 0:real^2,vector[&4 * &k + &4; &1]],
                interval[vector[&0; &3]:real^2,vector[&4 * &k + &4; &4]],
                interval[vector[&4 * &k; &1]:real^2,vector[&4 * &k + &4; &3]]} UNION
               {interval[vector[&4 * &i; &1]:real^2,vector[&4 * &i + &2; &3]] | i | i < k})`,
  GEN_TAC THEN
  REWRITE_TAC[holed_disk_model; UNIONS_UNION; UNIONS_INSERT; UNIONS_0; UNIONS_GSPEC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^2` THEN
  REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM; NOT_IN_EMPTY; IN_INTERVAL; DIMINDEX_2;
              FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
  SUBGOAL_THEN `&0 <= &k` ASSUME_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  EQ_TAC THENL
   [REWRITE_TAC[NOT_EXISTS_THM] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x:real^2)$2 <= &1` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `&3 <= (x:real^2)$2` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `&4 * &k <= (x:real^2)$1` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `(x:real^2)$1 / &4` FLOOR_POS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    MP_TAC(SPEC `(x:real^2)$1 / &4` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `n:num < k` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN ASM_REAL_ARITH_TAC;
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `j:num` THEN
      ASM_CASES_TAC `j:num < k` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&j + &1 <= &k` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&i + &1 <= &k` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `i:num` REAL_POS) THEN DISCH_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `j:num` THEN
      SUBGOAL_THEN `&j + &1 <= &i \/ &i <= &j` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC]]);;

let MOI_FSB_HD_POLY = prove
 (`!k. pl_polyhedron (holed_disk_model k) /\ locally_polyhedral (holed_disk_model k) /\
       compact (holed_disk_model k)`,
  GEN_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (holed_disk_model k)` ASSUME_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN ONCE_REWRITE_TAC[MOI_FSB_HD_UNION] THEN
    MATCH_MP_TAC(MESON[]
     `!X:(real^2->bool)->bool. FINITE X /\ (!k. k IN X ==> polytope k)
        ==> ?c. FINITE c /\ (!k. k IN c ==> polytope k) /\ UNIONS X = UNIONS c`) THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[FINITE_UNION; FINITE_INSERT; FINITE_EMPTY] THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY; IN_IMAGE] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[POLYTOPE_INTERVAL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; MOI_FEU_EULER_HOLED_DISK_MODEL]);;

let MOI_FSB_HD_FRONTIER = prove
 (`!k. frontier (holed_disk_model k) =
       relative_frontier (moi_fsb_hq k) UNION
       UNIONS {relative_frontier (moi_fsb_hc i) | i < k}`,
  GEN_TAC THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!P:real^2->bool. polytope P /\ ~(interior P = {})
      ==> relative_frontier P = P DIFF interior P /\ interior P SUBSET P /\
          closure (interior P) = P`
  (LABEL_TAC "PF") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPEC `P:real^2->bool` MOI_FSB_POLY2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> let cs = CONJUNCTS th in
      ASSUME_TAC(el 4 cs) THEN ASSUME_TAC(el 5 cs) THEN ASSUME_TAC(el 6 cs)) THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET] THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_INTERIOR; CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ABBREV_TAC `U = UNIONS {interior (moi_fsb_hc i) | i < k}` THEN
  SUBGOAL_THEN `closure U = UNIONS {moi_fsb_hc i | i < k}` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CLOSURE_UNIONS o lhand o snd) THEN
    ANTS_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[UNIONS_GSPEC] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EQ_TAC THEN STRIP_TAC THENL
     [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `closure (interior (moi_fsb_hc i)) = moi_fsb_hc i`
        (fun th -> ASM_MESON_TAC[th]) THEN
      USE_THEN "PF" (MP_TAC o SPEC `moi_fsb_hc i`) THEN ASM_SIMP_TAC[];
      EXISTS_TAC `interior (moi_fsb_hc i)` THEN CONJ_TAC THENL
       [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
        USE_THEN "PF" (MP_TAC o SPEC `moi_fsb_hc i`) THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[frontier] THEN
  SUBGOAL_THEN `closed (holed_disk_model k)` ASSUME_TAC THENL
   [SIMP_TAC[COMPACT_IMP_CLOSED; MOI_FSB_HD_POLY]; ALL_TAC] THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
  REWRITE_TAC[MOI_FSB_HD_EQ] THEN ASM_REWRITE_TAC[INTERIOR_DIFF] THEN
  SUBGOAL_THEN `~(interior (moi_fsb_hq k) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "PF" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `polytope (moi_fsb_hq k)`) (ASSUME `~(interior (moi_fsb_hq k) = {})`)))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i. i < k ==> relative_frontier (moi_fsb_hc i) =
                  moi_fsb_hc i DIFF interior (moi_fsb_hc i) /\
                  interior (moi_fsb_hc i) SUBSET moi_fsb_hc i /\
                  moi_fsb_hc i SUBSET interior (moi_fsb_hq k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `polytope (moi_fsb_hc i) /\ ~(interior (moi_fsb_hc i) = {}) /\
                  moi_fsb_hc i SUBSET interior (moi_fsb_hr k)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "PF" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `polytope (moi_fsb_hc i)`)
            (ASSUME `~(interior (moi_fsb_hc i) = {})`)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `moi_fsb_hr k` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "U" THEN REWRITE_TAC[UNIONS_GSPEC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^2` THEN
  REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_CASES_TAC `(x:real^2) IN interior (moi_fsb_hq k)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_DIFF];
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
      SUBGOAL_THEN `(x:real^2) IN moi_fsb_hc i /\ ~(x IN interior (moi_fsb_hc i)) /\
                    moi_fsb_hc i SUBSET interior (moi_fsb_hq k)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_DIFF]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET];
        REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
        ASM_CASES_TAC `j:num = i` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `DISJOINT (moi_fsb_hc i) (moi_fsb_hc j) /\
                      interior (moi_fsb_hc j) SUBSET moi_fsb_hc j`
        MP_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]];
        DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[] THEN
        EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* Tools for the planar holed disk theorem.  Frontiers under plane          *)
(* homeomorphisms, a free square off a compact set, images of polygons     *)
(* under PL homeomorphisms, a cell onto a triangle, moves fixed off the    *)
(* interior of a polygon, squeezing a rectangle off a compact set, and two *)
(* image identities for finite indexed unions.                             *)
(* ------------------------------------------------------------------------- *)

let MOI_FSB_FRONTIER_HOMEO = prove
 (`!(f:real^2->real^2) g c.
     homeomorphism ((:real^2),(:real^2)) (f,g)
     ==> IMAGE f (frontier c) = frontier (IMAGE f c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`; `(:real^2)`;
                 `(:real^2)`; `c:real^2->bool`] HOMEOMORPHISM_FRONTIER_OF) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; EUCLIDEAN_FRONTIER_OF; SUBSET_UNIV]);;

let MOI_FSB_FREE_SQ = prove
 (`!W U:real^2->bool.
     open W /\ ~(W = {}) /\ bounded W /\ compact U /\ U SUBSET W
     ==> ?S. polytope S /\ ~(interior S = {}) /\ S SUBSET W /\ DISJOINT S U`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x:real^2. x IN W /\ ~(x IN U)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~(W SUBSET U) ==> ?x:real^2. x IN W /\ ~(x IN U)`) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `W:real^2->bool = U` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `U:real^2->bool` CLOPEN) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    ASM_MESON_TAC[NOT_BOUNDED_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W DIFF U:real^2->bool`; `x:real^2`] MOI_FSB_SQ_IN_OPEN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_DIFF; COMPACT_IMP_CLOSED; IN_DIFF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `moi_fsb_sq x r` THEN
  MP_TAC(ISPECL [`x:real^2`; `r:real`] MOI_FSB_SQ) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The image of a polygon with interior under a PL homeomorphism of planar *)
(* sets is a filled PL circle. *)

let MOI_FSB_IMG_CELL = prove
 (`!(Q:real^2->bool) (t:real^2->bool) p q P.
     pl_homeomorphism (Q,t) (p,q) /\ polytope P /\ ~(interior P = {}) /\ P SUBSET Q
     ==> pl_sphere 1 (IMAGE p (relative_frontier P)) /\
         IMAGE p P = IMAGE p (relative_frontier P) UNION
                     inside (IMAGE p (relative_frontier P)) /\
         frontier (IMAGE p P) = IMAGE p (relative_frontier P)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 P (relative_frontier P:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5C_POLYTOPE_CELL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (P,IMAGE p P) (p:real^2->real^2,q)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5C_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`Q:real^2->bool`; `t:real^2->bool`] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (IMAGE p P) (IMAGE (p:real^2->real^2) (relative_frontier P))`
  MP_TAC THENL
   [MATCH_MP_TAC MOI_S5C_CELL_PLH THEN
    MAP_EVERY EXISTS_TAC [`P:real^2->bool`; `q:real^2->real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pl_cell_with_boundary 2 P (relative_frontier P:real^2->bool)` THEN
    REWRITE_TAC[pl_cell_with_boundary] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS(MATCH_MP MOI_FSB_PLANE_CELL th) in
    REWRITE_TAC[el 2 cs; el 5 cs] THEN ACCEPT_TAC(el 0 cs)));;

(* A planar cell is PL homeomorphic to any 2-simplex, boundary onto        *)
(* boundary. *)

let MOI_FSB_CELL_SIMPLEX = prove
 (`!(d:real^2->bool) j (k0:real^2->bool).
     pl_cell_with_boundary 2 d j /\ &2 simplex k0
     ==> ?p q. pl_homeomorphism (d,k0) (p,q) /\ IMAGE p j = relative_frontier k0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `kk:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^2`
     (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  MP_TAC(ISPECL [`kk:real^2->bool`; `k0:real^2->bool`; `&2:int`] MOI_FM3_SIMPLEX_PLH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2->real^2` (X_CHOOSE_THEN `q:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(p:real^2->real^2) o (g:real^2->real^2)`;
                        `(f:real^2->real^2) o (q:real^2->real^2)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `kk:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier kk SUBSET (kk:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^2) j = relative_frontier kk` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (kk,d) (f:real^2->real^2,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN
  SUBST1_TAC(ASSUME `IMAGE (g:real^2->real^2) j = relative_frontier kk`) THEN
  UNDISCH_TAC `pl_homeomorphism (relative_frontier kk,relative_frontier k0)
                 (p:real^2->real^2,q)` THEN
  SIMP_TAC[pl_homeomorphism; homeomorphism]);;

(* A PL homeomorphism of the plane fixed off the interior of a polygon     *)
(* restricts to the polygon. *)

let MOI_FSB_FIX_K0 = prove
 (`!(h:real^2->real^2) h' k0.
     pl_homeomorphism ((:real^2),(:real^2)) (h,h') /\
     (!x. ~(x IN interior k0) ==> h x = x) /\ polytope k0
     ==> pl_homeomorphism (k0,k0) (h,h') /\ IMAGE h k0 = k0 /\
         (!x. ~(x IN interior k0) ==> h' x = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^2->real^2`; `h':real^2->real^2`; `interior k0:real^2->bool`;
                 `interior k0:real^2->bool`] MOI_SA2_FIX_OFF) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_homeomorphism ((:real^2),(:real^2)) (h':real^2->real^2,h)` ASSUME_TAC
  THENL [ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h':real^2->real^2`; `h:real^2->real^2`; `interior k0:real^2->bool`;
                 `interior k0:real^2->bool`] MOI_SA2_FIX_OFF) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_SA2_PLH_UNIV
    (ASSUME `pl_homeomorphism ((:real^2),(:real^2)) (h:real^2->real^2,h')`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (h:real^2->real^2) k0 = k0` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k0:real^2->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pl_homeomorphism (k0,IMAGE h k0) (h:real^2->real^2,h')` MP_TAC THENL
   [MATCH_MP_TAC MOI_S5C_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`(:real^2)`; `(:real^2)`] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; SUBSET_UNIV];
    ASM_REWRITE_TAC[]]);;

(* Squeezing: a PL homeomorphism of a polygon Q onto a triangle k0 that    *)
(* carries a polygon R inside Q off a given compact set U in the interior. *)

let MOI_FSB_SQUEEZE = prove
 (`!(Q:real^2->bool) (R:real^2->bool) (k0:real^2->bool) (U:real^2->bool).
     polytope Q /\ polytope R /\ ~(interior R = {}) /\ R SUBSET interior Q /\
     &2 simplex k0 /\ compact U /\ U SUBSET interior k0
     ==> ?p q. pl_homeomorphism (Q,k0) (p,q) /\
               IMAGE p (relative_frontier Q) = relative_frontier k0 /\
               IMAGE p R SUBSET interior k0 /\ DISJOINT (IMAGE p R) U`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(interior Q:real^2->bool = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `R:real^2->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_FSB_SIMPLEX2 (ASSUME `&2 simplex (k0:real^2->bool)`)) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (tl (CONJUNCTS th))) THEN
  SUBGOAL_THEN `polytope (k0:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Q:real^2->bool`; `relative_frontier Q:real^2->bool`; `k0:real^2->bool`]
    MOI_FSB_CELL_SIMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5C_POLYTOPE_CELL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^2->real^2` (X_CHOOSE_THEN `q1:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (p1:real^2->real^2) R SUBSET interior k0` ASSUME_TAC THENL
   [MP_TAC(ISPEC `Q:real^2->bool` MOI_FSB_POLY2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o el 4 o CONJUNCTS) THEN
    MP_TAC(ISPEC `Q:real^2->bool` INTERIOR_SUBSET) THEN DISCH_TAC THEN
    UNDISCH_TAC `pl_homeomorphism (Q,k0) (p1:real^2->real^2,q1)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `(k0:real^2->bool) DIFF relative_frontier k0 = interior k0` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_DIFF] THEN
    SUBGOAL_THEN `(x:real^2) IN interior Q /\ x IN Q` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (p1:real^2->real^2) (relative_frontier Q) = relative_frontier k0` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(y:real^2) IN relative_frontier Q` THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    SUBGOAL_THEN `x:real^2 = y` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Q:real^2->bool`; `k0:real^2->bool`; `p1:real^2->real^2`;
                 `q1:real^2->real^2`; `R:real^2->bool`] MOI_FSB_IMG_CELL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS; INTERIOR_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `j = IMAGE (p1:real^2->real^2) (relative_frontier R)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`interior k0:real^2->bool`; `U:real^2->bool`] MOI_FSB_FREE_SQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `k0:real^2->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; INTERIOR_SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `S:real^2->bool` MOI_FSB_POLY2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in
    ASSUME_TAC(el 3 cs) THEN ASSUME_TAC(SYM(el 1 cs))) THEN
  MP_TAC(ISPECL [`interior k0:real^2->bool`; `j:real^2->bool`;
                 `relative_frontier S:real^2->bool`] MOI_FSB_DML) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTERIOR; CONVEX_CONNECTED; CONVEX_INTERIOR] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_fsb_amb] THEN
  DISCH_THEN(X_CHOOSE_THEN `h0:real^2->real^2` (X_CHOOSE_THEN `h0':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`h0:real^2->real^2`; `h0':real^2->real^2`; `k0:real^2->bool`]
    MOI_FSB_FIX_K0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(h0:real^2->real^2) o (p1:real^2->real^2)`;
                        `(q1:real^2->real^2) o (h0':real^2->real^2)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k0:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(k0:real^2->bool) DIFF relative_frontier k0 = interior k0` THEN
    UNDISCH_TAC `!x. ~(x IN interior k0) ==> (h0:real^2->real^2) x = x` THEN
    SET_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[]]);;

(* Images of finite indexed unions. *)

let MOI_FSB_IMAGE_UNION_LT = prove
 (`!(f:real^2->real^2) P C (A:num->real^2->bool) (B:num->real^2->bool) k.
     IMAGE f P = C /\ (!i. i < k ==> IMAGE f (A i) = B i)
     ==> IMAGE f (P UNION UNIONS {A i | i < k}) = C UNION UNIONS {B i | i < k}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS {(B:num->real^2->bool) i | i < k} =
                UNIONS {IMAGE (f:real^2->real^2) (A i) | i < k}` SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC; EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "C" THEN REWRITE_TAC[IMAGE_UNION] THEN AP_TERM_TAC THEN
  REWRITE_TAC[UNIONS_GSPEC; EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FSB_IMAGE_DIFF_LT = prove
 (`!(f:real^2->real^2) f' Q t0 (A:num->real^2->bool) (B:num->real^2->bool) k.
     (!x. x IN Q ==> f' (f x) = x) /\ IMAGE f Q = t0 /\
     (!i. i < k ==> A i SUBSET Q /\ IMAGE f (A i) = B i)
     ==> IMAGE f (Q DIFF UNIONS {A i | i < k}) = t0 DIFF UNIONS {B i | i < k}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "t0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; EXTENSION; IN_IMAGE]) THEN
  REWRITE_TAC[UNIONS_GSPEC; EXTENSION; IN_IMAGE; IN_DIFF; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Planar holed disks.  For pairwise disjoint filled PL circles             *)
(* in the interior of a triangle k0, the triangle minus their insides is    *)
(* PL homeomorphic to holed_disk_model k, the model frontier going onto the *)
(* triangle boundary and the circles.                                        *)
(* ------------------------------------------------------------------------- *)

(* A hole: a polygon P whose image under p is a filled PL circle, mapped  *)
(* onto the filled circle X by g o p when h carries X onto the image.      *)

let MOI_FSB_HOLE_IMAGE = prove
 (`!(p:real^2->real^2) (g:real^2->real^2) h (P:real^2->bool) (X:real^2->bool).
     homeomorphism ((:real^2),(:real^2)) (g,h) /\
     IMAGE p P = IMAGE p (relative_frontier P) UNION
                 inside (IMAGE p (relative_frontier P)) /\
     frontier (IMAGE p P) = IMAGE p (relative_frontier P) /\
     IMAGE h (X UNION inside X) =
       IMAGE p (relative_frontier P) UNION inside (IMAGE p (relative_frontier P)) /\
     frontier (X UNION inside X) = X
     ==> IMAGE (g o p) P = X UNION inside X /\
         IMAGE (g o p) (relative_frontier P) = X`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `Y = IMAGE (p:real^2->real^2) (relative_frontier P)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE ((g:real^2->real^2) o (p:real^2->real^2)) P = X UNION inside X`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN
    UNDISCH_TAC `IMAGE (p:real^2->real^2) P = Y UNION inside Y` THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `IMAGE (h:real^2->real^2) (X UNION inside X) = Y UNION inside Y` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `!y:real^2. (g:real^2->real^2) (h y) = y` ASSUME_TAC THENL
     [UNDISCH_TAC `homeomorphism ((:real^2),(:real^2)) (g:real^2->real^2,h)` THEN
      SIMP_TAC[homeomorphism; IN_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
  SUBST1_TAC(SYM(ASSUME `frontier (IMAGE (p:real^2->real^2) P) = Y`)) THEN
  MP_TAC(ISPECL [`g:real^2->real^2`; `h:real^2->real^2`; `IMAGE (p:real^2->real^2) P`]
    MOI_FSB_FRONTIER_HOMEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN ASM_REWRITE_TAC[]);;

let MOI_FSB_HOLE_INTERIOR = prove
 (`!(ff:real^2->real^2) gg Q P (X:real^2->bool).
     (!x. x IN Q ==> gg (ff x) = x) /\ P SUBSET Q /\
     interior P = P DIFF relative_frontier P /\ relative_frontier P SUBSET P /\
     IMAGE ff P = X UNION inside X /\ IMAGE ff (relative_frontier P) = X
     ==> IMAGE ff (interior P) = inside X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `X:real^2->bool` INSIDE_NO_OVERLAP) THEN
  SUBGOAL_THEN `IMAGE (ff:real^2->real^2) (P DIFF relative_frontier P) =
                IMAGE ff P DIFF IMAGE ff (relative_frontier P)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_FSB_PLANAR_HOLES = prove
 (`!k (k0:real^2->bool) (s:num->real^2->bool).
     &2 simplex k0 /\
     (!i. i < k ==> pl_sphere 1 (s i) /\ s i UNION inside (s i) SUBSET interior k0) /\
     (!i j. i < k /\ j < k /\ ~(i = j)
            ==> DISJOINT (s i UNION inside (s i)) (s j UNION inside (s j)))
     ==> ?f g. pl_homeomorphism (holed_disk_model k,
                                 k0 DIFF UNIONS {inside (s i) | i < k}) (f,g) /\
               IMAGE f (frontier (holed_disk_model k)) =
               relative_frontier k0 UNION UNIONS {s i | i < k}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "S") (LABEL_TAC "SD"))) THEN
  MP_TAC(SPEC `k:num` MOI_FSB_HD_FACTS) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_FSB_SIMPLEX2 (ASSUME `&2 simplex (k0:real^2->bool)`)) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (tl (CONJUNCTS th))) THEN
  SUBGOAL_THEN `polytope (k0:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_fsb_hr k SUBSET moi_fsb_hq k` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior (moi_fsb_hq k)` THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < k ==> compact ((s:num->real^2->bool) i UNION inside (s i)) /\
                  frontier (s i UNION inside (s i)) = s i`
  (LABEL_TAC "SC") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "S" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_S5C_PLANE_DISK o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_FSB_PLANE_CELL) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `D = UNIONS {(s:num->real^2->bool) i UNION inside (s i) | i < k}` THEN
  SUBGOAL_THEN `compact (D:real^2->bool) /\ D SUBSET interior k0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIONS THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      USE_THEN "SC" (fun th -> MESON_TAC[th]);
      REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
      USE_THEN "S" (fun th -> MESON_TAC[th])];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fsb_hq k`; `moi_fsb_hr k`; `k0:real^2->bool`; `D:real^2->bool`]
    MOI_FSB_SQUEEZE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2->real^2` (X_CHOOSE_THEN `q:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!i. i < k
        ==> moi_fsb_hc i SUBSET moi_fsb_hr k /\
            pl_sphere 1 (IMAGE (p:real^2->real^2) (relative_frontier (moi_fsb_hc i))) /\
            IMAGE p (moi_fsb_hc i) =
              IMAGE p (relative_frontier (moi_fsb_hc i)) UNION
              inside (IMAGE p (relative_frontier (moi_fsb_hc i))) /\
            frontier (IMAGE p (moi_fsb_hc i)) = IMAGE p (relative_frontier (moi_fsb_hc i)) /\
            interior (moi_fsb_hc i) = moi_fsb_hc i DIFF relative_frontier (moi_fsb_hc i) /\
            relative_frontier (moi_fsb_hc i) SUBSET moi_fsb_hc i`
  (LABEL_TAC "HC") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `polytope (moi_fsb_hc i) /\ ~(interior (moi_fsb_hc i) = {}) /\
                  moi_fsb_hc i SUBSET interior (moi_fsb_hr k)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_fsb_hc i SUBSET moi_fsb_hr k` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET_TRANS; INTERIOR_SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(a /\ b /\ c) /\ (d /\ e) ==> a /\ b /\ c /\ d /\ e`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSB_IMG_CELL THEN
      MAP_EVERY EXISTS_TAC [`moi_fsb_hq k`; `k0:real^2->bool`; `q:real^2->real^2`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS];
      MP_TAC(ISPEC `moi_fsb_hc i` MOI_FSB_POLY2) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> let cs = CONJUNCTS th in
        MP_TAC(CONJ (el 4 cs) (el 7 cs))) THEN
      MP_TAC(ISPEC `moi_fsb_hc i` INTERIOR_SUBSET) THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`k:num`; `interior k0:real^2->bool`; `s:num->real^2->bool`;
     `\i. IMAGE (p:real^2->real^2) (relative_frontier (moi_fsb_hc i))`] MOI_FSB_MDE0)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_INTERIOR] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERIOR]; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "HC" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      DISCH_THEN(fun th -> let cs = CONJUNCTS th in
        REWRITE_TAC[el 1 cs; GSYM(el 2 cs)] THEN ASSUME_TAC(el 0 cs)) THEN
      USE_THEN "S" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num < k`)]) THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (p:real^2->real^2) (moi_fsb_hr k)` THEN
      ASM_SIMP_TAC[IMAGE_SUBSET];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    USE_THEN "HC" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
    DISCH_THEN(fun th -> let cs = CONJUNCTS th in
      REWRITE_TAC[GSYM(el 2 cs)] THEN ASSUME_TAC(el 0 cs)) THEN
    USE_THEN "HC" (MP_TAC o C MP (ASSUME `j:num < k`) o SPEC `j:num`) THEN
    DISCH_THEN(fun th -> let cs = CONJUNCTS th in
      REWRITE_TAC[GSYM(el 2 cs)] THEN ASSUME_TAC(el 0 cs)) THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "SD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `DISJOINT (moi_fsb_hc i) (moi_fsb_hc j)` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `moi_fsb_hc i SUBSET moi_fsb_hq k /\ moi_fsb_hc j SUBSET moi_fsb_hq k`
      MP_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
      UNDISCH_TAC `pl_homeomorphism (moi_fsb_hq k,k0) (p:real^2->real^2,q)` THEN
      REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT1) THEN SET_TAC[];
      SUBGOAL_THEN `(s:num->real^2->bool) i UNION inside (s i) SUBSET D` MP_TAC THENL
       [EXPAND_TAC "D" THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`p:real^2->real^2`; `moi_fsb_hc j`; `moi_fsb_hr k`] IMAGE_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (IMAGE (p:real^2->real^2) (moi_fsb_hr k)) D` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HX"))))) THEN
  SUBGOAL_THEN `pl_homeomorphism ((:real^2),(:real^2)) (g:real^2->real^2,h)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^2->real^2`; `g:real^2->real^2`; `interior k0:real^2->bool`;
                 `{}:real^2->bool`] MOI_SA2_FIX_OFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^2->real^2`; `h:real^2->real^2`; `k0:real^2->bool`]
    MOI_FSB_FIX_K0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(MATCH_MP MOI_SA2_PLH_UNIV
    (ASSUME `pl_homeomorphism ((:real^2),(:real^2)) (g:real^2->real^2,h)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `pl_homeomorphism (moi_fsb_hq k,k0)
      ((g:real^2->real^2) o (p:real^2->real^2),(q:real^2->real^2) o (h:real^2->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k0:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN moi_fsb_hq k
         ==> ((q:real^2->real^2) o (h:real^2->real^2))
               (((g:real^2->real^2) o (p:real^2->real^2)) x) = x) /\
    IMAGE (g o p) (moi_fsb_hq k) = k0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `pl_homeomorphism (moi_fsb_hq k,k0)
        ((g:real^2->real^2) o (p:real^2->real^2),(q:real^2->real^2) o (h:real^2->real^2))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((g:real^2->real^2) o (p:real^2->real^2)) (relative_frontier (moi_fsb_hq k)) =
    relative_frontier k0`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(k0:real^2->bool) DIFF relative_frontier k0 = interior k0` THEN
    UNDISCH_TAC `!x. ~(x IN interior k0) ==> (g:real^2->real^2) x = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < k
        ==> IMAGE ((g:real^2->real^2) o (p:real^2->real^2)) (moi_fsb_hc i) =
              (s:num->real^2->bool) i UNION inside (s i) /\
            IMAGE (g o p) (relative_frontier (moi_fsb_hc i)) = s i /\
            IMAGE (g o p) (interior (moi_fsb_hc i)) = inside (s i) /\
            moi_fsb_hc i SUBSET moi_fsb_hq k`
  (LABEL_TAC "IM") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "HC" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `moi_fsb_hc i SUBSET moi_fsb_hq k` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p:real^2->real^2`; `g:real^2->real^2`; `h:real^2->real^2`;
                   `moi_fsb_hc i`; `(s:num->real^2->bool) i`] MOI_FSB_HOLE_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "HX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "SC" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
        SIMP_TAC[]];
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`(g:real^2->real^2) o (p:real^2->real^2)`;
                   `(q:real^2->real^2) o (h:real^2->real^2)`; `moi_fsb_hq k`;
                   `moi_fsb_hc i`; `(s:num->real^2->bool) i`] MOI_FSB_HOLE_INTERIOR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(g:real^2->real^2) o (p:real^2->real^2)`;
                        `(q:real^2->real^2) o (h:real^2->real^2)`] THEN
  CONJ_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL
      [`(g:real^2->real^2) o (p:real^2->real^2)`; `(q:real^2->real^2) o (h:real^2->real^2)`;
       `moi_fsb_hq k`; `k0:real^2->bool`; `\i. interior (moi_fsb_hc i)`;
       `\i. inside ((s:num->real^2->bool) i)`; `k:num`] MOI_FSB_IMAGE_DIFF_LT)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "IM" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_fsb_hc i` THEN
      ASM_REWRITE_TAC[INTERIOR_SUBSET];
      REWRITE_TAC[GSYM MOI_FSB_HD_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC MOI_S5C_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`moi_fsb_hq k`; `k0:real^2->bool`] THEN
    ASM_REWRITE_TAC[MOI_FSB_HD_POLY] THEN REWRITE_TAC[MOI_FSB_HD_EQ; SUBSET_DIFF];
    REWRITE_TAC[MOI_FSB_HD_FRONTIER] THEN
    MATCH_MP_TAC MOI_FSB_IMAGE_UNION_LT THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "IM" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Assembly.  The disk piece minus the open cones is the realized           *)
(* c-part; mapped into the triangle k0 the cones become disjoint filled     *)
(* circles in its interior; the planar theorem and the PL homeomorphism of  *)
(* the c-part with UNIONS c give the k-holed disk.                          *)
(* ------------------------------------------------------------------------- *)

let MOI_FSB_PSI_DISK = prove
 (`!(f:real^N+(real^N->bool)->real^M) c J0 J (k0:real^2->bool) phi psi.
     moi_fsb_rhyp f c /\ J0 IN components (surface_boundary c) /\
     J IN components (surface_boundary c) /\ ~(J = J0) /\
     pl_sphere 1 (moi_fsb_rc f c J) /\ &2 simplex k0 /\
     pl_homeomorphism (k0,moi_fsb_rp f c UNION
                          UNIONS {moi_fsb_rk f c J' | J' |
                                  J' IN components (surface_boundary c) DELETE J0})
                      (phi,psi) /\
     IMAGE phi (relative_frontier k0) = moi_fsb_rc f c J0
     ==> pl_cell_with_boundary 2 (IMAGE psi (moi_fsb_rk f c J))
                                 (IMAGE psi (moi_fsb_rc f c J)) /\
         IMAGE psi (moi_fsb_rk f c J) SUBSET interior k0 /\
         inside (IMAGE psi (moi_fsb_rc f c J)) =
         IMAGE psi (moi_fsb_rk f c J DIFF moi_fsb_rc f c J)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `P = moi_fsb_rp (f:real^N+(real^N->bool)->real^M) c UNION
                  UNIONS {moi_fsb_rk (f:real^N+(real^N->bool)->real^M) c J' | J' |
                          J' IN components (surface_boundary c) DELETE J0}` THEN
  SUBGOAL_THEN `moi_fsb_rk (f:real^N+(real^N->bool)->real^M) c J SUBSET P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_DELETE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^M`; `c:(real^N->bool)->bool`;
                 `J0:real^N->bool`] MOI_FSB_RC_SUB) THEN
  MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^M`; `c:(real^N->bool)->bool`;
                 `J:real^N->bool`] MOI_FSB_RC_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_fsb_rc (f:real^N+(real^N->bool)->real^M) c J0 SUBSET P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (P,k0) (psi:real^M->real^2,phi)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
              REWRITE_RULE[pl_homeomorphism]) THEN
  SUBGOAL_THEN `moi_fsb_rk (f:real^N+(real^N->bool)->real^M) c J INTER moi_fsb_rc (f:real^N+(real^N->bool)->real^M) c J0 = {}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^M`; `c:(real^N->bool)->bool`;
                   `J:real^N->bool`; `J0:real^N->bool`] MOI_FSB_RK_DISJ) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (IMAGE (psi:real^M->real^2) (moi_fsb_rk (f:real^N+(real^N->bool)->real^M) c J))
                            (IMAGE psi (moi_fsb_rc (f:real^N+(real^N->bool)->real^M) c J))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5C_CELL_PLH THEN
    EXISTS_TAC `moi_fsb_rk (f:real^N+(real^N->bool)->real^M) c J` THEN
    EXISTS_TAC `phi:real^2->real^M` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSB_RK_CELL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`P:real^M->bool`; `k0:real^2->bool`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_S5C_CELL_POLYHEDRON THEN
      MAP_EVERY EXISTS_TAC
       [`2`; `moi_fsb_rc (f:real^N+(real^N->bool)->real^M) c J`] THEN
      MATCH_MP_TAC MOI_FSB_RK_CELL THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `k0:real^2->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `k0 DIFF relative_frontier k0 = interior (k0:real^2->bool) /\
                  relative_frontier k0 SUBSET k0` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `k0:real^2->bool` MOI_FSB_SIMPLEX2) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      ALL_TAC] THEN
    UNDISCH_TAC `k0 DIFF relative_frontier k0 = interior (k0:real^2->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^M) IN P` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_fsb_rk (f:real^N+(real^N->bool)->real^M) c J SUBSET P` THEN
      UNDISCH_TAC `(x:real^M) IN moi_fsb_rk (f:real^N+(real^N->bool)->real^M) c J` THEN
      SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^M) IN moi_fsb_rc (f:real^N+(real^N->bool)->real^M) c J0` MP_TAC THENL
     [SUBGOAL_THEN `(phi:real^2->real^M) (psi x) = x` (SUBST1_TAC o SYM) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (phi:real^2->real^M) (relative_frontier k0) =
                   moi_fsb_rc (f:real^N+(real^N->bool)->real^M) c J0` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_fsb_rk (f:real^N+(real^N->bool)->real^M) c J INTER
                   moi_fsb_rc f c J0 = {}` THEN
      UNDISCH_TAC `(x:real^M) IN moi_fsb_rk (f:real^N+(real^N->bool)->real^M) c J` THEN
      SET_TAC[]];
    SUBGOAL_THEN
     `IMAGE (psi:real^M->real^2) (moi_fsb_rk (f:real^N+(real^N->bool)->real^M) c J DIFF
                                  moi_fsb_rc f c J) =
      IMAGE psi (moi_fsb_rk f c J) DIFF IMAGE psi (moi_fsb_rc f c J)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!(f:real^M->real^2) (g:real^2->real^M) p s t.
          (!x. x IN p ==> g (f x) = x) /\ s SUBSET p /\ t SUBSET s
          ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t`) THEN
      MAP_EVERY EXISTS_TAC [`phi:real^2->real^M`; `P:real^M->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FSB_PLANE_CELL) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MP_TAC(ISPEC `IMAGE (psi:real^M->real^2)
                    (moi_fsb_rc (f:real^N+(real^N->bool)->real^M) c J)` INSIDE_NO_OVERLAP) THEN
    SET_TAC[]]);;

let MOI_FSB_PIECE_MINUS = prove
 (`!(f:real^N+(real^N->bool)->real^M) c J0.
     moi_fsb_rhyp f c /\ J0 IN components (surface_boundary c)
     ==> (moi_fsb_rp f c UNION
          UNIONS {moi_fsb_rk f c J | J | J IN components (surface_boundary c) DELETE J0})
         DIFF UNIONS {moi_fsb_rk f c J DIFF moi_fsb_rc f c J | J |
                      J IN components (surface_boundary c) DELETE J0} =
         moi_fsb_rp f c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!J y. J IN components (surface_boundary c)
          ==> ((y IN moi_fsb_rp f c /\ y IN moi_fsb_rk f c J <=> y IN moi_fsb_rc f c J) /\
               (y IN moi_fsb_rc (f:real^N+(real^N->bool)->real^M) c J
                ==> y IN moi_fsb_rk f c J))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^M`; `c:(real^N->bool)->bool`;
                   `J:real^N->bool`] MOI_FSB_RP_RK) THEN
    MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^M`; `c:(real^N->bool)->bool`;
                   `J:real^N->bool`] MOI_FSB_RC_SUB) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[IN_DIFF; IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_DELETE] THEN
  ASM_MESON_TAC[IN_DIFF]);;

let MOI_FSB_RP_POLYHEDRON = prove
 (`!(f:real^N+(real^N->bool)->real^M) c.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c
     ==> pl_polyhedron (moi_fsb_rp f c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSB_SC_CHARTS]; ALL_TAC] THEN
  REWRITE_TAC[pl_polyhedron; moi_fsb_rp] THEN
  EXISTS_TAC `{convex hull (IMAGE (f:real^N+(real^N->bool)->real^M) (IMAGE INL t)) |
               t IN moi_fsa_abs c}` THEN
  REWRITE_TAC[SIMPLE_IMAGE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[MOI_FSA_ABS_IMAGE] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; MOI_FSA_ABS_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `tr:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_IMAGE THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tr:real^N->bool`] MOI_FSA_VS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let MOI_FSB_SB_SUBSET = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c
     ==> surface_boundary c SUBSET UNIONS c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_FSB_SB_UNIONS; SUBSET; IN_UNIONS] THEN
  MESON_TAC[MOI_FSB_BEDGE_IN]);;

(* The third conclusion of the main theorem. *)

let MOI_FSB_PLANAR_EQ = prove
 (`!c:(real^N->bool)->bool k.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     connected (UNIONS c) /\ ~(UNIONS c = {}) /\
     CARD (components (surface_boundary c)) = k + 1 /\ complex_euler c = &1 - &k
     ==> ?(f:real^2->real^N) g.
           pl_homeomorphism (holed_disk_model k,UNIONS c) (f,g) /\
           IMAGE f (frontier (holed_disk_model k)) = surface_boundary c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (components (surface_boundary (c:(real^N->bool)->bool)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_FSB_BD_CIRCLES]; ALL_TAC] THEN
  SUBGOAL_THEN `?J0:real^N->bool. J0 IN components (surface_boundary c)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `CARD (components (surface_boundary (c:(real^N->bool)->bool))) = k + 1` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `moi_fsb_cap (c:(real^N->bool)->bool) (components (surface_boundary c))`
    MOI_FSB_REALIZE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MOI_FSB_CAP_BASIC THEN ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `f:real^N+(real^N->bool)->real^5`) THEN
  SUBGOAL_THEN `moi_fsb_rhyp (f:real^N+(real^N->bool)->real^5) c` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_fsb_rhyp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^5`; `c:(real^N->bool)->bool`]
    MOI_FSB_RP_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^5` (X_CHOOSE_THEN `h':real^5->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HJ")))) THEN
  SUBGOAL_THEN
   `!J:real^N->bool. J IN components (surface_boundary c)
       ==> pl_sphere 1 (moi_fsb_rc (f:real^N+(real^N->bool)->real^5) c J)`
  (LABEL_TAC "SPH") THENL
   [X_GEN_TAC `J:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "HJ" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `(J:real^N->bool) IN components (surface_boundary c)`))]) THEN
    MP_TAC(ISPECL [`J:real^N->bool`; `IMAGE (h:real^N->real^5) J`; `h:real^N->real^5`;
                   `h':real^5->real^N`; `1`] MOI_FM3_PL_SPHERE_TRANSFER) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[DIMINDEX_CONV `dimindex(:5)`] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `pl_sphere 1 (J:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FSB_BD_CIRCLES]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`UNIONS c:real^N->bool`;
                          `moi_fsb_rp (f:real^N+(real^N->bool)->real^5) c`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `surface_boundary c:real^N->bool` THEN
      ASM_SIMP_TAC[IN_COMPONENTS_SUBSET] THEN
      REWRITE_TAC[MOI_FSB_SB_UNIONS; SUBSET; IN_UNIONS] THEN
      ASM_MESON_TAC[MOI_FSB_BEDGE_IN];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `1` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^5`; `c:(real^N->bool)->bool`;
                 `J0:real^N->bool`; `k:num`] MOI_FSB_PIECE_DISK) THEN
  ASM_REWRITE_TAC[moi_fsa_disk] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^2->bool` (X_CHOOSE_THEN `phi:real^2->real^5`
    (X_CHOOSE_THEN `psi:real^5->real^2` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `P = moi_fsb_rp (f:real^N+(real^N->bool)->real^5) c UNION
                  UNIONS {moi_fsb_rk f c J | J | J IN components (surface_boundary c) DELETE J0}` THEN
  SUBGOAL_THEN `pl_homeomorphism (P,k0) (psi:real^5->real^2,phi)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
              REWRITE_RULE[pl_homeomorphism]) THEN
  DISCH_THEN(fun th -> match CONJUNCTS th with
      [a;b;_;d;_;_] -> MAP_EVERY ASSUME_TAC [a;b;d]
    | _ -> failwith "homeomorphism") THEN
  MP_TAC(CONJUNCT1(REWRITE_RULE[pl_homeomorphism] (ASSUME
   `pl_homeomorphism (UNIONS c,moi_fsb_rp (f:real^N+(real^N->bool)->real^5) c)
                     (h:real^N->real^5,h')`))) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_fsb_rp (f:real^N+(real^N->bool)->real^5) c SUBSET P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[SUBSET_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!J:real^N->bool. J IN components (surface_boundary c) /\ ~(J = J0)
       ==> moi_fsb_rk (f:real^N+(real^N->bool)->real^5) c J SUBSET P`
  (LABEL_TAC "RKP") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "P" THEN
    MATCH_MP_TAC(SET_RULE `!a b u:(real^5->bool)->bool. a IN u ==> a SUBSET b UNION UNIONS u`) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN EXISTS_TAC `J:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!J:real^N->bool. J IN components (surface_boundary c)
       ==> moi_fsb_rc (f:real^N+(real^N->bool)->real^5) c J SUBSET moi_fsb_rp f c`
  (LABEL_TAC "RCP") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^5`; `c:(real^N->bool)->bool`;
                   `J:real^N->bool`] MOI_FSB_RC_SUB) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`components (surface_boundary c) DELETE (J0:real^N->bool)`; `k:num`]
    HAS_SIZE_INDEX) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Jx:num->real^N->bool`
    (CONJUNCTS_THEN2 (LABEL_TAC "JX1") (LABEL_TAC "JX2"))) THEN
  SUBGOAL_THEN
   `!i. i < k ==> (Jx:num->real^N->bool) i IN components (surface_boundary c) /\
                  ~(Jx i = J0)`
  (LABEL_TAC "JXC") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "JX1" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
    REWRITE_TAC[IN_DELETE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. i < k /\ j < k /\ (Jx:num->real^N->bool) i = Jx j ==> i = j`
  (LABEL_TAC "JXI") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(Jx:num->real^N->bool) i IN components (surface_boundary c) DELETE J0`
    ASSUME_TAC THENL
     [USE_THEN "JX1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "JX2" (MP_TAC o C MP (ASSUME
      `(Jx:num->real^N->bool) i IN components (surface_boundary c) DELETE J0`) o
      SPEC `(Jx:num->real^N->bool) i`) THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `components (surface_boundary c) = (J0:real^N->bool) INSERT {(Jx:num->real^N->bool) i | i < k}`
  (LABEL_TAC "CJX") THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `J:real^N->bool` THEN
    REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_TAC THEN ASM_CASES_TAC `J:real^N->bool = J0` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(J:real^N->bool) IN components (surface_boundary c) DELETE J0`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
      USE_THEN "JX2" (MP_TAC o C MP (ASSUME
        `(J:real^N->bool) IN components (surface_boundary c) DELETE J0`) o
        SPEC `J:real^N->bool`) THEN
      REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC o CONJUNCT1) THEN
      EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "JXC" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `s = \i. IMAGE (psi:real^5->real^2)
                       (moi_fsb_rc (f:real^N+(real^N->bool)->real^5) c
                                   ((Jx:num->real^N->bool) i))` THEN
  SUBGOAL_THEN
   `!i. i < k ==>
        pl_cell_with_boundary 2
          (IMAGE (psi:real^5->real^2)
                 (moi_fsb_rk (f:real^N+(real^N->bool)->real^5) c ((Jx:num->real^N->bool) i)))
          ((s:num->real^2->bool) i) /\
        IMAGE psi (moi_fsb_rk f c (Jx i)) SUBSET interior k0 /\
        inside (s i) = IMAGE psi (moi_fsb_rk f c (Jx i) DIFF moi_fsb_rc f c (Jx i))`
  (LABEL_TAC "DI") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXPAND_TAC "s" THEN REWRITE_TAC[] THEN
    USE_THEN "JXC" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FSB_PSI_DISK THEN
    MAP_EVERY EXISTS_TAC [`J0:real^N->bool`; `phi:real^2->real^5`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "SPH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < k ==>
        pl_sphere 1 ((s:num->real^2->bool) i) /\
        s i UNION inside (s i) =
        IMAGE (psi:real^5->real^2)
              (moi_fsb_rk (f:real^N+(real^N->bool)->real^5) c ((Jx:num->real^N->bool) i))`
  (LABEL_TAC "SI") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "DI" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_FSB_PLANE_CELL o CONJUNCT1) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `k0:real^2->bool`; `s:num->real^2->bool`] MOI_FSB_PLANAR_HOLES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "SI" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      USE_THEN "DI" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      USE_THEN "SI" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      USE_THEN "SI" (MP_TAC o C MP (ASSUME `j:num < k`) o SPEC `j:num`) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
      USE_THEN "JXC" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
      USE_THEN "JXC" (MP_TAC o C MP (ASSUME `j:num < k`) o SPEC `j:num`) THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `~((Jx:num->real^N->bool) i = Jx j)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~(i:num = j)` THEN REWRITE_TAC[] THEN
        USE_THEN "JXI" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^5`; `c:(real^N->bool)->bool`;
                     `(Jx:num->real^N->bool) i`; `(Jx:num->real^N->bool) j`]
        MOI_FSB_RK_DISJ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      SUBGOAL_THEN `moi_fsb_rk (f:real^N+(real^N->bool)->real^5) c ((Jx:num->real^N->bool) i)
                    SUBSET P /\ moi_fsb_rk f c (Jx j) SUBSET P` MP_TAC THENL
       [CONJ_TAC THEN USE_THEN "RKP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `!x:real^5. x IN P ==> (phi:real^2->real^5) (psi x) = x` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^2->real^2` (X_CHOOSE_THEN `gg:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `k0 DIFF UNIONS {inside ((s:num->real^2->bool) i) | i < k} =
    IMAGE (psi:real^5->real^2) (moi_fsb_rp (f:real^N+(real^N->bool)->real^5) c)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^N+(real^N->bool)->real^5`; `c:(real^N->bool)->bool`;
                   `J0:real^N->bool`] MOI_FSB_PIECE_MINUS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN
     `UNIONS {inside ((s:num->real^2->bool) i) | i < k} =
      IMAGE (psi:real^5->real^2)
        (UNIONS {moi_fsb_rk (f:real^N+(real^N->bool)->real^5) c J DIFF moi_fsb_rc f c J |
                 J | J IN components (surface_boundary c) DELETE J0})`
    SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `u:real^2->bool` THEN
      REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `moi_fsb_rk (f:real^N+(real^N->bool)->real^5) c
                      ((Jx:num->real^N->bool) i) DIFF moi_fsb_rc f c (Jx i)` THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          USE_THEN "DI" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN SIMP_TAC[];
          EXISTS_TAC `(Jx:num->real^N->bool) i` THEN REWRITE_TAC[] THEN
          USE_THEN "JX1" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN SIMP_TAC[]];
        DISCH_THEN(X_CHOOSE_THEN `w:real^5->bool` (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `J:real^N->bool` STRIP_ASSUME_TAC))) THEN
        USE_THEN "JX2" (MP_TAC o C MP (ASSUME
          `(J:real^N->bool) IN components (surface_boundary c) DELETE J0`) o
          SPEC `J:real^N->bool`) THEN
        REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o CONJUNCT1) THEN
        EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "DI" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!(f:real^5->real^2) (g:real^2->real^5) p q k.
        (!x. x IN p ==> g (f x) = x) /\ IMAGE f p = k /\ q SUBSET p
        ==> k DIFF IMAGE f q = IMAGE f (p DIFF q)`) THEN
    EXISTS_TAC `phi:real^2->real^5` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b c:real^5->bool. a SUBSET c ==> a DIFF b SUBSET c`) THEN
    USE_THEN "RKP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (IMAGE (psi:real^5->real^2)
                        (moi_fsb_rp (f:real^N+(real^N->bool)->real^5) c),
                      moi_fsb_rp f c) (phi,psi)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`P:real^5->bool`; `k0:real^2->bool`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN ASM_SIMP_TAC[MOI_FSB_RP_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < k ==> IMAGE (phi:real^2->real^5) ((s:num->real^2->bool) i) =
                  moi_fsb_rc (f:real^N+(real^N->bool)->real^5) c ((Jx:num->real^N->bool) i)`
  (LABEL_TAC "PS") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "s" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
     `!(f:real^5->real^2) (g:real^2->real^5) p t.
        (!x. x IN p ==> g (f x) = x) /\ t SUBSET p ==> IMAGE g (IMAGE f t) = t`) THEN
    EXISTS_TAC `P:real^5->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_fsb_rp (f:real^N+(real^N->bool)->real^5) c` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "RCP" MATCH_MP_TAC THEN
    USE_THEN "JXC" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!J:real^N->bool. J IN components (surface_boundary c)
      ==> IMAGE (h':real^5->real^N) (moi_fsb_rc (f:real^N+(real^N->bool)->real^5) c J) = J`
  (LABEL_TAC "HJ'") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "HJ" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `(J:real^N->bool) IN components (surface_boundary c)`))]) THEN
    MATCH_MP_TAC(SET_RULE
     `!(f:real^N->real^5) (g:real^5->real^N) p t.
        (!x. x IN p ==> g (f x) = x) /\ t SUBSET p ==> IMAGE g (IMAGE f t) = t`) THEN
    EXISTS_TAC `UNIONS c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `surface_boundary c:real^N->bool` THEN
    ASM_SIMP_TAC[IN_COMPONENTS_SUBSET; MOI_FSB_SB_SUBSET];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(h':real^5->real^N) o (phi:real^2->real^5) o (ff:real^2->real^2)`;
    `((gg:real^2->real^2) o (psi:real^5->real^2)) o (h:real^N->real^5)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `moi_fsb_rp (f:real^N+(real^N->bool)->real^5) c` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `IMAGE (psi:real^5->real^2) (moi_fsb_rp (f:real^N+(real^N->bool)->real^5) c)` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `k0 DIFF UNIONS {inside ((s:num->real^2->bool) i) | i < k} =
        IMAGE (psi:real^5->real^2) (moi_fsb_rp (f:real^N+(real^N->bool)->real^5) c)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [UNIONS_COMPONENTS] THEN
  USE_THEN "CJX" SUBST1_TAC THEN
  REWRITE_TAC[IMAGE_UNION; IMAGE_UNIONS; UNIONS_INSERT] THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "HJ'" (fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `(J0:real^N->bool) IN components (surface_boundary c)`)]) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `u:real^N->bool` THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `v:real^5->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `w:real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC))))) THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "PS" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num < k`)]) THEN
    USE_THEN "HJ'" MATCH_MP_TAC THEN
    USE_THEN "JXC" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `moi_fsb_rc (f:real^N+(real^N->bool)->real^5) c ((Jx:num->real^N->bool) i)` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN USE_THEN "HJ'" MATCH_MP_TAC THEN
      USE_THEN "JXC" (MP_TAC o C MP (ASSUME `i:num < k`) o SPEC `i:num`) THEN SIMP_TAC[];
      EXISTS_TAC `(s:num->real^2->bool) i` THEN
      USE_THEN "PS" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num < k`)]) THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]]]);;

(* The main theorem. *)

let SURFACE_EULER_PLANAR = prove
 (MOI_FND_SURFACE_PLANAR,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FSB_BD_CIRCLES; MOI_FSB_EULER_BOUND] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSB_PLANAR_EQ THEN ASM_REWRITE_TAC[]);;


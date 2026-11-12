(* ========================================================================= *)
(* pc_moi_s34_residb: the global clauses of the tetra balls C''(r) of Moise   *)
(* GTM 47, Sec 34, pp.244-245.  From the per-3-simplex clauses                *)
(* moi_s4x_local (pc_moi_s34_residstmt) we prove the pairwise intersections   *)
(* (G1), the covering of the rims at interior edges (G3) and of A_v at        *)
(* interior vertices (G2): RESID_B : MOI_S4Y_RESID_B.  Route: interiors of    *)
(* the balls miss f1(N); interiors of distinct balls are disjoint; near a     *)
(* point of F in a ball and in no face disk, F lies in the ball, so two       *)
(* balls meeting there would cover a neighbourhood of a point of F (gluing    *)
(* of half charts, pc_moi_s34_rchart), which contradicts F = frontier of      *)
(* f1(N); (G3), (G2) by open-closed arguments on the rim circles and on the   *)
(* spheres frontier f1(C_v) minus finitely many points.                       *)
(* ========================================================================= *)

needs "src/pc_moi_s34_residstmt.ml";;
needs "src/pc_moi_s34_rchart.ml";;
needs "src/pc_moi_s34_frame.ml";;
needs "src/pc_moi_s34_tinf.ml";;
needs "src/pc_moi_s34_l910.ml";;
needs "src/pc_moi_s34_scellb.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Combinatorics of kk.  A 3-simplex has a vertex outside any               *)
(* other 3-simplex; a 2-face of a 3-simplex off the complex boundary lies in *)
(* a second 3-simplex; every edge and vertex lies in a 3-simplex; finiteness *)
(* of the simplices at a point and of the faces of a simplex.               *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Y_SIMP3_OTHER_VERTEX = prove
 (`!(tt:(real^N->bool)->bool) kk r r'.
     moi_s34_tube tt kk /\ r IN moi_s34_simp kk (&3) /\ r' IN moi_s34_simp kk (&3) /\
     ~(r = r')
     ==> ?u. {u} IN kk /\ u IN r /\ ~(u IN r')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4K_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `lf_simplicial_complex (kk:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?n'. n' simplex (r':real^N->bool)` (X_CHOOSE_TAC `n':int`) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->bool) SUBSET r'` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o last o CONJUNCTS o MATCH_MP SIMPLEX_EXTREME_POINTS o
      check (fun th -> concl th = `n simplex (r:real^N->bool)`)) THEN
    MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `u:real^N` THEN
      REWRITE_TAC[GSYM FACE_OF_SING] THEN DISCH_TAC THEN
      SUBGOAL_THEN `{u:real^N} IN kk /\ u IN r` MP_TAC THENL
       [CONJ_TAC THENL
         [ASM_MESON_TAC[];
          REWRITE_TAC[GSYM SING_SUBSET] THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
        ASM_MESON_TAC[]];
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->bool) face_of r'` ASSUME_TAC THENL
   [SUBGOAL_THEN `r:real^N->bool = r INTER r'` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:real^N->bool`; `r':real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ASM_REWRITE_TAC[INT_LT_REFL] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]);;

let MOI_S4Y_FACE_TWO = prove
 (`!(kk:(real^N->bool)->bool) s r.
     s IN moi_s34_simp kk (&2) /\ r IN moi_s34_simp kk (&3) /\ s SUBSET r /\
     ~(s SUBSET complex_boundary kk)
     ==> ?r2. r2 IN moi_s34_simp kk (&3) /\ s SUBSET r2 /\ ~(r2 = r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `~(s SUBSET complex_boundary (kk:(real^N->bool)->bool))` THEN
  REWRITE_TAC[complex_boundary] THEN
  MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN f ==> s SUBSET UNIONS f`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{r':real^N->bool | r' IN kk /\ aff_dim r' = &3 /\ s SUBSET r'} = {r}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `q:real^N->bool` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `q:real^N->bool` o REWRITE_RULE[NOT_EXISTS_THM] o
        check (is_neg o concl)) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[CARD_SING]]);;

let MOI_S4Y_EDGE_TETRA = prove
 (`!(tt:(real^N->bool)->bool) kk g.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1)
     ==> ?r. r IN moi_s34_simp kk (&3) /\ g SUBSET r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
    MOI_S4L_EDGE_VERTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `u:real^N`;
                `g:real^N->bool`] MOI_S4O_KK_PURE_GEN) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(g:real^N->bool) IN moi_s34_simp kk (&1)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `g:real^N->bool = segment[u,w]` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^N->bool. (w:real^N) IN x`) THEN
    REWRITE_TAC[ENDS_IN_SEGMENT; IN_SING] THEN ASM_MESON_TAC[];
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN MESON_TAC[]]);;

let MOI_S4Y_VERTEX_TETRA = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk
     ==> ?r. r IN moi_s34_simp kk (&3) /\ v IN r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4B_KK_TETRA THEN
  EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
  EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING]);;

let MOI_S4Y_FINITE_AT = prove
 (`!(tt:(real^N->bool)->bool) kk x.
     moi_s34_tube tt kk /\ x IN UNIONS kk ==> FINITE {q | q IN kk /\ x IN q}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4K_COFACES_FINITE THEN
  ASM_MESON_TAC[MOI_S4K_TUBE_FACTS]);;

let MOI_S4Y_FINITE_FACES = prove
 (`!(tt:(real^N->bool)->bool) kk r.
     moi_s34_tube tt kk /\ r IN kk ==> FINITE {q | q IN kk /\ q SUBSET r}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4K_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[lf_simplicial_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{f:real^N->bool | f face_of r}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_POLYTOPE_FACES THEN ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `q:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `q:real^N->bool = q INTER r` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The frame in R^3.  FN = f1(N) is the union of the vertex                  *)
(* balls C_v'' = f1(C_v); F = f1(Bd N) misses interior FN and lies in the    *)
(* closure of interior FN; F INTER C_v'' = A_v'' = f1(C_v INTER Bd N), the  *)
(* frontier of C_v'' is a PL 2-sphere containing A_v'' and the splitting     *)
(* disks D_g'' (g at v); F INTER D_g'' is the rim f1(D_g INTER Bd N).        *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Y_AV_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk
     ==> IMAGE f1 (moi_s34_bd tt kk) INTER IMAGE f1 (moi_s34_vb tt kk v) =
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
         IMAGE f1 (moi_s34_vb tt kk v) SUBSET IMAGE f1 (moi_s34_nb tt kk) /\
         compact (IMAGE f1 (moi_s34_vb tt kk v)) /\
         pl_ball 3 (IMAGE f1 (moi_s34_vb tt kk v)) /\
         pl_sphere 2 (frontier (IMAGE f1 (moi_s34_vb tt kk v))) /\
         frontier (IMAGE f1 (moi_s34_vb tt kk v)) =
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
         UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g |
                 g IN moi_s34_simp kk (&1) /\ v IN g}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s34_vb tt kk v SUBSET moi_s34_nb tt (kk:(real^N->bool)->bool) /\
                moi_s34_bd tt kk SUBSET moi_s34_nb tt kk` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4L_GRAPH_TUBE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> CONJ_TAC THENL
     [MP_TAC(SPEC `v:real^N` (CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))) THEN ASM_SIMP_TAC[];
      ACCEPT_TAC(CONJUNCT1(CONJUNCT2 th))]);
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4L_AV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S4L_BALL_FRONTIER_SPHERE) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
      MOI_S4L_FRAME_F1) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`; `moi_s34_nb tt (kk:(real^N->bool)->bool)`;
                   `moi_s34_vb tt kk (v:real^N)`; `moi_s34_bd tt (kk:(real^N->bool)->bool)`]
      MOI_S4L_IMAGE_INTER_INJ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC THEN SET_TAC[]];
    MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S4Y_SD_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car g.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ g IN moi_s34_simp kk (&1)
     ==> IMAGE f1 (moi_s34_bd tt kk) INTER IMAGE f1 (moi_s34_sd tt kk g) =
         IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) /\
         pl_cell_with_boundary 2 (IMAGE f1 (moi_s34_sd tt kk g))
           (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) /\
         IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
         IMAGE f1 (moi_s34_sd tt kk g) /\
         compact (IMAGE f1 (moi_s34_sd tt kk g)) /\
         IMAGE f1 (moi_s34_sd tt kk g) SUBSET IMAGE f1 (moi_s34_nb tt kk) /\
         (!v. {v} IN kk /\ v IN g
              ==> IMAGE f1 (moi_s34_sd tt kk g) SUBSET IMAGE f1 (moi_s34_vb tt kk v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s34_sd tt kk g SUBSET moi_s34_nb tt (kk:(real^N->bool)->bool) /\
                moi_s34_bd tt kk SUBSET moi_s34_nb tt kk` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
        MOI_S4L_IMAGES) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o last o CONJUNCTS) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4K_NB_UNION_CELLS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2)];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))
                  (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk))` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car` THEN
    REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
      MOI_S4L_FRAME_F1) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`; `moi_s34_nb tt (kk:(real^N->bool)->bool)`;
                   `moi_s34_sd tt kk (g:real^N->bool)`; `moi_s34_bd tt (kk:(real^N->bool)->bool)`]
      MOI_S4L_IMAGE_INTER_INJ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC THEN SET_TAC[]];
    MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[moi_s34_sd] THEN
    MATCH_MP_TAC(SET_RULE `(a:real^N->bool) IN f ==> INTERS f SUBSET a`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[]]);;
let MOI_S4Y_FN_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car
     ==> IMAGE f1 (moi_s34_nb tt kk) =
         UNIONS {IMAGE f1 (moi_s34_vb tt kk v) | v | {v} IN kk} /\
         IMAGE f1 (moi_s34_bd tt kk) SUBSET IMAGE f1 (moi_s34_nb tt kk) /\
         IMAGE f1 (moi_s34_bd tt kk) INTER interior (IMAGE f1 (moi_s34_nb tt kk)) = {} /\
         IMAGE f1 (moi_s34_bd tt kk) SUBSET
         closure (interior (IMAGE f1 (moi_s34_nb tt kk)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S4L_FRAME_F1
    (ASSUME `moi_s34_frame tt kk (h:real^N->real^3) ep f1 car`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S4K_NB_UNION_CELLS (ASSUME `moi_s34_tube (tt:(real^N->bool)->bool) kk`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nbu") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) =
                UNIONS {IMAGE f1 (moi_s34_vb tt kk v) | v | {v} IN kk}` (LABEL_TAC "fnu") THENL
   [REMOVE_THEN "nbu" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    REMOVE_THEN "nbu" (K ALL_TAC)] THEN
  CONJ_TAC THENL [USE_THEN "fnu" ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?v:real^N. {v} IN (kk:(real^N->bool)->bool) /\
                (y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^3) IN UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | v |
                                        {v} IN (kk:(real^N->bool)->bool)}` MP_TAC THENL
     [USE_THEN "fnu" (SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
      UNDISCH_TAC `moi_s34_bd tt kk SUBSET moi_s34_nb tt (kk:(real^N->bool)->bool)` THEN
      SET_TAC[];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4Y_AV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN closure (interior (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)))`
  MP_TAC THENL
   [MP_TAC(ISPEC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` MOI_S4YC_BALL_BASIC) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> SUBST1_TAC(SYM(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> (y:real^3) IN s ==> y IN t`) THEN
  MATCH_MP_TAC SUBSET_CLOSURE THEN MATCH_MP_TAC SUBSET_INTERIOR THEN FIRST_ASSUM ACCEPT_TAC);;


(* ------------------------------------------------------------------------- *)
(* Facts on one tetra ball b = C''(r).  b is a compact ball                 *)
(* with connected interior; b INTER f1(N) lies in F; F INTER b lies in the  *)
(* frontier, which lies in the face disks of r and F; the interior of b     *)
(* misses f1(N) (F lies in the closure of interior f1(N)) and every face   *)
(* disk; the patches lie in A_v'' and the rim arcs in the rims.             *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Y_BALL_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r b.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     r IN moi_s34_simp kk (&3) /\ moi_s4x_local tt kk f1 car dd r b
     ==> compact b /\ closed b /\ connected (interior b) /\ ~(interior b = {}) /\
         interior b SUBSET b /\ frontier b = b DIFF interior b /\
         b INTER IMAGE f1 (moi_s34_nb tt kk) SUBSET IMAGE f1 (moi_s34_bd tt kk) /\
         b INTER IMAGE f1 (moi_s34_bd tt kk) SUBSET frontier b /\
         frontier b SUBSET
         UNIONS {dd s | s | s IN moi_s34_simp kk (&2) /\ s SUBSET r} UNION
         IMAGE f1 (moi_s34_bd tt kk) /\
         (!s. s IN moi_s34_simp kk (&2) /\ s SUBSET r ==> dd s SUBSET frontier b) /\
         interior b INTER IMAGE f1 (moi_s34_nb tt kk) = {} /\
         (!s. s IN moi_s34_simp kk (&2) ==> interior b INTER dd s = {}) /\
         (!v. {v} IN kk /\ v IN r
              ==> b INTER IMAGE f1 (moi_s34_vb tt kk v) SUBSET
                  IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)) /\
         (!g. g IN moi_s34_simp kk (&1)
              ==> b INTER IMAGE f1 (moi_s34_sd tt kk g) SUBSET
                  IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s4x_local tt kk (f1:real^N->real^3) car dd r b` THEN
  REWRITE_TAC[moi_s4x_local] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "fr") (CONJUNCTS_THEN2 (LABEL_TAC "nbbd")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "avoid")))))))) THEN
  MP_TAC(MATCH_MP MOI_S4YC_BALL_BASIC (ASSUME `pl_ball 3 (b:real^3->bool)`)) THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun k -> ASSUME_TAC(el k (CONJUNCTS th))) [0;1;2]) THEN
  MP_TAC(MATCH_MP MOI_S4YC_BALL_DIFF_FRONTIER (ASSUME `pl_ball 3 (b:real^3->bool)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "fdi") (K ALL_TAC)))) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
    MOI_S4Y_FN_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  ASSUME_TAC(ISPEC `b:real^3->bool` INTERIOR_SUBSET) THEN
  SUBGOAL_THEN `b INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) SUBSET
                IMAGE f1 (moi_s34_bd tt kk)` ASSUME_TAC THENL
   [USE_THEN "nbbd" (fun th -> REWRITE_TAC[th]) THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `b INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) SUBSET frontier b`
  ASSUME_TAC THENL
   [USE_THEN "fr" (fun th -> REWRITE_TAC[th]) THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frontier b SUBSET
    UNIONS {dd s | s | s IN moi_s34_simp kk (&2) /\ s SUBSET r} UNION
    IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` ASSUME_TAC THENL
   [USE_THEN "fr" (fun th -> REWRITE_TAC[th]) THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN moi_s34_simp kk (&2) /\ s SUBSET r
                    ==> (dd:(real^N->bool)->real^3->bool) s SUBSET frontier b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "fr" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN f ==> x SUBSET UNIONS f UNION t`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior b INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) = {}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `interior b INTER interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) = {}`
    ASSUME_TAC THENL
     [MP_TAC(ISPEC `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` INTERIOR_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC
       [`interior b SUBSET (b:real^3->bool)`;
        `b INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) SUBSET IMAGE f1 (moi_s34_bd tt kk)`;
        `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER
         interior (IMAGE f1 (moi_s34_nb tt kk)) = {}`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `interior b INTER
                  closure (interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))) = {}`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_INTERIOR]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`interior b SUBSET (b:real^3->bool)`;
      `b INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) SUBSET IMAGE f1 (moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) SUBSET
       closure (interior (IMAGE f1 (moi_s34_nb tt kk)))`;
      `interior b INTER
       closure (interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))) = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN moi_s34_simp kk (&2)
                    ==> interior b INTER (dd:(real^N->bool)->real^3->bool) s = {}`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(s:real^N->bool) SUBSET r` THENL
     [SUBGOAL_THEN `(dd:(real^N->bool)->real^3->bool) s SUBSET frontier b` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!s. P s ==> (dd:(real^N->bool)->real^3->bool) s SUBSET frontier b`)
          (concl th))) THEN ASM_REWRITE_TAC[];
        USE_THEN "fdi" (fun th -> REWRITE_TAC[th]) THEN SET_TAC[]];
      USE_THEN "avoid" (MP_TAC o SPEC `s:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `interior b SUBSET (b:real^3->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. {v} IN kk /\ v IN r
        ==> b INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET
            IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `v:real^N`] MOI_S4Y_AV_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (MP_TAC o CONJUNCT1)) THEN
    UNDISCH_TAC `b INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) SUBSET
                 IMAGE f1 (moi_s34_bd tt kk)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. g IN moi_s34_simp kk (&1)
        ==> b INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET
            IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `g:real^N->bool`] MOI_S4Y_SD_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
      (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2)) THEN
    UNDISCH_TAC `b INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) SUBSET
                 IMAGE f1 (moi_s34_bd tt kk)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN USE_THEN "fdi" ACCEPT_TAC);;

(* The clauses of moi_s4x_local, one at a time. *)

let MOI_S4Y_LOCAL_CLAUSES = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) car dd r b.
     moi_s4x_local tt kk f1 car dd r b
     ==> pl_ball 3 b /\
         (!v. {v} IN kk /\ v IN r
              ==> pl_cell_with_boundary 2 (b INTER IMAGE f1 (moi_s34_vb tt kk v))
                    (UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                             s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
                     UNIONS {b INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                             g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r})) /\
         (!g. g IN moi_s34_simp kk (&1) /\ g SUBSET r
              ==> pl_cell_with_boundary 1 (b INTER IMAGE f1 (moi_s34_sd tt kk g))
                    (UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                             s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r})) /\
         (!w. {w} IN kk /\ ~(w IN r) ==> DISJOINT b (IMAGE f1 (moi_s34_vb tt kk w))) /\
         (!s. s IN moi_s34_simp kk (&2) /\ ~(s SUBSET r) ==> DISJOINT b (dd s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4x_local] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Distinct tetra balls have disjoint interiors.  interior b                *)
(* misses frontier b' (face disks and F), so by connectedness it lies in   *)
(* interior b' or misses b'; nesting is impossible since b meets C_u'' for  *)
(* a vertex u of r outside r', which b' misses.                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Y_PATCH_NONEMPTY = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) car dd r b v.
     moi_s4x_local tt kk f1 car dd r b /\ {v} IN kk /\ v IN r
     ==> ~(b INTER IMAGE f1 (moi_s34_vb tt kk v) = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4x_local] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `v:real^N` o el 4 o CONJUNCTS) STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO) THEN
  SET_TAC[]);;

let MOI_S4Y_INTERIOR_MISS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r b r' b'.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     r IN moi_s34_simp kk (&3) /\ moi_s4x_local tt kk f1 car dd r b /\
     r' IN moi_s34_simp kk (&3) /\ moi_s4x_local tt kk f1 car dd r' b' /\ ~(r = r')
     ==> interior b INTER b' = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `b:real^3->bool`]
    MOI_S4Y_BALL_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "B")] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r':real^N->bool`; `b':real^3->bool`]
    MOI_S4Y_BALL_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "B'")] THEN
  SUBGOAL_THEN `interior b INTER frontier b':real^3->bool = {}` ASSUME_TAC THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
      MOI_S4Y_FN_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2)] THEN
    USE_THEN "B" (fun th -> MP_TAC(el 10 (CONJUNCTS th)) THEN MP_TAC(el 11 (CONJUNCTS th))) THEN
    USE_THEN "B'" (fun th -> MP_TAC(el 8 (CONJUNCTS th))) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior b' INTER interior b = {} \/
                ((:real^3) DIFF b') INTER interior b = {}` MP_TAC THENL
   [USE_THEN "B" (MP_TAC o el 2 o CONJUNCTS) THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`interior b':real^3->bool`; `(:real^3) DIFF b'`]) THEN
    MATCH_MP_TAC(TAUT `(a /\ b /\ c /\ d) ==> ~(a /\ b /\ c /\ d /\ ~e /\ ~f) ==> e \/ f`) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[OPEN_INTERIOR];
      REWRITE_TAC[GSYM closed] THEN USE_THEN "B'" (ACCEPT_TAC o el 1 o CONJUNCTS);
      USE_THEN "B'" (MP_TAC o el 5 o CONJUNCTS) THEN
      UNDISCH_TAC `interior b INTER frontier b':real^3->bool = {}` THEN SET_TAC[];
      MP_TAC(ISPEC `b':real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [USE_THEN "B'" (MP_TAC o el 5 o CONJUNCTS) THEN
    UNDISCH_TAC `interior b INTER frontier b':real^3->bool = {}` THEN
    UNDISCH_TAC `interior b' INTER interior b:real^3->bool = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^3->bool) SUBSET b'` ASSUME_TAC THENL
   [SUBGOAL_THEN `pl_ball 3 (b:real^3->bool)` MP_TAC THENL
     [UNDISCH_TAC `moi_s4x_local tt kk (f1:real^N->real^3) car dd r b` THEN
      SIMP_TAC[moi_s4x_local];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV
      [el 3 (CONJUNCTS(MATCH_MP MOI_S4YC_BALL_BASIC th))]) THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [UNDISCH_TAC `((:real^3) DIFF b') INTER interior b = {}` THEN SET_TAC[];
      USE_THEN "B'" (ACCEPT_TAC o el 1 o CONJUNCTS)];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`;
                `r':real^N->bool`] MOI_S4Y_SIMP3_OTHER_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                `r:real^N->bool`; `b:real^3->bool`; `u:real^N`] MOI_S4Y_PATCH_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DISJOINT b' (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u))` MP_TAC THENL
   [UNDISCH_TAC `moi_s4x_local tt kk (f1:real^N->real^3) car dd r' b'` THEN
    REWRITE_TAC[moi_s4x_local] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(b:real^3->bool) SUBSET b'` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Near a point x of b INTER F in no face disk of r, F lies in               *)
(* b.  Off the rims x is in the cell interior of one patch, which is open    *)
(* in the 2-sphere frontier C_v'' (MOI_S4YC_CELL2_OPEN), and F = A_v'' near *)
(* x.  On a rim of an edge g = vw, the open rim arc is open in the rim, so  *)
(* the patch and the splitting disk D_g'' have the same boundary near x and *)
(* glue to a neighbourhood of x in frontier C_v'' (MOI_S4YC_CELLS2_GLUE),    *)
(* and F = A_v'' UNION A_w'' near x.                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Y_EDGE_OTHER = prove
 (`!(tt:(real^N->bool)->bool) kk g v.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1) /\ {v} IN kk /\ v IN g
     ==> ?w. {w} IN kk /\ w IN g /\ ~(w = v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
    MOI_S4L_EDGE_VERTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `v:real^N = u1 \/ v = u2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(v:real^N) IN {v | v IN g /\ {v} IN kk}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]];
    EXISTS_TAC `u2:real^N` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[];
    EXISTS_TAC `u1:real^N` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[]]);;

let MOI_S4Y_CLOSED_UNIONS_FAM = prove
 (`!(P:A->bool) (f:A->real^3->bool).
     FINITE {x | P x} /\ (!x. P x ==> compact (f x)) ==> closed (UNIONS {f x | P x})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]);;

let MOI_S4Y_LOCAL_IN_A = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r b v x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     r IN moi_s34_simp kk (&3) /\ moi_s4x_local tt kk f1 car dd r b /\
     {v} IN kk /\ v IN r /\ x IN b /\ x IN IMAGE f1 (moi_s34_vb tt kk v) /\
     (!w. {w} IN kk /\ ~(w = v) ==> ~(x IN IMAGE f1 (moi_s34_vb tt kk w))) /\
     (!s. s IN moi_s34_simp kk (&2) /\ s SUBSET r ==> ~(x IN dd s))
     ==> ?W. open W /\ x IN W /\ IMAGE f1 (moi_s34_bd tt kk) INTER W SUBSET b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `v:real^N`; `x:real^3`] MOI_S4L_LOCAL_AV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `bp = UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk v) | s |
                 s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
         UNIONS {b INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                 g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r}` THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (b INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))
                  bp` ASSUME_TAC THENL
   [EXPAND_TAC "bp" THEN
    UNDISCH_TAC `moi_s4x_local tt kk (f1:real^N->real^3) car dd r b` THEN
    REWRITE_TAC[moi_s4x_local] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 4 o CONJUNCTS) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^3) IN bp)` ASSUME_TAC THENL
   [EXPAND_TAC "bp" THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
    STRIP_TAC THENL
     [ASM_MESON_TAC[];
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`;
                    `v:real^N`] MOI_S4Y_EDGE_OTHER) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                    `g:real^N->bool`] MOI_S4Y_SD_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^N` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `~((x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4Y_AV_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(el 4 (CONJUNCTS th)) THEN
    ASSUME_TAC(SET_RULE `!a u:real^3->bool. a SUBSET a UNION u` |> ISPECL
      [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
       `UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                g IN moi_s34_simp kk (&1) /\ v IN g}`] |>
      REWRITE_RULE[GSYM(el 5 (CONJUNCTS th))])) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `b:real^3->bool`]
    MOI_S4Y_BALL_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 12 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`; `x:real^3`]
    MOI_S4YC_SPHERE2_CHART) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`; `x:real^3`;
                 `b INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`; `bp:real^3->bool`]
    MOI_S4YC_CELL2_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[IN_DIFF; IN_INTER]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `oo INTER vv:real^3->bool` THEN ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN
  ASM SET_TAC[]);;

let SPDR9_RSI_SET = prove
 (`!B S rg au su v1 v4 b brho Vu:real^3->bool.
     B INTER S = rg ==> au SUBSET B ==> au SUBSET su ==>
     rg INTER v1 SUBSET b INTER S DIFF brho ==> su INTER v4 SUBSET S UNION b INTER Vu ==>
     au INTER v4 INTER v1 SUBSET b /\ su INTER v4 INTER v1 SUBSET S UNION b INTER Vu`,
  SET_TAC[]);;

let MOI_S4Y_RIM_SIDE_IN = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r b g u x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     r IN moi_s34_simp kk (&3) /\ moi_s4x_local tt kk f1 car dd r b /\
     g IN moi_s34_simp kk (&1) /\ g SUBSET r /\ {u} IN kk /\ u IN g /\
     x IN b /\ x IN IMAGE f1 (moi_s34_sd tt kk g) /\
     (!s. s IN moi_s34_simp kk (&2) /\ s SUBSET r ==> ~(x IN dd s))
     ==> ?V. open V /\ x IN V /\
             IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) INTER V SUBSET b /\
             frontier (IMAGE f1 (moi_s34_vb tt kk u)) INTER V SUBSET
             IMAGE f1 (moi_s34_sd tt kk g) UNION (b INTER IMAGE f1 (moi_s34_vb tt kk u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^N) IN r` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                `r:real^N->bool`; `b:real^3->bool`] MOI_S4Y_LOCAL_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `u:real^N` (el 1 (CONJUNCTS th))) THEN
                       MP_TAC(SPEC `g:real^N->bool` (el 2 (CONJUNCTS th)))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `brho = UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                               IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | s |
                             s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r}` THEN
  DISCH_TAC THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `bp = UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk u) | s |
                 s IN moi_s34_simp kk (&2) /\ u IN s /\ s SUBSET r} UNION
         UNIONS {b INTER IMAGE f1 (moi_s34_sd tt kk g') | g' |
                 g' IN moi_s34_simp kk (&1) /\ u IN g' /\ g' SUBSET r}` THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `g:real^N->bool`] MOI_S4Y_SD_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `rg = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun k -> ASSUME_TAC(el k (CONJUNCTS th))) [0;1;2;3;4] THEN
    MP_TAC(SPEC `u:real^N` (el 5 (CONJUNCTS th)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `b:real^3->bool`]
    MOI_S4Y_BALL_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `g:real^N->bool` (el 13 (CONJUNCTS th))) THEN
    MP_TAC(SPEC `u:real^N` (el 12 (CONJUNCTS th)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `u:real^N`] MOI_S4Y_AV_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `su = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u))` THEN
  ABBREV_TAC `au = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC(el 4 (CONJUNCTS th)) THEN
    MP_TAC(CONJ (el 0 (CONJUNCTS th)) (el 5 (CONJUNCTS th)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP (SET_RULE
    `(f:real^3->bool) INTER c = a ==> a SUBSET f`)) MP_TAC) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP (SET_RULE
    `(s:real^3->bool) = a UNION u ==> a SUBSET s`) th) THEN
    ASSUME_TAC(MATCH_MP (SET_RULE `(s:real^3->bool) = a UNION UNIONS f ==> UNIONS f SUBSET s`) th)) THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET su` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                        g IN moi_s34_simp kk (&1) /\ u IN g}` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN f ==> a SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the open rim arc is open in the rim *)
  SUBGOAL_THEN `~((x:real^3) IN brho)` ASSUME_TAC THENL
   [EXPAND_TAC "brho" THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`; `rg:real^3->bool`;
                 `x:real^3`] MOI_S4YC_CELL2_BD_CHART) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`rg:real^3->bool`; `x:real^3`;
                 `b INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`; `brho:real^3->bool`]
    MOI_S4YC_CELL1_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DIFF; IN_INTER] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^3->bool` STRIP_ASSUME_TAC) THEN
  (* away from the face disks and the other splitting disks of r *)
  ABBREV_TAC `ud = UNIONS {(dd:(real^N->bool)->real^3->bool) s | s |
                           s IN moi_s34_simp kk (&2) /\ s SUBSET r}` THEN
  ABBREV_TAC `ug = UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g') | g' |
                           g' IN moi_s34_simp kk (&1) /\ g' SUBSET r /\ ~(g' = g)}` THEN
  SUBGOAL_THEN `closed (ud:real^3->bool) /\ closed (ug:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `r:real^N->bool`]
      MOI_S4Y_FINITE_FACES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(r:real^N->bool) IN moi_s34_simp kk (&3)` THEN
      SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
      DISCH_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "ud" THEN MATCH_MP_TAC MOI_S4Y_CLOSED_UNIONS_FAM THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{q:real^N->bool | q IN kk /\ q SUBSET r}` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s34_simp] THEN MESON_TAC[];
        X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
        UNDISCH_TAC `moi_s34_fdisk tt kk (f1:real^N->real^3) car dd` THEN
        REWRITE_TAC[moi_s34_fdisk] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS o CONJUNCT1) THEN SIMP_TAC[]];
      EXPAND_TAC "ug" THEN MATCH_MP_TAC MOI_S4Y_CLOSED_UNIONS_FAM THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{q:real^N->bool | q IN kk /\ q SUBSET r}` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s34_simp] THEN MESON_TAC[];
        X_GEN_TAC `g':real^N->bool` THEN STRIP_TAC THEN
        MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                      `ep:real^N->real`; `f1:real^N->real^3`;
                      `car:(real^N->bool)->real^3->bool`; `g':real^N->bool`] MOI_S4Y_SD_FACTS) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^3) IN ud) /\ ~((x:real^3) IN ug)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "ud" THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      UNDISCH_TAC `!s. s IN moi_s34_simp kk (&2) /\ s SUBSET r
                       ==> ~((x:real^3) IN (dd:(real^N->bool)->real^3->bool) s)` THEN
      MESON_TAC[];
      EXPAND_TAC "ug" THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `g':real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
        MOI_S4L_IMG_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`g:real^N->bool`; `g':real^N->bool`] o CONJUNCT1) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `bp SUBSET ud UNION ug UNION
                (b INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["bp"; "ud"; "ug"] THEN
    REWRITE_TAC[SUBSET; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_CASES_TAC `g':real^N->bool = g` THENL
       [DISJ2_TAC THEN DISJ2_TAC THEN UNDISCH_TAC `g':real^N->bool = g` THEN
        DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `g':real^N->bool` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `b INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET bp`
  ASSUME_TAC THENL
   [EXPAND_TAC "bp" THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN f ==> a SUBSET u UNION UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bp INTER ((:real^3) DIFF (ud UNION ug)) SUBSET
                b INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` ASSUME_TAC THENL
   [UNDISCH_TAC `bp SUBSET ud UNION ug UNION
                 (b INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) DIFF rg)
                         (b INTER IMAGE f1 (moi_s34_vb tt kk u) DIFF bp)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`b INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u) SUBSET au`;
      `(au:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER IMAGE f1 (moi_s34_sd tt kk g) = rg`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`su:real^3->bool`; `x:real^3`] MOI_S4YC_SPHERE2_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET su` THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
    MESON_TAC[SUBSET];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`su:real^3->bool`; `x:real^3`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`; `rg:real^3->bool`;
                 `b INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u)`; `bp:real^3->bool`]
    MOI_S4YC_CELLS2_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`b INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u) SUBSET au`;
        `(au:real^3->bool) SUBSET su`] THEN SET_TAC[];
      UNDISCH_TAC `b INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET rg` THEN
      REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `v1 INTER ((:real^3) DIFF (ud UNION ug))` THEN
      ASM_SIMP_TAC[OPEN_INTER; GSYM closed; CLOSED_UNION; IN_INTER; IN_DIFF; IN_UNIV;
                   IN_UNION] THEN
      MAP_EVERY UNDISCH_TAC
       [`rg INTER v1 SUBSET b INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) DIFF brho`;
        `bp INTER ((:real^3) DIFF (ud UNION ug)) SUBSET
         b INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`;
        `b INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET bp`;
        `b INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET rg`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v4:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v4 INTER v1:real^3->bool` THEN ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN
  MAP_EVERY UNDISCH_TAC
   [`su INTER v4 SUBSET IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) UNION
     b INTER IMAGE f1 (moi_s34_vb tt kk u)`;
    `rg INTER v1 SUBSET b INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) DIFF brho`;
    `(au:real^3->bool) SUBSET su`;
    `(au:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
    `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER IMAGE f1 (moi_s34_sd tt kk g) = rg`] THEN
  MATCH_ACCEPT_TAC SPDR9_RSI_SET);;

let MOI_S4Y_LOCAL_IN = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r b x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     r IN moi_s34_simp kk (&3) /\ moi_s4x_local tt kk f1 car dd r b /\
     x IN b /\ x IN IMAGE f1 (moi_s34_bd tt kk) /\
     (!s. s IN moi_s34_simp kk (&2) /\ s SUBSET r ==> ~(x IN dd s))
     ==> ?W. open W /\ x IN W /\ IMAGE f1 (moi_s34_bd tt kk) INTER W SUBSET b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?v:real^N. {v} IN kk /\ (x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
      MOI_S4Y_FN_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP (SET_RULE
      `(a:real^3->bool) SUBSET n /\ n = u ==> a SUBSET u`)
      (CONJ (el 1 (CONJUNCTS th)) (el 0 (CONJUNCTS th))))) THEN
    REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                `r:real^N->bool`; `b:real^3->bool`] MOI_S4Y_LOCAL_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "avv" o el 3 o CONJUNCTS) THEN
  SUBGOAL_THEN `!w:real^N. {w} IN kk /\ (x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)
                ==> w IN r` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "avv" (MP_TAC o SPEC `w:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^3) IN b` THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "avv" (K ALL_TAC) THEN
  SUBGOAL_THEN `(v:real^N) IN r` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `!w:real^N. {w} IN kk /\ ~(w = v)
                            ==> ~((x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))`
  THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `b:real^3->bool`;
                  `v:real^N`; `x:real^3`] MOI_S4Y_LOCAL_IN_A) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC o
    REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  SUBGOAL_THEN `(w:real^N) IN r` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `v:real^N`] MOI_S4Y_AV_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `v:real^N`; `w:real^N`; `x:real^3`] MOI_S4L_AV_NO_OTHER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`; `w:real^N`]
    MOI_S4L_EDGE_SD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,w] SUBSET r` ASSUME_TAC THENL
   [UNDISCH_TAC `(r:real^N->bool) IN moi_s34_simp kk (&3)` THEN
    REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `convex (r:real^N->bool)` MP_TAC THENL
     [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4K_TUBE_FACTS) THEN
      ASM_REWRITE_TAC[lf_simplicial_complex] THEN STRIP_TAC THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[v,w]))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN IMAGE (f:real^N->real^3) s ==> x IN IMAGE f t`) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `v:real^N`; `w:real^N`; `x:real^3`] MOI_S4L_LOCAL_AV_AW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `b:real^3->bool`;
                `segment[v:real^N,w]`; `v:real^N`; `x:real^3`] MOI_S4Y_RIM_SIDE_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `b:real^3->bool`;
                `segment[v:real^N,w]`; `w:real^N`; `x:real^3`] MOI_S4Y_RIM_SIDE_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `vw:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `oo INTER vv INTER vw:real^3->bool` THEN ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN
  MAP_EVERY UNDISCH_TAC
   [`IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER oo SUBSET
     IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
     IMAGE f1 (moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER vv SUBSET b`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w INTER moi_s34_bd tt kk) INTER vw SUBSET b`] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* (G1), two distinct tetra balls meet exactly in the face                   *)
(* disks of their common 2-faces.  A common point in no face disk lies in F  *)
(* and in both frontiers, F lies in both balls near it, so the frontiers     *)
(* agree near it and the balls glue to a neighbourhood (MOI_S4YC_BALLS_GLUE)*)
(* of a point of F, which contradicts F = frontier of f1(N).                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Y_NOT_INT_UNION = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car b b' x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     b INTER IMAGE f1 (moi_s34_nb tt kk) SUBSET IMAGE f1 (moi_s34_bd tt kk) /\
     b' INTER IMAGE f1 (moi_s34_nb tt kk) SUBSET IMAGE f1 (moi_s34_bd tt kk) /\
     x IN IMAGE f1 (moi_s34_bd tt kk)
     ==> ~(x IN interior (b UNION b'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
    MOI_S4Y_FN_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interior (b UNION b') INTER
                  interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) = {})` MP_TAC THENL
   [MP_TAC(ISPECL [`interior (b UNION b'):real^3->bool`;
                   `interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^3` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
    DISCH_THEN(MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN b UNION b'` MP_TAC THENL
     [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` MP_TAC THENL
     [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`b INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) SUBSET IMAGE f1 (moi_s34_bd tt kk)`;
      `b' INTER IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) SUBSET IMAGE f1 (moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER
       interior (IMAGE f1 (moi_s34_nb tt kk)) = {}`;
      `(z:real^3) IN interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk))`] THEN
    SET_TAC[]]);;

let SPDR9_G1_SET = prove
 (`!P w1 w2 ud ua ub b b' ib ib' fb fb':real^3->bool.
     P INTER w2 SUBSET b' ==> P INTER w1 SUBSET b ==> fb' = b' DIFF ib' ==>
     fb' SUBSET ub UNION P ==> b' INTER P SUBSET fb' ==> fb = b DIFF ib ==>
     fb SUBSET ua UNION P ==> b INTER P SUBSET fb ==> ua SUBSET ud /\ ub SUBSET ud ==>
     (w1 INTER w2 INTER ((:real^3) DIFF ud)) INTER (b DIFF ib) =
     (w1 INTER w2 INTER ((:real^3) DIFF ud)) INTER (b' DIFF ib')`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REPLICATE_TAC 2 DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  ASM SET_TAC[]);;

let MOI_S4Y_G1 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r b r' b'.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     r IN moi_s34_simp kk (&3) /\ moi_s4x_local tt kk f1 car dd r b /\
     r' IN moi_s34_simp kk (&3) /\ moi_s4x_local tt kk f1 car dd r' b' /\ ~(r = r')
     ==> b INTER b' =
         UNIONS {dd s | s | s IN moi_s34_simp kk (&2) /\ s SUBSET r /\ s SUBSET r'}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `b:real^3->bool`]
    MOI_S4Y_BALL_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "B")] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r':real^N->bool`; `b':real^3->bool`]
    MOI_S4Y_BALL_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "B'")] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `b:real^3->bool`;
                `r':real^N->bool`; `b':real^3->bool`] MOI_S4Y_INTERIOR_MISS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r':real^N->bool`; `b':real^3->bool`;
                `r:real^N->bool`; `b:real^3->bool`] MOI_S4Y_INTERIOR_MISS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                `r:real^N->bool`; `b:real^3->bool`] MOI_S4Y_LOCAL_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASSUME_TAC(el 0 (CONJUNCTS th)) THEN
    LABEL_TAC "avs" (el 4 (CONJUNCTS th))) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                `r':real^N->bool`; `b':real^3->bool`] MOI_S4Y_LOCAL_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASSUME_TAC(el 0 (CONJUNCTS th)) THEN
    LABEL_TAC "avs'" (el 4 (CONJUNCTS th))) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^N->bool` THEN
    STRIP_TAC THEN REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [USE_THEN "B" (fun th -> MP_TAC(SPEC `s:real^N->bool` (el 9 (CONJUNCTS th))) THEN
        MP_TAC(el 5 (CONJUNCTS th))) THEN
      DISCH_THEN SUBST1_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]];
      USE_THEN "B'" (fun th -> MP_TAC(SPEC `s:real^N->bool` (el 9 (CONJUNCTS th))) THEN
        MP_TAC(el 5 (CONJUNCTS th))) THEN
      DISCH_THEN SUBST1_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]]]] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INTER] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  ASM_CASES_TAC `?s. s IN moi_s34_simp kk (&2) /\ s SUBSET r /\
                     (x:real^3) IN (dd:(real^N->bool)->real^3->bool) s` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "avs'" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `?s. s IN moi_s34_simp kk (&2) /\ s SUBSET r' /\
                     (x:real^3) IN (dd:(real^N->bool)->real^3->bool) s` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "avs" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN `!s. s IN moi_s34_simp kk (&2) /\ s SUBSET r
                    ==> ~((x:real^3) IN (dd:(real^N->bool)->real^3->bool) s)` (LABEL_TAC "nr") THENL
   [UNDISCH_TAC `~(?s. s IN moi_s34_simp kk (&2) /\ s SUBSET r /\
                       (x:real^3) IN (dd:(real^N->bool)->real^3->bool) s)` THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN moi_s34_simp kk (&2) /\ s SUBSET r'
                    ==> ~((x:real^3) IN (dd:(real^N->bool)->real^3->bool) s)` (LABEL_TAC "nr'") THENL
   [UNDISCH_TAC `~(?s. s IN moi_s34_simp kk (&2) /\ s SUBSET r' /\
                       (x:real^3) IN (dd:(real^N->bool)->real^3->bool) s)` THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN frontier b /\ x IN frontier b'` STRIP_ASSUME_TAC THENL
   [USE_THEN "B" (fun th -> REWRITE_TAC[el 5 (CONJUNCTS th)]) THEN
    USE_THEN "B'" (fun th -> REWRITE_TAC[el 5 (CONJUNCTS th)]) THEN
    MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN b`; `(x:real^3) IN b'`; `interior b INTER b':real^3->bool = {}`;
      `interior b' INTER b:real^3->bool = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` ASSUME_TAC THENL
   [USE_THEN "B" (MP_TAC o SPEC `x:real^3` o GEN_REWRITE_RULE I [SUBSET] o el 8 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    USE_THEN "nr" MP_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`; `b:real^3->bool`;
                `x:real^3`] MOI_S4Y_LOCAL_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r':real^N->bool`; `b':real^3->bool`;
                `x:real^3`] MOI_S4Y_LOCAL_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real^3->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `ud = UNIONS {(dd:(real^N->bool)->real^3->bool) s | s |
                           s IN moi_s34_simp kk (&2) /\ (s SUBSET r \/ s SUBSET r')}` THEN
  SUBGOAL_THEN `closed (ud:real^3->bool) /\ ~((x:real^3) IN ud)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "ud" THEN MATCH_MP_TAC MOI_S4Y_CLOSED_UNIONS_FAM THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{q:real^N->bool | q IN kk /\ q SUBSET r} UNION
                    {q:real^N->bool | q IN kk /\ q SUBSET r'}` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S4Y_FINITE_FACES THEN
          EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
          MAP_EVERY UNDISCH_TAC [`(r:real^N->bool) IN moi_s34_simp kk (&3)`;
                                 `(r':real^N->bool) IN moi_s34_simp kk (&3)`] THEN
          SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
          REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; moi_s34_simp] THEN MESON_TAC[]];
        X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
        UNDISCH_TAC `moi_s34_fdisk tt kk (f1:real^N->real^3) car dd` THEN
        REWRITE_TAC[moi_s34_fdisk] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS o CONJUNCT1) THEN SIMP_TAC[]];
      EXPAND_TAC "ud" THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `s:real^N->bool` THEN
      USE_THEN "nr" (MP_TAC o SPEC `s:real^N->bool`) THEN
      USE_THEN "nr'" (MP_TAC o SPEC `s:real^N->bool`) THEN CONV_TAC TAUT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:real^3->bool`; `b':real^3->bool`; `x:real^3`] MOI_S4YC_BALLS_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `w1 INTER w2 INTER ((:real^3) DIFF ud)` THEN
      ASM_SIMP_TAC[OPEN_INTER; GSYM closed; IN_INTER; IN_DIFF; IN_UNIV] THEN
      SUBGOAL_THEN
       `UNIONS {(dd:(real^N->bool)->real^3->bool) s | s | s IN moi_s34_simp kk (&2) /\ s SUBSET r}
        SUBSET ud /\
        UNIONS {(dd:(real^N->bool)->real^3->bool) s | s | s IN moi_s34_simp kk (&2) /\ s SUBSET r'}
        SUBSET ud` MP_TAC THENL
       [EXPAND_TAC "ud" THEN CONJ_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN
        GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_THM] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      USE_THEN "B" (fun th -> MP_TAC(el 7 (CONJUNCTS th)) THEN MP_TAC(el 8 (CONJUNCTS th)) THEN
        MP_TAC(el 5 (CONJUNCTS th))) THEN
      USE_THEN "B'" (fun th -> MP_TAC(el 7 (CONJUNCTS th)) THEN MP_TAC(el 8 (CONJUNCTS th)) THEN
        MP_TAC(el 5 (CONJUNCTS th))) THEN
      ABBREV_TAC `ua = UNIONS {(dd:(real^N->bool)->real^3->bool) s | s |
                               s IN moi_s34_simp kk (&2) /\ s SUBSET r}` THEN
      ABBREV_TAC `ub = UNIONS {(dd:(real^N->bool)->real^3->bool) s | s |
                               s IN moi_s34_simp kk (&2) /\ s SUBSET r'}` THEN
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER w1 SUBSET b`;
        `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER w2 SUBSET b'`] THEN
      MATCH_ACCEPT_TAC SPDR9_G1_SET;
      MP_TAC(ISPEC `b':real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `interior b INTER b':real^3->bool = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `b:real^3->bool`; `b':real^3->bool`; `x:real^3`] MOI_S4Y_NOT_INT_UNION) THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "B" (fun th -> REWRITE_TAC[el 6 (CONJUNCTS th)]) THEN
  USE_THEN "B'" (fun th -> REWRITE_TAC[el 6 (CONJUNCTS th)]));;

(* ------------------------------------------------------------------------- *)
(* (G3), at an interior edge g the rim arcs of the 3-simplices               *)
(* at g cover the rim f1(D_g INTER Bd N).  Their union U is closed and       *)
(* nonempty, and open in the rim: at an interior point of an arc by         *)
(* MOI_S4YC_CELL1_OPEN; at an end, a face point of a 2-face s at g, by       *)
(* gluing the arcs of the two 3-simplices at s (MOI_S4YC_CELLS1_GLUE), whose *)
(* open arcs are disjoint by (G1).  The rim is connected.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Y_CELL_NONEMPTY = prove
 (`!n (c:real^N->bool) bd. pl_cell_with_boundary n c bd ==> ~(c = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(k:real^N->bool = {})` MP_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `&n simplex ({}:real^N->bool)` THEN REWRITE_TAC[SIMPLEX_EMPTY] THEN
    INT_ARITH_TAC;
    ASM SET_TAC[]]);;

let MOI_S4Y_FACE_DISK_RIM = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd s g.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     s IN moi_s34_simp kk (&2) /\ g IN moi_s34_simp kk (&1) /\ ~(g SUBSET s)
     ==> dd s INTER IMAGE f1 (moi_s34_sd tt kk g) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
    MOI_S4L_EDGE_VERTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?w:real^N. {w} IN kk /\ w IN g /\ ~(w IN s)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    UNDISCH_TAC `~((g:real^N->bool) SUBSET s)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `g:real^N->bool = segment[u1,u2]` THEN DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `convex (s:real^N->bool)` MP_TAC THENL
     [UNDISCH_TAC `(s:real^N->bool) IN moi_s34_simp kk (&2)` THEN
      REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4K_TUBE_FACTS) THEN
      ASM_REWRITE_TAC[lf_simplicial_complex] THEN STRIP_TAC THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT ((dd:(real^N->bool)->real^3->bool) s)
                         (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))` MP_TAC THENL
   [UNDISCH_TAC `moi_s34_fdisk tt kk (f1:real^N->real^3) car dd` THEN
    REWRITE_TAC[moi_s34_fdisk] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^N` o el 3 o CONJUNCTS) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `g:real^N->bool`] MOI_S4Y_SD_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^N` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  SET_TAC[]);;

let MOI_S4Y_RIM_OPEN = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g r x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     (!r. r IN moi_s34_simp kk (&3) ==> moi_s4x_local tt kk f1 car dd r (rr r)) /\
     g IN moi_s34_simp kk (&1) /\ ~(g SUBSET complex_boundary kk) /\
     r IN moi_s34_simp kk (&3) /\ g SUBSET r /\
     x IN rr r /\ x IN IMAGE f1 (moi_s34_sd tt kk g)
     ==> ?v. open v /\ x IN v /\
             IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) INTER v SUBSET
             UNIONS {rr r' INTER IMAGE f1 (moi_s34_sd tt kk g) | r' |
                     r' IN moi_s34_simp kk (&3) /\ g SUBSET r'}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s4x_local tt kk (f1:real^N->real^3) car dd r (rr r)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `U = UNIONS {(rr:(real^N->bool)->real^3->bool) r' INTER
                            IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | r' |
                          r' IN moi_s34_simp kk (&3) /\ g SUBSET r'}` THEN
  SUBGOAL_THEN `!r':real^N->bool. r' IN moi_s34_simp kk (&3) /\ g SUBSET r'
                ==> (rr:(real^N->bool)->real^3->bool) r' INTER
                    IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET U` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "U" THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN f ==> a SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `r':real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `g:real^N->bool`] MOI_S4Y_SD_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(el 1 (CONJUNCTS th)) THEN ASSUME_TAC(el 2 (CONJUNCTS th))) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`;
                `(rr:(real^N->bool)->real^3->bool) r`] MOI_S4Y_BALL_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 13 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`;
                 `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`;
                 `x:real^3`] MOI_S4YC_CELL2_BD_CHART) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                `r:real^N->bool`; `(rr:(real^N->bool)->real^3->bool) r`] MOI_S4Y_LOCAL_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 2 o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_CASES_TAC `?s. s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r /\
                     (x:real^3) IN (dd:(real^N->bool)->real^3->bool) s` THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`;
                   `x:real^3`;
                   `(rr:(real^N->bool)->real^3->bool) r INTER
                    IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`;
                   `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                              IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | s |
                            s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r}`]
      MOI_S4YC_CELL1_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF; IN_INTER] THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
      UNDISCH_TAC `~(?s. s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r /\
                         (x:real^3) IN (dd:(real^N->bool)->real^3->bool) s)` THEN
      MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(rr:(real^N->bool)->real^3->bool) r INTER
                IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`kk:(real^N->bool)->bool`; `s:real^N->bool`; `r:real^N->bool`]
    MOI_S4Y_FACE_TWO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(g:real^N->bool) SUBSET r2` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4x_local tt kk (f1:real^N->real^3) car dd r2 (rr r2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                `r2:real^N->bool`; `(rr:(real^N->bool)->real^3->bool) r2`] MOI_S4Y_LOCAL_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 2 o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r2:real^N->bool`;
                `(rr:(real^N->bool)->real^3->bool) r2`] MOI_S4Y_BALL_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 13 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`;
                `(rr:(real^N->bool)->real^3->bool) r`; `r2:real^N->bool`;
                `(rr:(real^N->bool)->real^3->bool) r2`] MOI_S4Y_G1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `uo = UNIONS {(dd:(real^N->bool)->real^3->bool) s' | s' |
                           s' IN moi_s34_simp kk (&2) /\ (s' SUBSET r \/ s' SUBSET r2) /\
                           ~(s' = s)}` THEN
  SUBGOAL_THEN `closed (uo:real^3->bool) /\ ~((x:real^3) IN uo)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "uo" THEN MATCH_MP_TAC MOI_S4Y_CLOSED_UNIONS_FAM THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{q:real^N->bool | q IN kk /\ q SUBSET r} UNION
                    {q:real^N->bool | q IN kk /\ q SUBSET r2}` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S4Y_FINITE_FACES THEN
          EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
          MAP_EVERY UNDISCH_TAC [`(r:real^N->bool) IN moi_s34_simp kk (&3)`;
                                 `(r2:real^N->bool) IN moi_s34_simp kk (&3)`] THEN
          SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
          REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; moi_s34_simp] THEN MESON_TAC[]];
        X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
        UNDISCH_TAC `moi_s34_fdisk tt kk (f1:real^N->real^3) car dd` THEN
        REWRITE_TAC[moi_s34_fdisk] THEN
        DISCH_THEN(MP_TAC o SPEC `s':real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS o CONJUNCT1) THEN SIMP_TAC[]];
      EXPAND_TAC "uo" THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
      UNDISCH_TAC `moi_s34_fdisk tt kk (f1:real^N->real^3) car dd` THEN
      REWRITE_TAC[moi_s34_fdisk] THEN
      DISCH_THEN(MP_TAC o SPECL [`s':real^N->bool`; `s:real^N->bool`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
       EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?v. open v /\ (x:real^3) IN v /\
        v INTER UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                          IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | s |
                        s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r} =
        v INTER UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                          IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | s |
                        s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r2}`
  ASSUME_TAC THENL
   [EXISTS_TAC `(:real^3) DIFF uo` THEN ASM_REWRITE_TAC[GSYM closed; IN_DIFF; IN_UNIV] THEN
    EXPAND_TAC "uo" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN
    MAP_EVERY UNDISCH_TAC [`(s:real^N->bool) IN moi_s34_simp kk (&2)`;
                           `(g:real^N->bool) SUBSET s`; `(s:real^N->bool) SUBSET r`;
                           `(s:real^N->bool) SUBSET r2`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT ((rr:(real^N->bool)->real^3->bool) r INTER
              IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) DIFF
              UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                        IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | s |
                      s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r})
             ((rr:(real^N->bool)->real^3->bool) r2 INTER
              IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) DIFF
              UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                        IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | s |
                      s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r2})`
  ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `DISJOINT ((a:real^3->bool) DIFF b) (c DIFF d) <=>
                          !y. y IN a /\ y IN c ==> y IN b \/ y IN d`] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN DISJ1_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN (rr:(real^N->bool)->real^3->bool) r INTER rr r2` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s'':real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN EXISTS_TAC `s'':real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `s'':real^N->bool`; `g:real^N->bool`]
      MOI_S4Y_FACE_DISK_RIM) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`;
                 `x:real^3`;
                 `(rr:(real^N->bool)->real^3->bool) r INTER
                  IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`;
                 `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                            IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | s |
                          s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r}`;
                 `(rr:(real^N->bool)->real^3->bool) r2 INTER
                  IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`;
                 `UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                            IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | s |
                          s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r2}`]
    MOI_S4YC_CELLS1_GLUE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `(rr:(real^N->bool)->real^3->bool) r INTER
              IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) UNION
              rr r2 INTER IMAGE f1 (moi_s34_sd tt kk g)` THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4Y_G3 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr g.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     (!r. r IN moi_s34_simp kk (&3) ==> moi_s4x_local tt kk f1 car dd r (rr r)) /\
     g IN moi_s34_simp kk (&1) /\ ~(g SUBSET complex_boundary kk)
     ==> IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
         UNIONS {rr r | r | r IN moi_s34_simp kk (&3) /\ g SUBSET r}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `U = UNIONS {(rr:(real^N->bool)->real^3->bool) r' INTER
                            IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | r' |
                          r' IN moi_s34_simp kk (&3) /\ g SUBSET r'}` THEN
  SUBGOAL_THEN `(U:real^3->bool) SUBSET
                UNIONS {(rr:(real^N->bool)->real^3->bool) r | r |
                        r IN moi_s34_simp kk (&3) /\ g SUBSET r}` MP_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN f ==> a INTER c SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `(a:real^3->bool) SUBSET u ==> u SUBSET b ==> a SUBSET b`) THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `g:real^N->bool`] MOI_S4Y_SD_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(el 1 (CONJUNCTS th)) THEN ASSUME_TAC(el 3 (CONJUNCTS th))) THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN moi_s34_simp kk (&3) /\ g SUBSET r
                    ==> moi_s4x_local tt kk (f1:real^N->real^3) car dd r
                          ((rr:(real^N->bool)->real^3->bool) r)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:real^3->bool) SUBSET
                IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`;
                  `(rr:(real^N->bool)->real^3->bool) r`] MOI_S4Y_BALL_FACTS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 13 o CONJUNCTS) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (U:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC MOI_S4Y_CLOSED_UNIONS_FAM THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
        MOI_S4L_EDGE_VERTS) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{q:real^N->bool | q IN kk /\ u1 IN q}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S4Y_FINITE_AT THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u1:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
        GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM; moi_s34_simp] THEN
        X_GEN_TAC `q:real^N->bool` THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(g:real^N->bool) SUBSET q` THEN
        UNDISCH_TAC `g:real^N->bool = segment[u1,u2]` THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPECL [`u1:real^N`; `u2:real^N`] ENDS_IN_SEGMENT) THEN SET_TAC[]];
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN MATCH_MP_TAC COMPACT_INTER THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`;
                    `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                    `r:real^N->bool`; `(rr:(real^N->bool)->real^3->bool) r`]
        MOI_S4Y_BALL_FACTS) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(U:real^3->bool = {})` ASSUME_TAC THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
      MOI_S4Y_EDGE_TETRA) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                  `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                  `r:real^N->bool`; `(rr:(real^N->bool)->real^3->bool) r`]
      MOI_S4Y_LOCAL_CLAUSES) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o el 2 o CONJUNCTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_S4Y_CELL_NONEMPTY) THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) SUBSET u ==> ~(a = {}) ==> ~(u = {})`) THEN
    EXPAND_TAC "U" THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN f ==> a SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean
                  (IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk))) U`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?r. r IN moi_s34_simp kk (&3) /\ g SUBSET r /\
                      (y:real^3) IN (rr:(real^N->bool)->real^3->bool) r /\
                      y IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN U` THEN EXPAND_TAC "U" THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                  `g:real^N->bool`; `r:real^N->bool`; `y:real^3`] MOI_S4Y_RIM_OPEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) INTER v` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk))`
  MP_TAC THENL
   [UNDISCH_TAC `pl_cell_with_boundary 2 (IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))
                   (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk))` THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN DISCH_THEN(MP_TAC o SPEC `U:real^3->bool`) THEN
  ASM_SIMP_TAC[CLOSED_SUBSET] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Local covering of the sphere S_v = frontier C_v'' at an                  *)
(* interior vertex v by the patches at v and the splitting disks at v, away *)
(* from the finitely many corners (face points on rims): inside a disk or a *)
(* patch (MOI_S4YC_CELL2_OPEN), on a rim (MOI_S4Y_RIM_SIDE_IN after (G3)),  *)
(* on a face arc (MOI_S4YC_CELLS2_GLUE with the second 3-simplex at the     *)
(* face, whose open patch is disjoint by (G1)).                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Y_PATCH_RIM_IN_BD = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd r b v g.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     r IN moi_s34_simp kk (&3) /\ moi_s4x_local tt kk f1 car dd r b /\
     {v} IN kk /\ v IN r /\ g IN moi_s34_simp kk (&1) /\ v IN g
     ==> b INTER IMAGE f1 (moi_s34_sd tt kk g) SUBSET
         UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                 s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
         UNIONS {b INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                 g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(g:real^N->bool) SUBSET r` THENL
   [MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN f ==> a SUBSET u UNION UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
    MOI_S4L_EDGE_VERTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?w:real^N. {w} IN kk /\ w IN g /\ ~(w IN r)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    UNDISCH_TAC `~((g:real^N->bool) SUBSET r)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `g:real^N->bool = segment[u1,u2]` THEN DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `convex (r:real^N->bool)` MP_TAC THENL
     [UNDISCH_TAC `(r:real^N->bool) IN moi_s34_simp kk (&3)` THEN
      REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] MOI_S4K_TUBE_FACTS) THEN
      ASM_REWRITE_TAC[lf_simplicial_complex] THEN STRIP_TAC THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                `r:real^N->bool`; `b:real^3->bool`] MOI_S4Y_LOCAL_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^N` o el 3 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `g:real^N->bool`] MOI_S4Y_SD_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^N` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  SET_TAC[]);;

let MOI_S4Y_FACE_ARC_GLUE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v r s x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     (!r. r IN moi_s34_simp kk (&3) ==> moi_s4x_local tt kk f1 car dd r (rr r)) /\
     {v} IN kk /\ ~(v IN complex_boundary kk) /\
     r IN moi_s34_simp kk (&3) /\ s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r /\
     x IN dd s /\ x IN IMAGE f1 (moi_s34_vb tt kk v) /\
     (!g. g IN moi_s34_simp kk (&1) /\ v IN g ==> ~(x IN IMAGE f1 (moi_s34_sd tt kk g)))
     ==> ?V. open V /\ x IN V /\
             frontier (IMAGE f1 (moi_s34_vb tt kk v)) INTER V SUBSET
             UNIONS {rr r' INTER IMAGE f1 (moi_s34_vb tt kk v) | r' |
                     r' IN moi_s34_simp kk (&3) /\ v IN r'}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`kk:(real^N->bool)->bool`; `s:real^N->bool`; `r:real^N->bool`]
    MOI_S4Y_FACE_TWO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^N) IN r /\ v IN r2` STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4x_local tt kk (f1:real^N->real^3) car dd r (rr r) /\
                moi_s4x_local tt kk (f1:real^N->real^3) car dd r2 (rr r2)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `uu = UNIONS {(rr:(real^N->bool)->real^3->bool) r' INTER
                             IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | r' |
                           r' IN moi_s34_simp kk (&3) /\ v IN r'}` THEN
  SUBGOAL_THEN `!r':real^N->bool. r' IN moi_s34_simp kk (&3) /\ v IN r'
                ==> (rr:(real^N->bool)->real^3->bool) r' INTER
                    IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET uu` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "uu" THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN f ==> a SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `r':real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `bp1 = UNIONS {(dd:(real^N->bool)->real^3->bool) s' INTER IMAGE (f1:real^N->real^3)
                    (moi_s34_vb tt kk v) | s' |
                  s' IN moi_s34_simp kk (&2) /\ v IN s' /\ s' SUBSET r} UNION
          UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                  g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r}` THEN
  ABBREV_TAC
   `bp2 = UNIONS {(dd:(real^N->bool)->real^3->bool) s' INTER IMAGE (f1:real^N->real^3)
                    (moi_s34_vb tt kk v) | s' |
                  s' IN moi_s34_simp kk (&2) /\ v IN s' /\ s' SUBSET r2} UNION
          UNIONS {(rr:(real^N->bool)->real^3->bool) r2 INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                  g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r2}` THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 ((rr:(real^N->bool)->real^3->bool) r INTER
                             IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) bp1 /\
    pl_cell_with_boundary 2 ((rr:(real^N->bool)->real^3->bool) r2 INTER
                             IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) bp2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                    `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                    `r:real^N->bool`; `(rr:(real^N->bool)->real^3->bool) r`]
        MOI_S4Y_LOCAL_CLAUSES) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 1 o CONJUNCTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "bp1" THEN REWRITE_TAC[];
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                    `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                    `r2:real^N->bool`; `(rr:(real^N->bool)->real^3->bool) r2`]
        MOI_S4Y_LOCAL_CLAUSES) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 1 o CONJUNCTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "bp2" THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4Y_AV_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `sv = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))` THEN
  DISCH_THEN(fun th -> ASSUME_TAC(el 4 (CONJUNCTS th)) THEN
    ASSUME_TAC(MATCH_MP (SET_RULE `(s:real^3->bool) = a UNION u ==> a SUBSET s`)
                        (el 5 (CONJUNCTS th))) THEN
    ASSUME_TAC(MATCH_MP (SET_RULE `(s:real^3->bool) = a UNION UNIONS f ==> UNIONS f SUBSET s`)
                        (el 5 (CONJUNCTS th)))) THEN
  SUBGOAL_THEN
   `(rr:(real^N->bool)->real^3->bool) r INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)
    SUBSET sv /\
    (rr:(real^N->bool)->real^3->bool) r2 INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)
    SUBSET sv` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THENL
     [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`;
                    `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                    `r:real^N->bool`; `(rr:(real^N->bool)->real^3->bool) r`]
        MOI_S4Y_BALL_FACTS);
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`;
                    `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                    `r2:real^N->bool`; `(rr:(real^N->bool)->real^3->bool) r2`]
        MOI_S4Y_BALL_FACTS)] THEN
    ANTS_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 12 o CONJUNCTS) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN (rr:(real^N->bool)->real^3->bool) r` ASSUME_TAC THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`;
                  `(rr:(real^N->bool)->real^3->bool) r`] MOI_S4Y_BALL_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `s:real^N->bool` (el 9 (CONJUNCTS th))) THEN
      MP_TAC(el 5 (CONJUNCTS th))) THEN
    DISCH_THEN SUBST1_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      MP_TAC(ASSUME `(x:real^3) IN (dd:(real^N->bool)->real^3->bool) s`) THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `uo = UNIONS {(dd:(real^N->bool)->real^3->bool) s' | s' |
                           s' IN moi_s34_simp kk (&2) /\ (s' SUBSET r \/ s' SUBSET r2) /\
                           ~(s' = s)} UNION
                   UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                           g IN moi_s34_simp kk (&1) /\ v IN g}` THEN
  SUBGOAL_THEN `closed (uo:real^3->bool) /\ ~((x:real^3) IN uo)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "uo" THEN MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THEN
      MATCH_MP_TAC MOI_S4Y_CLOSED_UNIONS_FAM THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{q:real^N->bool | q IN kk /\ q SUBSET r} UNION
                    {q:real^N->bool | q IN kk /\ q SUBSET r2}` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S4Y_FINITE_FACES THEN
          EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
          MAP_EVERY UNDISCH_TAC [`(r:real^N->bool) IN moi_s34_simp kk (&3)`;
                                 `(r2:real^N->bool) IN moi_s34_simp kk (&3)`] THEN
          SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
          REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; moi_s34_simp] THEN MESON_TAC[]];
        X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
        UNDISCH_TAC `moi_s34_fdisk tt kk (f1:real^N->real^3) car dd` THEN
        REWRITE_TAC[moi_s34_fdisk] THEN
        DISCH_THEN(MP_TAC o SPEC `s':real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS o CONJUNCT1) THEN SIMP_TAC[];
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{q:real^N->bool | q IN kk /\ v IN q}` THEN CONJ_TAC THENL
         [MATCH_MP_TAC MOI_S4Y_FINITE_AT THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
          ASM_REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
          REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s34_simp] THEN MESON_TAC[]];
        X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
        MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                      `ep:real^N->real`; `f1:real^N->real^3`;
                      `car:(real^N->bool)->real^3->bool`; `g:real^N->bool`] MOI_S4Y_SD_FACTS) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
      EXPAND_TAC "uo" THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; DE_MORGAN_THM] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
        UNDISCH_TAC `moi_s34_fdisk tt kk (f1:real^N->real^3) car dd` THEN
        REWRITE_TAC[moi_s34_fdisk] THEN
        DISCH_THEN(MP_TAC o SPECL [`s':real^N->bool`; `s:real^N->bool`] o CONJUNCT2) THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `!g. g IN moi_s34_simp kk (&1) /\ v IN g
                         ==> ~((x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))` THEN
        MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?vv. open vv /\ (x:real^3) IN vv /\ vv INTER bp1 = vv INTER bp2` ASSUME_TAC THENL
   [EXISTS_TAC `(:real^3) DIFF uo` THEN ASM_REWRITE_TAC[GSYM closed; IN_DIFF; IN_UNIV] THEN
    MAP_EVERY EXPAND_TAC ["uo"; "bp1"; "bp2"] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN
    MAP_EVERY UNDISCH_TAC [`(s:real^N->bool) IN moi_s34_simp kk (&2)`;
                           `(v:real^N) IN s`; `(s:real^N->bool) SUBSET r`;
                           `(s:real^N->bool) SUBSET r2`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT ((rr:(real^N->bool)->real^3->bool) r INTER
              IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) DIFF bp1)
             ((rr:(real^N->bool)->real^3->bool) r2 INTER
              IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) DIFF bp2)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`;
                  `(rr:(real^N->bool)->real^3->bool) r`; `r2:real^N->bool`;
                  `(rr:(real^N->bool)->real^3->bool) r2`] MOI_S4Y_G1) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
    REWRITE_TAC[SET_RULE `DISJOINT ((a:real^3->bool) DIFF b) (c DIFF d) <=>
                          !y. y IN a /\ y IN c ==> y IN b \/ y IN d`] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN DISJ1_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN (rr:(real^N->bool)->real^3->bool) r INTER rr r2` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s'':real^N->bool` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "bp1" THEN
    REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN DISJ1_TAC THEN
    EXISTS_TAC `s'':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_s34_fdisk tt kk (f1:real^N->real^3) car dd` THEN
    REWRITE_TAC[moi_s34_fdisk] THEN
    DISCH_THEN(MP_TAC o SPEC `s'':real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 3 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sv:real^3->bool`; `x:real^3`] MOI_S4YC_SPHERE2_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN (rr:(real^N->bool)->real^3->bool) r`;
      `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`;
      `(rr:(real^N->bool)->real^3->bool) r INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)
       SUBSET sv`] THEN
    SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`sv:real^3->bool`; `x:real^3`;
                 `(rr:(real^N->bool)->real^3->bool) r INTER
                  IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`; `bp1:real^3->bool`;
                 `(rr:(real^N->bool)->real^3->bool) r2 INTER
                  IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`; `bp2:real^3->bool`]
    MOI_S4YC_CELLS2_GLUE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    EXPAND_TAC "bp1" THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
    DISJ1_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `vv:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `(rr:(real^N->bool)->real^3->bool) r INTER
              IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) UNION
              rr r2 INTER IMAGE f1 (moi_s34_vb tt kk v)` THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4Y_SV_OPEN = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     (!r. r IN moi_s34_simp kk (&3) ==> moi_s4x_local tt kk f1 car dd r (rr r)) /\
     {v} IN kk /\ ~(v IN complex_boundary kk) /\
     x IN frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\
     x IN UNIONS {rr r INTER IMAGE f1 (moi_s34_vb tt kk v) | r |
                  r IN moi_s34_simp kk (&3) /\ v IN r} UNION
          UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g | g IN moi_s34_simp kk (&1) /\ v IN g} /\
     ~(?s g. s IN moi_s34_simp kk (&2) /\ g IN moi_s34_simp kk (&1) /\ v IN g /\
             g SUBSET s /\ x IN dd s /\ x IN IMAGE f1 (moi_s34_sd tt kk g))
     ==> ?V. open V /\ x IN V /\
             frontier (IMAGE f1 (moi_s34_vb tt kk v)) INTER V SUBSET
             UNIONS {rr r INTER IMAGE f1 (moi_s34_vb tt kk v) | r |
                     r IN moi_s34_simp kk (&3) /\ v IN r} UNION
             UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g | g IN moi_s34_simp kk (&1) /\ v IN g}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `uv = UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER
                             IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | r |
                           r IN moi_s34_simp kk (&3) /\ v IN r} UNION
                   UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                           g IN moi_s34_simp kk (&1) /\ v IN g}` THEN
  SUBGOAL_THEN
   `(!r:real^N->bool. r IN moi_s34_simp kk (&3) /\ v IN r
        ==> (rr:(real^N->bool)->real^3->bool) r INTER
            IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET uv) /\
    (!g:real^N->bool. g IN moi_s34_simp kk (&1) /\ v IN g
        ==> IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET uv)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "uv" THEN
      MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN f ==> a SUBSET UNIONS f UNION u`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN EXPAND_TAC "uv" THEN
      MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN f ==> a SUBSET u UNION UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4Y_AV_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `sv = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))` THEN
  DISCH_THEN(fun th -> ASSUME_TAC(el 4 (CONJUNCTS th)) THEN
    ASSUME_TAC(MATCH_MP (SET_RULE `(s:real^3->bool) = a UNION u ==> a SUBSET s`)
                        (el 5 (CONJUNCTS th))) THEN
    ASSUME_TAC(MATCH_MP (SET_RULE `(s:real^3->bool) = a UNION UNIONS f ==> UNIONS f SUBSET s`)
                        (el 5 (CONJUNCTS th)))) THEN
  SUBGOAL_THEN `!g:real^N->bool. g IN moi_s34_simp kk (&1) /\ v IN g
                ==> IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET sv` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                        g IN moi_s34_simp kk (&1) /\ v IN g}` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN f ==> a SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?g. g IN moi_s34_simp kk (&1) /\ v IN g /\
                     (x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `g:real^N->bool`] MOI_S4Y_SD_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC(el 1 (CONJUNCTS th))) THEN
    ASM_CASES_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                     (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THENL
     [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                    `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                    `g:real^N->bool`] MOI_S4Y_G3) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3` o GEN_REWRITE_RULE I [SUBSET]) THEN
      ASM_REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `moi_s4x_local tt kk (f1:real^N->real^3) car dd r (rr r)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                    `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`;
                    `(rr:(real^N->bool)->real^3->bool) r`; `g:real^N->bool`; `v:real^N`;
                    `x:real^3`] MOI_S4Y_RIM_SIDE_IN) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN DISCH_TAC THEN
        ASM_CASES_TAC `(g:real^N->bool) SUBSET s` THENL
         [UNDISCH_TAC `~(?s g. s IN moi_s34_simp kk (&2) /\ g IN moi_s34_simp kk (&1) /\
                               (v:real^N) IN g /\ g SUBSET s /\
                               (x:real^3) IN (dd:(real^N->bool)->real^3->bool) s /\
                               x IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))` THEN
          REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `g:real^N->bool`] THEN
          ASM_REWRITE_TAC[];
          MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                        `ep:real^N->real`; `f1:real^N->real^3`;
                        `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                        `s:real^N->bool`; `g:real^N->bool`] MOI_S4Y_FACE_DISK_RIM) THEN
          ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `vv:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `vv:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) UNION
                  (rr:(real^N->bool)->real^3->bool) r INTER IMAGE f1 (moi_s34_vb tt kk v)` THEN
      ASM_REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MP_TAC(ISPECL [`sv:real^3->bool`; `x:real^3`] MOI_S4YC_SPHERE2_CHART) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      MP_TAC(ISPECL [`sv:real^3->bool`; `x:real^3`;
                     `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`;
                     `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`]
        MOI_S4YC_CELL2_OPEN) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[IN_DIFF]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `vv:real^3->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `vv:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. r IN moi_s34_simp kk (&3) /\ (v:real^N) IN r /\
                    (x:real^3) IN (rr:(real^N->bool)->real^3->bool) r /\
                    x IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN uv` THEN EXPAND_TAC "uv" THEN
    REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
    UNDISCH_TAC `~(?g. g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\
                       (x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4x_local tt kk (f1:real^N->real^3) car dd r (rr r)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `bp = UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk v) | s |
                 s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
         UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                 g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r}` THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 ((rr:(real^N->bool)->real^3->bool) r INTER
                  IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) bp` ASSUME_TAC THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                  `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                  `r:real^N->bool`; `(rr:(real^N->bool)->real^3->bool) r`] MOI_S4Y_LOCAL_CLAUSES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 1 o CONJUNCTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "bp" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(rr:(real^N->bool)->real^3->bool) r INTER
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET sv` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`;
                  `(rr:(real^N->bool)->real^3->bool) r`] MOI_S4Y_BALL_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 12 o CONJUNCTS) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^3) IN bp` THENL
   [SUBGOAL_THEN `?s. s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s /\ s SUBSET r /\
                      (x:real^3) IN (dd:(real^N->bool)->real^3->bool) s` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN bp` THEN EXPAND_TAC "bp" THEN
      REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
      UNDISCH_TAC `~(?g. g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\
                         (x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))` THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                  `v:real^N`; `r:real^N->bool`; `s:real^N->bool`; `x:real^3`]
      MOI_S4Y_FACE_ARC_GLUE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(?g. g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\
                         (x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))` THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `vv:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `vv:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER
                          IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | r |
                        r IN moi_s34_simp kk (&3) /\ v IN r}` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "uv" THEN SET_TAC[];
    MP_TAC(ISPECL [`sv:real^3->bool`; `x:real^3`] MOI_S4YC_SPHERE2_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`sv:real^3->bool`; `x:real^3`;
                   `(rr:(real^N->bool)->real^3->bool) r INTER
                    IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`; `bp:real^3->bool`]
      MOI_S4YC_CELL2_OPEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_DIFF; IN_INTER]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `vv:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `vv:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(rr:(real^N->bool)->real^3->bool) r INTER
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* (G2), at an interior vertex v the tetra balls at v cover                  *)
(* A_v'' = f1(C_v INTER Bd N): the union of the patches and splitting disks *)
(* at v is closed and open in the sphere S_v minus the finite set of        *)
(* corners (MOI_S4Y_SV_OPEN), which is connected (MOI_S4YC_SPHERE2_DIFF_   *)
(* FINITE), and it is nonempty; so it is S_v, and the rims are covered by   *)
(* (G3).                                                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Y_FINITE_UNIONS_FAM = prove
 (`!(P:A->bool) (f:A->B->bool).
     FINITE {x | P x} /\ (!x. P x ==> FINITE (f x)) ==> FINITE (UNIONS {f x | P x})`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  ASM_SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE; IN_ELIM_THM]);;

let MOI_S4Y_G2 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car dd rr v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     (!r. r IN moi_s34_simp kk (&3) ==> moi_s4x_local tt kk f1 car dd r (rr r)) /\
     {v} IN kk /\ ~(v IN complex_boundary kk)
     ==> IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
         UNIONS {rr r | r | r IN moi_s34_simp kk (&3) /\ v IN r}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {q:real^N->bool | q IN kk /\ v IN q}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4Y_FINITE_AT THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  ABBREV_TAC `uv = UNIONS {(rr:(real^N->bool)->real^3->bool) r INTER
                             IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) | r |
                           r IN moi_s34_simp kk (&3) /\ v IN r} UNION
                   UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                           g IN moi_s34_simp kk (&1) /\ v IN g}` THEN
  ABBREV_TAC `ee = {y:real^3 | ?s g. s IN moi_s34_simp kk (&2) /\ g IN moi_s34_simp kk (&1) /\
                                    (v:real^N) IN g /\ g SUBSET s /\
                                    y IN (dd:(real^N->bool)->real^3->bool) s /\
                                    y IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)}` THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `v:real^N`] MOI_S4Y_AV_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `sv = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))` THEN
  DISCH_THEN(fun th -> ASSUME_TAC(el 4 (CONJUNCTS th)) THEN
    ASSUME_TAC(MATCH_MP (SET_RULE `(s:real^3->bool) = a UNION u ==> a SUBSET s`)
                        (el 5 (CONJUNCTS th))) THEN
    ASSUME_TAC(MATCH_MP (SET_RULE `(s:real^3->bool) = a UNION UNIONS f ==> UNIONS f SUBSET s`)
                        (el 5 (CONJUNCTS th)))) THEN
  (* uv inside sv, ee inside uv *)
  SUBGOAL_THEN `(uv:real^3->bool) SUBSET sv` ASSUME_TAC THENL
   [EXPAND_TAC "uv" THEN
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `r:real^N->bool` THEN
      STRIP_TAC THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                    `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`;
                    `(rr:(real^N->bool)->real^3->bool) r`] MOI_S4Y_BALL_FACTS) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 12 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET sv` THEN
      SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ee:real^3->bool) SUBSET uv` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ee"; "uv"] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; UNIONS_GSPEC] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (ee:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `UNIONS {UNIONS {(dd:(real^N->bool)->real^3->bool) s INTER
                                  IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | s |
                                s IN moi_s34_simp kk (&2) /\ g SUBSET s} | g |
                        g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4Y_FINITE_UNIONS_FAM THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{q:real^N->bool | q IN kk /\ v IN q}` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s34_simp] THEN MESON_TAC[];
        X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
        MATCH_MP_TAC MOI_S4Y_FINITE_UNIONS_FAM THEN CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN
          EXISTS_TAC `{q:real^N->bool | q IN kk /\ v IN q}` THEN ASM_REWRITE_TAC[] THEN
          GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM; moi_s34_simp] THEN
          ASM SET_TAC[];
          X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
          UNDISCH_TAC `moi_s34_fdisk tt kk (f1:real^N->real^3) car dd` THEN
          REWRITE_TAC[moi_s34_fdisk] THEN
          DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN(MP_TAC o SPEC `g:real^N->bool` o last o CONJUNCTS) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[FINITE_SING]]];
      EXPAND_TAC "ee" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; UNIONS_GSPEC; IN_INTER] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (uv:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "uv" THEN MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_S4Y_CLOSED_UNIONS_FAM THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{q:real^N->bool | q IN kk /\ v IN q}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s34_simp] THEN MESON_TAC[];
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN MATCH_MP_TAC COMPACT_INTER THEN
      CONJ_TAC THENL
       [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                      `ep:real^N->real`; `f1:real^N->real^3`;
                      `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                      `r:real^N->bool`; `(rr:(real^N->bool)->real^3->bool) r`]
          MOI_S4Y_BALL_FACTS) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
        MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                      `ep:real^N->real`; `f1:real^N->real^3`;
                      `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4Y_AV_FACTS) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{q:real^N->bool | q IN kk /\ v IN q}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s34_simp] THEN MESON_TAC[];
      X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                    `g:real^N->bool`] MOI_S4Y_SD_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected ((sv:real^3->bool) DIFF ee)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4YC_SPHERE2_DIFF_FINITE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean ((sv:real^3->bool) DIFF ee))
                        ((sv DIFF ee) INTER uv)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_DIFF] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                  `v:real^N`; `y:real^3`] MOI_S4Y_SV_OPEN) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `~((y:real^3) IN ee)` THEN EXPAND_TAC "ee" THEN REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `vv:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `((sv:real^3->bool) DIFF ee) INTER vv` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; IN_INTER; IN_DIFF] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean ((sv:real^3->bool) DIFF ee))
                          ((sv DIFF ee) INTER uv)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(((sv:real^3->bool) DIFF ee) INTER uv = {})` ASSUME_TAC THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`]
      MOI_S4Y_VERTEX_TETRA) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_s4x_local tt kk (f1:real^N->real^3) car dd r (rr r)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(rr:(real^N->bool)->real^3->bool) r INTER
                  IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET uv` ASSUME_TAC THENL
     [EXPAND_TAC "uv" THEN
      MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN f ==> a SUBSET UNIONS f UNION u`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `f1:real^N->real^3`;
                  `car:(real^N->bool)->real^3->bool`; `dd:(real^N->bool)->real^3->bool`;
                  `r:real^N->bool`; `(rr:(real^N->bool)->real^3->bool) r`] MOI_S4Y_LOCAL_CLAUSES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 1 o CONJUNCTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o el 3 o CONJUNCTS o MATCH_MP MOI_S4L_PL_CELL2_TOPO) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER; IN_DIFF] THEN
    MATCH_MP_TAC(TAUT `(c /\ (c ==> a)) /\ ~b ==> (a /\ ~b) /\ c`) THEN CONJ_TAC THENL
     [CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(y:real^3) IN (rr:(real^N->bool)->real^3->bool) r`;
          `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`;
          `(rr:(real^N->bool)->real^3->bool) r INTER
           IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) SUBSET uv`] THEN SET_TAC[];
        UNDISCH_TAC `(uv:real^3->bool) SUBSET sv` THEN SET_TAC[]];
      ALL_TAC] THEN
    EXPAND_TAC "ee" THEN REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `g:real^N->bool`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`;
                  `(rr:(real^N->bool)->real^3->bool) r`; `v:real^N`; `g:real^N->bool`]
      MOI_S4Y_PATCH_RIM_IN_BD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3` o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(sv:real^3->bool) DIFF ee` CONNECTED_CLOPEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `((sv:real^3->bool) DIFF ee) INTER uv`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(sv:real^3->bool) SUBSET uv` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`((sv:real^3->bool) DIFF ee) INTER uv = sv DIFF ee`;
                           `(ee:real^3->bool) SUBSET uv`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN uv` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "uv" THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                `g:real^N->bool`] MOI_S4Y_G3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3` o GEN_REWRITE_RULE I [SUBSET]) THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `g:real^N->bool`] MOI_S4Y_SD_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN REWRITE_TAC[IN_INTER] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `v:real^N`] MOI_S4Y_AV_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem RESID_B : |- MOI_S4Y_RESID_B.  The per-ball               *)
(* clauses of moi_s34_resid are moi_s4x_local; the global clauses are       *)
(* MOI_S4Y_G1, MOI_S4Y_G2 and MOI_S4Y_G3.  (The Schoenflies antecedent is   *)
(* not used.)                                                                *)
(* ------------------------------------------------------------------------- *)

let RESID_B = prove
 (MOI_S4Y_RESID_B,
  DISCH_THEN(K ALL_TAC) THEN
  MAP_EVERY X_GEN_TAC
   [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
    `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
    `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`] THEN
  STRIP_TAC THEN REWRITE_TAC[moi_s34_resid] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_s4x_local tt kk (f1:real^N->real^3) car dd r (rr r)` MP_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[moi_s4x_local]];
    MAP_EVERY X_GEN_TAC [`r:real^N->bool`; `r':real^N->bool`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `r:real^N->bool`;
                  `(rr:(real^N->bool)->real^3->bool) r`; `r':real^N->bool`;
                  `(rr:(real^N->bool)->real^3->bool) r'`] MOI_S4Y_G1) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; REWRITE_TAC[]];
    X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                  `v:real^N`] MOI_S4Y_G2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                  `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                  `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`;
                  `g:real^N->bool`] MOI_S4Y_G3) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]]);;

print_string ("RESIDB_TARGET " ^
   string_of_bool ((aconv (concl RESID_B) MOI_S4Y_RESID_B && frees (concl RESID_B) = [] && hyp RESID_B = [])) ^
   "\n");;


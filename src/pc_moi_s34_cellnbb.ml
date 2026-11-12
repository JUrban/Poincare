
(* ========================================================================= *)
(* pc_moi_s34_cellnbb: Moise GTM 47, Sec 34, Lemma 3 (printed p.240), the   *)
(* general-position part.  A PL 3-ball c0 inside the open set w0 around the *)
(* compact set k is moved by one small generic translation; then its        *)
(* frontier crosses F = f1(Bd N) at every trace point, the trace crosses    *)
(* every rim inside F, the trace has finitely many components and the       *)
(* frontier meets the rims in finitely many points.  Main theorem           *)
(* GP_BALL : |- MOI_S4Z_GP_BALL (the statement term below).                 *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_s34_frame.ml";;
needs "src/pc_moi_s34_l910.ml";;
needs "src/pc_moi_fnd_gpb.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_loop_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_S4Z_GP_BALL =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real) (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool)
   (c0:real^3->bool) (k:real^3->bool) (w0:real^3->bool).
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\
     FINITE {v | {v} IN kk /\ ~(IMAGE f1 (moi_s34_vb tt kk v) INTER w0 = {})} /\
     pl_ball 3 c0 /\ compact k /\ k SUBSET interior c0 /\ open w0 /\ c0 SUBSET w0
     ==> ?c. pl_ball 3 c /\ k SUBSET interior c /\ c SUBSET w0 /\
             (!x. x IN moi_s34_trace tt kk f1 c
                  ==> pl_crossing_at (frontier c) (IMAGE f1 (moi_s34_bd tt kk)) x) /\
             (!g x. g IN moi_s34_simp kk (&1) /\
                    x IN frontier c INTER
                         IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
                    ==> pl_curve_crossing_at (IMAGE f1 (moi_s34_bd tt kk))
                          (moi_s34_trace tt kk f1 c)
                          (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) x) /\
             FINITE (components (moi_s34_trace tt kk f1 c)) /\
             FINITE (frontier c INTER moi_s34_rims tt kk f1)`;;


(* ------------------------------------------------------------------------- *)
(* Part 1: triangulations.  A PL 3-ball in real^3 is a PL 3-cell with        *)
(* boundary its frontier and a compact polyhedron; the frontier of a PL     *)
(* 3-ball with finitely many subpolyhedra is the polyhedron of a finite     *)
(* combinatorial 2-manifold in which each subpolyhedron is a union of       *)
(* simplices (a simplicial refinement of polytope families, then the        *)
(* boundary complex: PL_BALL_TRIANGULATION_BOUNDARY,                        *)
(* BOUNDARY_COMPLEX_SURFACE).                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Z_PL_BALL_CELL = prove
 (`!B:real^3->bool.
     pl_ball 3 B ==> pl_cell_with_boundary 3 B (frontier B) /\ pl_polyhedron B`,
  GEN_TAC THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCD_BALL_FRONTIER THEN
    EXISTS_TAC `g:real^3->real^3` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4K_CELL_POLY THEN
    MAP_EVERY EXISTS_TAC [`3`; `IMAGE (f:real^3->real^3) (relative_frontier k)`] THEN
    REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4Z_BALL_TRI = prove
 (`!(B:real^3->bool) Y.
     pl_ball 3 B /\ FINITE Y /\
     (!y. y IN Y ==> pl_polyhedron y /\ y SUBSET frontier B)
     ==> ?s. FINITE s /\ combinatorial_manifold 2 s /\ UNIONS s = frontier B /\
             (!y. y IN Y ==> UNIONS {a | a IN s /\ a SUBSET y} = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Y"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4Z_PL_BALL_CELL) THEN
  SUBGOAL_THEN `frontier B SUBSET (B:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* one polytope family for B refining polytope families of the members of Y *)
  SUBGOAL_THEN
   `?P:(real^3->bool)->bool.
      FINITE P /\ (!k. k IN P ==> polytope k) /\ UNIONS P = B /\
      !y. y IN Y ==> ?Qy. Qy SUBSET P /\ UNIONS Qy = y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_polyhedron (B:real^3->bool)` THEN REWRITE_TAC[pl_polyhedron] THEN
    DISCH_THEN(X_CHOOSE_THEN `PB:(real^3->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
    SUBGOAL_THEN
     `?Q:(real^3->bool)->(real^3->bool)->bool.
        !y. y IN Y ==> FINITE (Q y) /\ (!k. k IN Q y ==> polytope k) /\ UNIONS (Q y) = y`
    (X_CHOOSE_THEN `Q:(real^3->bool)->(real^3->bool)->bool` (LABEL_TAC "Q")) THENL
     [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
      X_GEN_TAC `y:real^3->bool` THEN DISCH_TAC THEN
      USE_THEN "Y" (fun th -> MP_TAC(MP (SPEC `y:real^3->bool` th)
        (ASSUME `(y:real^3->bool) IN Y`))) THEN
      REWRITE_TAC[pl_polyhedron] THEN MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `PB UNION UNIONS (IMAGE (Q:(real^3->bool)->(real^3->bool)->bool) Y)` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FINITE_UNION] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE];
      REWRITE_TAC[IN_UNION; IN_UNIONS; EXISTS_IN_IMAGE] THEN X_GEN_TAC `k:real^3->bool` THEN
      STRIP_TAC THENL
       [ASM_SIMP_TAC[];
        USE_THEN "Q" (MP_TAC o SPEC `x:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[]];
      REWRITE_TAC[UNIONS_UNION] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET b ==> b UNION s = (b:real^3->bool)`) THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN
      DISCH_THEN(X_CHOOSE_THEN `kq:real^3->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `y:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      SUBGOAL_THEN `(z:real^3) IN y` MP_TAC THENL
       [USE_THEN "Q" (fun th -> MP_TAC(MP (SPEC `y:real^3->bool` th)
          (ASSUME `(y:real^3->bool) IN Y`))) THEN
        STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
        ASM_MESON_TAC[];
        USE_THEN "Y" (fun th -> MP_TAC(MP (SPEC `y:real^3->bool` th)
          (ASSUME `(y:real^3->bool) IN Y`))) THEN
        ASM SET_TAC[]];
      X_GEN_TAC `y:real^3->bool` THEN DISCH_TAC THEN
      EXISTS_TAC `(Q:(real^3->bool)->(real^3->bool)->bool) y` THEN
      USE_THEN "Q" (fun th -> MP_TAC(MP (SPEC `y:real^3->bool` th)
        (ASSUME `(y:real^3->bool) IN Y`))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `P:(real^3->bool)->bool` POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ref")))) THEN
  SUBGOAL_THEN `FINITE (t:(real^3->bool)->bool) /\ lf_simplicial_complex t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_complex (t:(real^3->bool)->bool)` THEN
      SIMP_TAC[simplicial_complex];
      ASM_SIMP_TAC[MOI_FMB_SC_LF]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `frontier B:real^3->bool`]
                PL_BALL_TRIANGULATION_BOUNDARY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `t:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `boundary_complex (t:(real^3->bool)->bool)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[boundary_complex] THEN SET_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3->bool` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `P:(real^3->bool)->bool`)) (concl th) &&
    can (find_term ((=) `Y:(real^3->bool)->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Qy:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "Y" (fun th -> MP_TAC(MP (SPEC `y:real^3->bool` th)
    (ASSUME `(y:real^3->bool) IN Y`))) THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^3` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [MESON_TAC[SUBSET]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?kq:real^3->bool. kq IN Qy /\ z IN kq` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN y` THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `y:real^3->bool`)) THEN
    REWRITE_TAC[IN_UNIONS];
    ALL_TAC] THEN
  USE_THEN "ref" (MP_TAC o SPEC `kq:real^3->bool`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fq:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?a:real^3->bool. a IN fq /\ z IN a` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN kq` THEN FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `kq:real^3->bool`)) THEN
    REWRITE_TAC[IN_UNIONS];
    ALL_TAC] THEN
  EXISTS_TAC `a:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a:real^3->bool) SUBSET kq /\ kq SUBSET y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `kq:real^3->bool`)) THEN ASM SET_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rand(concl th) = `y:real^3->bool`)) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ASM SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Part 2: small lemmas.  Finitely many edges of kk at a vertex;            *)
(* simplices in affine general position whose dimensions add up to at most  *)
(* 3 meet in a finite set; the generic translate of a PL ball is a PL ball, *)
(* with the translated frontier and interior; uniform translation margins   *)
(* of compact sets in open sets.                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Z_EDGES_FINITE = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk
     ==> FINITE {g | g IN moi_s34_simp kk (&1) /\ v IN g}`,
  REWRITE_TAC[moi_s34_tube; simplicial_subcomplex] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN UNIONS tt` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `lf_simplicial_complex (tt:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{s:real^N->bool | s IN tt /\ ~(s INTER u = {})}` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s34_simp] THEN
  X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ASM SET_TAC[]]);;

let MOI_S4Z_GP_FINITE = prove
 (`!S1 S2:real^3->bool.
     affine_gp_3 S1 S2 /\ aff_dim S1 + aff_dim S2 <= &3 ==> FINITE (S1 INTER S2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[affine_gp_3; DISJOINT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC) THENL
   [ASM_REWRITE_TAC[FINITE_EMPTY]; ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `aff_dim (S1:real^3->bool) + aff_dim (S2:real^3->bool) - &3 = &0`
  SUBST1_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_TAC `a:real^3`) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{a:real^3}` THEN
  REWRITE_TAC[FINITE_SING] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `S1:real^3->bool`] HULL_SUBSET) THEN
  MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `S2:real^3->bool`] HULL_SUBSET) THEN
  SET_TAC[]);;

let MOI_S4Z_TRANSLATE_PL_BALL = prove
 (`!(c0:real^3->bool) d. pl_ball 3 c0 ==> pl_ball 3 (IMAGE (\x. d + x) c0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4Z_PL_BALL_CELL) THEN
  UNDISCH_TAC `pl_ball 3 (c0:real^3->bool)` THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(\x:real^3. d + x) = (\z. z - --d)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[pl_ball] THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `(\z:real^3. z - --d) o (f:real^3->real^3)`;
                        `(g:real^3->real^3) o (\z:real^3. z + --d)`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `c0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FGB_PLH_UNIV_RESTRICT THEN
  ASM_SIMP_TAC[MOI_FGB_TRANSLATE_PLH; LOCALLY_POLYHEDRAL_PL_POLYHEDRON]);;

let MOI_S4Z_MARGIN = prove
 (`!(k:real^3->bool) u.
     compact k /\ open u /\ k SUBSET u
     ==> ?e. &0 < e /\ !d. norm d < e ==> IMAGE (\x. d + x) k SUBSET u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `(:real^3) DIFF u`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `d:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `d + x:real^3`]) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; dist] THEN
  REWRITE_TAC[VECTOR_ARITH `x - (d + x):real^3 = --d`; NORM_NEG] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Part 3: the vertex-ball spheres.  moi_s4z_vtri tt kk f1 v t: t is a       *)
(* finite combinatorial 2-manifold triangulating Sigma_v = frontier f1(C_v) *)
(* in which every splitting disk f1(D_g) at v is a union of simplices.  It   *)
(* exists (MOI_S4Z_BALL_TRI); every simplex of t lies in A_v or in a disk   *)
(* at v (MOI_S4Z_CLASS).  Local tools: a PL 2-cell has points off its        *)
(* boundary near every boundary point; near a point x only the members of a *)
(* finite closed family containing x matter; the simplices of a closed      *)
(* triangulated surface through a point of the relative interior of an edge *)
(* or of a triangle.                                                         *)
(* ------------------------------------------------------------------------- *)

let moi_s4z_vtri = new_definition
 `moi_s4z_vtri (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
               (f1:real^N->real^3) (v:real^N) (t:(real^3->bool)->bool) <=>
    FINITE t /\ combinatorial_manifold 2 t /\
    UNIONS t = frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\
    (!g. g IN moi_s34_simp kk (&1) /\ v IN g
         ==> UNIONS {a | a IN t /\ a SUBSET IMAGE f1 (moi_s34_sd tt kk g)} =
             IMAGE f1 (moi_s34_sd tt kk g))`;;

let MOI_S4Z_FRAME_DISK = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car g.
     moi_s34_frame tt kk h ep f1 car /\ g IN moi_s34_simp kk (&1)
     ==> pl_cell_with_boundary 2 (IMAGE f1 (moi_s34_sd tt kk g))
           (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk))`,
  REWRITE_TAC[moi_s34_frame] THEN MESON_TAC[]);;

let MOI_S4Z_VTRI_EXISTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk
     ==> ?t. moi_s4z_vtri tt kk f1 v t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`] MOI_S4L_AV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`;
                 `IMAGE (\g. IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g))
                        {g | g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g}`]
                MOI_S4Z_BALL_TRI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC MOI_S4Z_EDGES_FINITE THEN
      EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `g:real^N->bool` THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4K_CELL_POLY THEN
      MAP_EVERY EXISTS_TAC
       [`2`; `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`] THEN
      MATCH_MP_TAC MOI_S4Z_FRAME_DISK THEN
      MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                            `car:(real^N->bool)->real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[moi_s4z_vtri] THEN
  X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `t:(real^3->bool)->bool`)) (concl th))) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `g:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4Z_CELL_DENSE = prove
 (`!(E:real^3->bool) R x e.
     pl_cell_with_boundary 2 E R /\ x IN R /\ &0 < e
     ==> ?y. y IN E /\ ~(y IN R) /\ dist(x,y) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `homeomorphism (k,E) (f:real^3->real^3,g)` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^3) IN R` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `convex (k:real^3->bool) /\ closed k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^3) IN k` ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:real^3) IN relative_frontier k` THEN
    ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; IN_DIFF];
    ALL_TAC] THEN
  UNDISCH_TAC `(f:real^3->real^3) continuous_on k` THEN
  REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `x0:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `de:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?z:real^3. z IN relative_interior k /\ dist(z,x0) < de` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x0:real^3) IN closure(relative_interior k)` MP_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `de:real`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `(f:real^3->real^3) z` THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z1:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z1:real^3) IN k` ASSUME_TAC THENL
     [UNDISCH_TAC `(z1:real^3) IN relative_frontier k` THEN
      ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; IN_DIFF];
      ALL_TAC] THEN
    SUBGOAL_THEN `z:real^3 = z1` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(z1:real^3) IN relative_frontier k` THEN
    ASM_REWRITE_TAC[relative_frontier; IN_DIFF];
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[]]);;

let MOI_S4Z_NEAR = prove
 (`!(c:(real^N->bool)->bool) x.
     FINITE c /\ (!s. s IN c ==> closed s)
     ==> ?r. &0 < r /\ !s z. s IN c /\ z IN s /\ dist(x,z) < r ==> x IN s`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = UNIONS {s:real^N->bool | s IN c /\ ~(x IN s)}` THEN
  SUBGOAL_THEN `closed (D:real^N->bool) /\ ~((x:real^N) IN D)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:real^N) DIFF D` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[GSYM closed] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `z:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN D` MP_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `ball(x:real^N,r) SUBSET (:real^N) DIFF D` THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN ASM_MESON_TAC[]);;

let MOI_S4Z_EDGE_STAR = prove
 (`!c (e:real^3->bool) x p q a1 a2 sg.
     combinatorial_manifold 2 c /\ e IN c /\ aff_dim e = &1 /\ x IN relative_interior e /\
     (!tr. tr IN c /\ aff_dim tr = &2 /\ e SUBSET tr
           ==> tr = convex hull {p,q,a1} \/ tr = convex hull {p,q,a2}) /\
     sg IN c /\ x IN sg
     ==> sg = e \/ sg = convex hull {p,q,a1} \/ sg = convex hull {p,q,a2}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->bool) SUBSET sg` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `x:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(sg:real^3->bool) = &1 \/ aff_dim sg = &2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e:real^3->bool`; `sg:real^3->bool`] AFF_DIM_SUBSET) THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `sg:real^3->bool`] MOI_FGB_CM2_DIM) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    DISJ1_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_S4Z_TRI_STAR = prove
 (`!c (A:real^3->bool) x sg.
     combinatorial_manifold 2 c /\ A IN c /\ aff_dim A = &2 /\ x IN relative_interior A /\
     sg IN c /\ x IN sg
     ==> sg = A`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^3->bool) SUBSET sg` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `x:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
  EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`A:real^3->bool`; `sg:real^3->bool`] AFF_DIM_SUBSET) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `sg:real^3->bool`] MOI_FGB_CM2_DIM) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

(* Every simplex of a vertex-sphere triangulation lies in A_v or in a disk. *)

let MOI_S4Z_CLASS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v t sg.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     moi_s4z_vtri tt kk f1 v t /\ sg IN t
     ==> sg SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) \/
         ?g. g IN moi_s34_simp kk (&1) /\ v IN g /\
             sg SUBSET IMAGE f1 (moi_s34_sd tt kk g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4z_vtri] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`] MOI_S4L_AV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (sg:real^3->bool) /\ closed sg` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (t:(real^3->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `sg:real^3->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?y g. y IN relative_interior sg /\ g IN moi_s34_simp kk (&1) /\ (v:real^N) IN g /\
          y IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^3` (X_CHOOSE_THEN `g:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    DISJ2_TAC THEN EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:real^N->bool` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `t:(real^3->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `a:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `y:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISJ1_TAC THEN
  SUBGOAL_THEN `relative_interior sg SUBSET
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`
    MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `UNIONS (t:(real^3->bool)->bool)`)) THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `sg:real^3->bool` THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(relative_interior sg):real^3->bool` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED; SUBSET_REFL];
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]);;


(* ------------------------------------------------------------------------- *)
(* Part 4: rims in a vertex-sphere triangulation t of Sigma_v.  Near a      *)
(* rim point no triangle of t has the point in its relative interior; A_v  *)
(* is a union of simplices of t; at a rim point x in the relative interior  *)
(* of an edge e of t, of the two triangles at e one lies in A_v and the     *)
(* other in the disk, and near x A_v is that triangle and the rim is e.    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Z_LOCAL_UNION = prove
 (`!c (Z:real^N->bool) x r.
     Z = UNIONS {a | a IN c /\ a SUBSET Z} /\
     (!s z. s IN c /\ z IN s /\ dist(x,z) < r ==> x IN s)
     ==> !z. dist(x,z) < r
             ==> (z IN Z <=> ?a. a IN c /\ x IN a /\ a SUBSET Z /\ z IN a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[SUBSET]] THEN DISCH_TAC THEN
  UNDISCH_TAC `(z:real^N) IN Z` THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* The rim data of an edge [v,w] seen from v (MOI_S4L_EDGE_SD, MOI_S4L_SIGMA). *)

let MOI_S4Z_RIM_DATA = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v w.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     ~(w = v) /\ segment[v,w] IN kk
     ==> segment[v,w] IN moi_s34_simp kk (&1) /\ v IN segment[v,w] /\ {w} IN kk /\
         moi_s34_sd tt kk (segment[v,w]) = moi_s34_vb tt kk v INTER moi_s34_vb tt kk w /\
         pl_cell_with_boundary 2
           (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w))
           (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)) /\
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) INTER
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) =
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) /\
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) SUBSET
         frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
         frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) SUBSET
         IMAGE f1 (moi_s34_vb tt kk w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `v:real^N`; `w:real^N`] MOI_S4L_EDGE_SD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`] MOI_S4L_SIGMA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `pl_cell_with_boundary:num->(real^3->bool)->(real^3->bool)->bool`))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN DISJ2_TAC THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]);;

(* A rim point is never in the relative interior of a triangle of t. *)

let MOI_S4Z_RIM_NOT_TRI = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v w t x sg.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     ~(w = v) /\ segment[v,w] IN kk /\ moi_s4z_vtri tt kk f1 v t /\
     x IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) /\
     sg IN t /\ x IN relative_interior sg
     ==> ~(aff_dim sg = &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`] MOI_S4Z_RIM_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4z_vtri]) THEN
  SUBGOAL_THEN `!s. s IN t ==> closed (s:real^3->bool)` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    UNDISCH_TAC `combinatorial_manifold 2 (t:(real^3->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold; lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^3->bool` o CONJUNCT1 o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `x:real^3`] MOI_S4Z_NEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!z. z IN frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) /\
                    dist(x,z) < r0 ==> z IN sg`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `(z:real^3) IN frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS (t:(real^3->bool)->bool)`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `s:real^3->bool = sg` (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC MOI_S4Z_TRI_STAR THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `x:real^3`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `t:(real^3->bool)->bool`; `sg:real^3->bool`] MOI_S4Z_CLASS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MP_TAC(ISPECL
     [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                                  moi_s34_bd tt kk)`;
      `x:real^3`; `r0:real`] MOI_S4Z_CELL_DENSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN sg` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~((y:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk))` THEN
    SUBGOAL_THEN
     `IMAGE (f1:real^N->real^3)
        (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) =
      IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) INTER
      IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `g = segment[v:real^N,w]` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`]
                  MOI_S4L_IMG_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`g:real^N->bool`; `segment[v:real^N,w]`] o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p ==> (~q ==> p) ==> q`) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^3` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`; `x:real^3`; `r0:real`] MOI_S4L_RIM_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN sg` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~((y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(sg:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)`
  MP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)` THEN
    ASM_MESON_TAC[];
    ASM SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Part 5: A_v is the union of the simplices of t inside it, and the        *)
(* rim edge picture: at a rim point x in the relative interior of an edge e *)
(* of t, one of the two triangles at e lies in A_v, the other in the disk;  *)
(* near x, A_v is that triangle and the rim is e.                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Z_VTRI_CLOSED = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) v t.
     moi_s4z_vtri tt kk f1 v t
     ==> FINITE t /\ lf_simplicial_complex t /\ (!s. s IN t ==> closed (s:real^3->bool))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4z_vtri; combinatorial_manifold] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
  UNDISCH_TAC `lf_simplicial_complex (t:(real^3->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^3->bool` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED]);;

let MOI_S4Z_AV_UNION = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v t.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     moi_s4z_vtri tt kk f1 v t
     ==> IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) =
         UNIONS {a | a IN t /\
                     a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4Z_VTRI_CLOSED) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4z_vtri]) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`] MOI_S4L_AV_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[SUBSET]] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN UNIONS t` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `s0:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `t:(real^3->bool)->bool`; `s0:real^3->bool`] MOI_S4Z_CLASS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2
   (fun th -> MP_TAC th THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s0:real^3->bool` o REWRITE_RULE[NOT_EXISTS_THM] o
        check (fun th -> is_neg(concl th) && is_exists(dest_neg(concl th)))) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[])
    (X_CHOOSE_THEN `g0:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?w. ~(w = v) /\ g0 = segment[v:real^N,w]`
  (X_CHOOSE_THEN `w:real^N` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g0:real^N->bool`]
                  MOI_S4L_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(v:real^N) IN {u1,u2}` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rand(concl th) = `{u1:real^N,u2}`)) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
     [EXISTS_TAC `u2:real^N` THEN ASM_MESON_TAC[];
      EXISTS_TAC `u1:real^N` THEN ASM_MESON_TAC[SEGMENT_SYM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,w] IN kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s34_simp; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`] MOI_S4Z_RIM_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* every simplex of t through y lies in the disk of g0 *)
  SUBGOAL_THEN `!s. s IN t /\ (y:real^3) IN s
                    ==> s SUBSET IMAGE (f1:real^N->real^3)
                                   (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `v:real^N`; `t:(real^3->bool)->bool`; `s:real^3->bool`] MOI_S4Z_CLASS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2
     (fun th -> MP_TAC th THEN
        FIRST_ASSUM(MP_TAC o SPEC `s:real^3->bool` o REWRITE_RULE[NOT_EXISTS_THM] o
          check (fun th -> is_neg(concl th) && is_exists(dest_neg(concl th)))) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[])
      (X_CHOOSE_THEN `g1:real^N->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `g1 = segment[v:real^N,w]` SUBST_ALL_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                     `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMG_FACTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`g1:real^N->bool`; `segment[v:real^N,w]`] o CONJUNCT1) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `~p ==> (~q ==> p) ==> q`) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^3` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(s:real^3->bool) SUBSET
                     IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g1)` THEN
        UNDISCH_TAC `(y:real^3) IN s` THEN SET_TAC[];
        UNDISCH_TAC `(s0:real^3->bool) SUBSET
                     IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[v,w]))` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN s0` THEN SET_TAC[]];
      UNDISCH_TAC `(s:real^3->bool) SUBSET
                   IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[v,w]))` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `y:real^3`] MOI_S4Z_NEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (f1:real^N->real^3)
        (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) =
      IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) INTER
      IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`; `y:real^3`; `r0:real`] MOI_S4L_RIM_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:real^3) IN UNIONS t` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `s1:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN s1` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~((z:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s1:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)`
  MP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)` THEN
    ASM_MESON_TAC[];
    ASM SET_TAC[]]);;

(* Assumption selector: the theorem says S SUBSET Z or ~(S SUBSET Z). *)

let moi_s4z_sub_check z th =
  let c = concl th in
  let c' = if is_neg c then dest_neg c else c in
  try snd(dest_binary "SUBSET" c') = z with Failure _ -> false;;

(* The rim edge picture. *)

let MOI_S4Z_RIM_EDGE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v w t x e.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     ~(w = v) /\ segment[v,w] IN kk /\ moi_s4z_vtri tt kk f1 v t /\
     x IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) /\
     e IN t /\ aff_dim e = &1 /\ x IN relative_interior e
     ==> ?p q a r. ~(p = q) /\ e = convex hull {p,q} /\ ~(a = p) /\ ~(a = q) /\
                   ~affine_dependent {p,q,a} /\
                   convex hull {p,q,a} SUBSET
                   IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\ &0 < r /\
                   (!z. dist(x,z) < r
                        ==> (z IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) <=>
                             z IN convex hull {p,q,a})) /\
                   (!z. dist(x,z) < r
                        ==> (z IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                                            moi_s34_bd tt kk) <=>
                             z IN convex hull {p,q}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`] MOI_S4Z_RIM_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4Z_VTRI_CLOSED) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4z_vtri]) THEN
  ABBREV_TAC `Av = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `Ed = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)` THEN
  ABBREV_TAC `Rg = IMAGE (f1:real^N->real^3)
                     (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
  SUBGOAL_THEN `Av:real^3->bool = UNIONS {a | a IN t /\ a SUBSET Av}` ASSUME_TAC THENL
   [EXPAND_TAC "Av" THEN MATCH_MP_TAC MOI_S4Z_AV_UNION THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Ed:real^3->bool = UNIONS {a | a IN t /\ a SUBSET Ed}` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `segment[v:real^N,w]` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun tm -> is_const tm && fst(dest_const tm) = "moi_s34_sd")) (concl th) &&
      can (find_term ((=) `t:(real^3->bool)->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `e:real^3->bool`] MOI_FGB_EDGE_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `q:real^3`
   (X_CHOOSE_THEN `a1:real^3` (X_CHOOSE_THEN `a2:real^3` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `e:real^3->bool`)) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `x:real^3`] MOI_S4Z_NEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  (* the simplices of t through x *)
  SUBGOAL_THEN `!a. a IN t /\ (x:real^3) IN a
                    ==> a = convex hull {p,q} \/ a = convex hull {p,q,a1} \/
                        a = convex hull {p,q,a2}`
  (LABEL_TAC "star") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4Z_EDGE_STAR THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `x:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {p:real^3,q} SUBSET convex hull {p,q,a1} /\
                convex hull {p,q} SUBSET convex hull {p,q,a2} /\
                (x:real^3) IN convex hull {p,q}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    ALL_TAC] THEN
  (* local forms of Av, Ed and of the sphere *)
  SUBGOAL_THEN
   `!Z:real^3->bool. Z = UNIONS {a | a IN (t:(real^3->bool)->bool) /\ a SUBSET Z}
        ==> !z. dist(x:real^3,z) < r0
                ==> (z IN Z <=>
                     convex hull {p,q} SUBSET Z /\ z IN convex hull {p,q} \/
                     convex hull {p,q,a1} SUBSET Z /\ z IN convex hull {p,q,a1} \/
                     convex hull {p,q,a2} SUBSET Z /\ z IN convex hull {p,q,a2})`
  (LABEL_TAC "loc") THENL
   [X_GEN_TAC `Z:real^3->bool` THEN
    DISCH_THEN(fun zth -> MP_TAC(MATCH_MP MOI_S4Z_LOCAL_UNION (CONJ zth
      (ASSUME `!s z. s IN (t:(real^3->bool)->bool) /\ z IN s /\ dist(x:real^3,z) < r0
                     ==> x IN s`)))) THEN
    DISCH_THEN(fun th -> X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      MP_TAC(SPEC `z:real^3` th)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `a:real^3->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "star" (fun th -> MP_TAC(MP (SPEC `a:real^3->bool` th)
        (CONJ (ASSUME `(a:real^3->bool) IN t`) (ASSUME `(x:real^3) IN a`)))) THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
      STRIP_TAC THENL
       [EXISTS_TAC `convex hull {p:real^3,q}` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `convex hull {p:real^3,q,a1}` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        EXISTS_TAC `convex hull {p:real^3,q,a2}` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {p:real^3,q,a1} IN t /\ convex hull {p:real^3,q,a2} IN t`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* classification of the two triangles *)
  SUBGOAL_THEN
   `!b. convex hull {p,q,b} IN t /\ convex hull {p,q} SUBSET convex hull {p,q,b}
        ==> convex hull {p,q,b} SUBSET Av \/ convex hull {p:real^3,q,b} SUBSET Ed`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `v:real^N`; `t:(real^3->bool)->bool`; `convex hull {p:real^3,q,b}`]
                  MOI_S4Z_CLASS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
    SUBGOAL_THEN `g = segment[v:real^N,w]` SUBST_ALL_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                     `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMG_FACTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`g:real^N->bool`; `segment[v:real^N,w]`] o CONJUNCT1) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `~p ==> (~q ==> p) ==> q`) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^3` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `convex hull {p:real^3,q,b} SUBSET
                     IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
        UNDISCH_TAC `convex hull {p:real^3,q} SUBSET convex hull {p,q,b}` THEN
        UNDISCH_TAC `(x:real^3) IN convex hull {p,q}` THEN SET_TAC[];
        UNDISCH_TAC `(x:real^3) IN Rg` THEN
        UNDISCH_TAC `(Ed:real^3->bool) INTER Av = Rg` THEN SET_TAC[]];
      UNDISCH_TAC `convex hull {p:real^3,q,b} SUBSET
                   IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[v,w]))` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the two impossible configurations *)
  SUBGOAL_THEN `~(convex hull {p,q,a1} SUBSET Av /\ convex hull {p:real^3,q,a2} SUBSET Av)`
  ASSUME_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`Ed:real^3->bool`; `Rg:real^3->bool`; `x:real^3`; `r0:real`]
                  MOI_S4Z_CELL_DENSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN UNIONS t` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN Ed` THEN
      UNDISCH_TAC `Ed SUBSET frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "loc" (MP_TAC o SPEC `UNIONS t:real^3->bool`) THEN
    ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((y:real^3) IN Rg)` THEN UNDISCH_TAC `(y:real^3) IN Ed` THEN
    UNDISCH_TAC `(Ed:real^3->bool) INTER Av = Rg` THEN
    UNDISCH_TAC `convex hull {p,q,a1} SUBSET (Av:real^3->bool)` THEN
    UNDISCH_TAC `convex hull {p,q,a2} SUBSET (Av:real^3->bool)` THEN
    UNDISCH_TAC `convex hull {p:real^3,q} SUBSET convex hull {p,q,a1}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(convex hull {p,q,a1} SUBSET Ed /\ convex hull {p:real^3,q,a2} SUBSET Ed)`
  ASSUME_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `v:real^N`; `w:real^N`; `x:real^3`; `r0:real`] MOI_S4L_RIM_SIDE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN UNIONS t` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN Av` THEN
      UNDISCH_TAC `Av SUBSET frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "loc" (MP_TAC o SPEC `UNIONS t:real^3->bool`) THEN
    ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))` THEN
    UNDISCH_TAC `Ed SUBSET IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)` THEN
    UNDISCH_TAC `convex hull {p,q,a1} SUBSET (Ed:real^3->bool)` THEN
    UNDISCH_TAC `convex hull {p,q,a2} SUBSET (Ed:real^3->bool)` THEN
    UNDISCH_TAC `convex hull {p:real^3,q} SUBSET convex hull {p,q,a1}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the conclusion for a triangle pair (b1 in A_v, b2 in the disk) *)
  SUBGOAL_THEN
   `!b1 b2. (b1 = a1 /\ b2 = a2 \/ b1 = a2 /\ b2 = a1) /\
            convex hull {p,q,b1} SUBSET Av /\ ~(convex hull {p,q,b1} SUBSET Ed) /\
            convex hull {p,q,b2} SUBSET Ed /\ ~(convex hull {p:real^3,q,b2} SUBSET Av)
            ==> ?a r. ~(a = p) /\ ~(a = q) /\ ~affine_dependent {p,q,a} /\
                      convex hull {p,q,a} SUBSET Av /\ &0 < r /\
                      (!z. dist(x,z) < r ==> (z IN Av <=> z IN convex hull {p,q,a})) /\
                      (!z. dist(x,z) < r ==> (z IN Rg <=> z IN convex hull {p,q}))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`b1:real^3`; `b2:real^3`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`b1:real^3`; `r0:real`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      (lhs(concl th) = `b1:real^3` || lhs(concl th) = `b2:real^3`)))) THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
       USE_THEN "loc" (MP_TAC o SPEC `Av:real^3->bool`) THEN
       ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
       DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
       UNDISCH_TAC `convex hull {p:real^3,q} SUBSET convex hull {p,q,a1}` THEN
       UNDISCH_TAC `convex hull {p:real^3,q} SUBSET convex hull {p,q,a2}` THEN
       REPEAT(FIRST_X_ASSUM(MP_TAC o check (moi_s4z_sub_check `Av:real^3->bool`))) THEN
       SET_TAC[];
       X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
       SUBGOAL_THEN `Rg:real^3->bool = Ed INTER Av` SUBST1_TAC THENL
        [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       REWRITE_TAC[IN_INTER] THEN
       USE_THEN "loc" (MP_TAC o SPEC `Av:real^3->bool`) THEN
       ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
       DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
       USE_THEN "loc" (MP_TAC o SPEC `Ed:real^3->bool`) THEN
       ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
       DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
       SUBGOAL_THEN `convex hull {p,q,a1} INTER convex hull {p:real^3,q,a2} =
                     convex hull {p,q}` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       UNDISCH_TAC `convex hull {p:real^3,q} SUBSET convex hull {p,q,a1}` THEN
       UNDISCH_TAC `convex hull {p:real^3,q} SUBSET convex hull {p,q,a2}` THEN
       REPEAT(FIRST_X_ASSUM(MP_TAC o check (moi_s4z_sub_check `Av:real^3->bool`))) THEN
       REPEAT(FIRST_X_ASSUM(MP_TAC o check (moi_s4z_sub_check `Ed:real^3->bool`))) THEN
       SET_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?a r. ~(a = p) /\ ~(a = q) /\ ~affine_dependent {p,q,a} /\
          convex hull {p,q,a} SUBSET Av /\ &0 < r /\
          (!z. dist(x,z) < r ==> (z IN Av <=> z IN convex hull {p,q,a})) /\
          (!z. dist(x,z) < r ==> (z IN Rg <=> z IN convex hull {p:real^3,q}))`
  MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `a1:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Ed:real^3->bool`)) (concl th) &&
      not (can (find_term ((=) `b1:real^3`)) (concl th)))) THEN
    FIRST_ASSUM(MP_TAC o SPEC `a2:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Ed:real^3->bool`)) (concl th) &&
      not (can (find_term ((=) `b1:real^3`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `convex hull {p:real^3,q,a1} SUBSET Av` THENL
     [MAP_EVERY EXISTS_TAC [`a1:real^3`; `a2:real^3`] THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`a2:real^3`; `a1:real^3`] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`p:real^3`; `q:real^3`; `a:real^3`; `r:real`] THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Part 6: two triangles on the two sides of a common line through x        *)
(* (from the two vertex spheres at a rim point).  Near x their union is a    *)
(* plane or a wedge of two half planes along the line (MOI_FGB_WEDGE_CASE   *)
(* after moving both triangles onto a common edge [x - e, x + e] by          *)
(* MOI_FGB_HALF_PLANE; in the coplanar case the triangles lie on opposite    *)
(* sides, since they meet only on the line near x).                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Z_ORTH = prove
 (`!e w:real^3.
     ~(e = vec 0) /\ (!l. ~(w = l % e))
     ==> ?v. v dot e = &0 /\ &0 < v dot w /\ ~(v = vec 0) /\
             ?c. w = v + c % e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~((e:real^3) dot e = &0)` ASSUME_TAC THENL [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
  ABBREV_TAC `c = ((w:real^3) dot e) / (e dot e)` THEN
  EXISTS_TAC `w - c % e:real^3` THEN
  SUBGOAL_THEN `~(w - c % e:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(w - c % e) dot (e:real^3) = &0` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[DOT_LSUB; DOT_LMUL] THEN
    UNDISCH_TAC `~(e dot e:real^3 = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(w - c % e) dot (w:real^3) = (w - c % e) dot (w - c % e)` SUBST1_TAC THENL
     [UNDISCH_TAC `(w - c % e) dot (e:real^3) = &0` THEN
      REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
      REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_RING;
      ASM_REWRITE_TAC[DOT_POS_LT]];
    EXISTS_TAC `c:real` THEN VECTOR_ARITH_TAC]);;

(* A triangle near a relative interior point of its edge equals the triangle *)
(* on any other edge through that point (same line, same apex).             *)

let MOI_S4Z_SUBEDGE = prove
 (`!(p:real^3) q a p0 q0 u.
     ~(p = q) /\ ~(a = p) /\ ~(a = q) /\ ~affine_dependent {p,q,a} /\
     &0 < u /\ u < &1 /\ ~(p0 = q0) /\
     p0 IN affine hull {p,q} /\ q0 IN affine hull {p,q} /\
     (&1 - inv(&2)) % p0 + inv(&2) % q0 = (&1 - u) % p + u % q
     ==> ~(a = p0) /\ ~(a = q0) /\ ~affine_dependent {p0,q0,a} /\
         affine hull {p0,q0,a} = affine hull {p,q,a} /\
         ?r. &0 < r /\
             !z. dist((&1 - u) % p + u % q,z) < r
                 ==> (z IN convex hull {p,q,a} <=> z IN convex hull {p0,q0,a})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `x:real^3 = (&1 - u) % p + u % q` THEN
  SUBGOAL_THEN `~((a:real^3) IN affine hull {p,q})` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FGB_OFF_LINE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `affine hull {p0:real^3,q0} SUBSET affine hull {p,q}` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_AFFINE_HULL] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((a:real^3) IN affine hull {p0,q0})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(a:real^3 = p0) /\ ~(a = q0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~((a:real^3) IN affine hull {p0,q0})` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {p0:real^3,q0,a}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p0:real^3`; `q0:real^3`; `a:real^3`] COLLINEAR_3_EQ_AFFINE_DEPENDENT) THEN
    MP_TAC(ISPECL [`p0:real^3`; `q0:real^3`; `a:real^3`] COLLINEAR_3_AFFINE_HULL) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull {p0:real^3,q0,a} = affine hull {p,q,a}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{p0:real^3,q0,a}`; `affine hull {p:real^3,q,a}`]
                  AFF_DIM_EQ_AFFINE_HULL) THEN
    REWRITE_TAC[HULL_HULL] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!x s t. (x:real^3) IN s /\ s SUBSET t ==> x IN t`) THEN
        EXISTS_TAC `affine hull {p:real^3,q}` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
        MATCH_MP_TAC(SET_RULE `!x s t. (x:real^3) IN s /\ s SUBSET t ==> x IN t`) THEN
        EXISTS_TAC `affine hull {p:real^3,q}` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
        MATCH_MP_TAC HULL_INC THEN SET_TAC[]];
      ASM_SIMP_TAC[AFF_DIM_AFFINE_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
      ASM_SIMP_TAC[MOI_FGB_CARD3; INT_LE_REFL]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the apex direction orthogonal to the line *)
  MP_TAC(ISPECL [`q - p:real^3`; `a - x:real^3`] MOI_S4Z_ORTH) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN X_GEN_TAC `l:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `~((a:real^3) IN affine hull {p,q})` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `a:real^3 = (&1 - (u + l)) % p + (u + l) % q` SUBST1_TAC THENL
     [UNDISCH_TAC `a - x:real^3 = l % (q - p)` THEN EXPAND_TAC "x" THEN VECTOR_ARITH_TAC;
      REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`&1 - (u + l)`; `u + l:real`] THEN REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
  SUBGOAL_THEN `(v:real^3) dot (q0 - p0) = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `(q0:real^3) IN affine hull {p,q}` THEN
    UNDISCH_TAC `(p0:real^3) IN affine hull {p,q}` THEN
    REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `s2:real` STRIP_ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `s3:real` (X_CHOOSE_THEN `s4:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `q0 - p0:real^3 = (s4 - s2) % (q - p)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `s1 = &1 - s2 /\ s3 = &1 - s4` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
      ASM_REWRITE_TAC[DOT_RMUL; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a:real^3`; `v:real^3`; `u:real`]
                MOI_FGB_HALF_PLANE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p0:real^3`; `q0:real^3`; `a:real^3`; `v:real^3`; `inv(&2)`]
                MOI_FGB_HALF_PLANE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r1 r2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(&1 - u) % p + u % q:real^3 = x`]) THEN
  ASM_SIMP_TAC[]);;

(* Two edges through x that agree near x lie on one line. *)

let MOI_S4Z_LINE_SAME = prove
 (`!(p:real^3) q p' q' u u' r.
     ~(p' = q') /\ &0 < u' /\ u' < &1 /\ &0 < r /\
     (&1 - u') % p' + u' % q' = (&1 - u) % p + u % q /\
     (!z. dist((&1 - u) % p + u % q,z) < r
          ==> z IN convex hull {p',q'} ==> z IN convex hull {p,q})
     ==> p' IN affine hull {p,q} /\ q' IN affine hull {p,q}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `x:real^3 = (&1 - u) % p + u % q` THEN
  SUBGOAL_THEN `(x:real^3) IN affine hull {p,q}` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`&1 - u`; `u:real`] THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(q' - p':real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  ABBREV_TAC `ep = min ((&1 - u') / &2) (r / (&2 * norm(q' - p':real^3)))` THEN
  SUBGOAL_THEN `&0 < ep /\ ep <= (&1 - u') / &2 /\ ep * norm(q' - p':real^3) < r`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ep" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(r / (&2 * norm(q' - p':real^3))) * norm(q' - p')` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
        SUBGOAL_THEN `(r / (&2 * norm(q' - p':real^3))) * norm(q' - p') = r / &2`
        SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < norm(q' - p':real^3)` THEN CONV_TAC REAL_FIELD;
          ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  ABBREV_TAC `z:real^3 = x + ep % (q' - p')` THEN
  SUBGOAL_THEN `(z:real^3) IN affine hull {p,q}` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!y s t. (y:real^3) IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `convex hull {p:real^3,q}` THEN REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (is_forall o concl)) THEN
    CONJ_TAC THENL
     [EXPAND_TAC "z" THEN REWRITE_TAC[dist; VECTOR_ARITH `x - (x + y):real^3 = --y`] THEN
      ASM_REWRITE_TAC[NORM_NEG; NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`];
      REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; IN_SEGMENT] THEN
      EXISTS_TAC `u' + ep:real` THEN
      REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "z" THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rand(concl th) = `x:real^3` &&
        can (find_term ((=) `p':real^3`)) (lhs(concl th)))) THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN convex hull {p',q'} /\ (z:real^3) IN convex hull {p',q'} /\
                ~(x = z)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; IN_SEGMENT] THEN EXISTS_TAC `u':real` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; IN_SEGMENT] THEN
      EXISTS_TAC `u' + ep:real` THEN
      REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "z" THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rand(concl th) = `x:real^3` &&
        can (find_term ((=) `p':real^3`)) (lhs(concl th)))) THEN
      VECTOR_ARITH_TAC;
      EXPAND_TAC "z" THEN REWRITE_TAC[VECTOR_ARITH `x = x + y <=> y = vec 0:real^3`] THEN
      ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull {x:real^3,z} = affine hull {p',q'}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{x:real^3,z}`; `affine hull {p':real^3,q'}`] AFF_DIM_EQ_AFFINE_HULL) THEN
    REWRITE_TAC[HULL_HULL] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`{p':real^3,q'}`] CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
      UNDISCH_TAC `(x:real^3) IN convex hull {p',q'}` THEN
      UNDISCH_TAC `(z:real^3) IN convex hull {p',q'}` THEN SET_TAC[];
      ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL; AFF_DIM_2; INT_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull {x:real^3,z} SUBSET affine hull {p,q}` MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_AFFINE_HULL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `{p':real^3,q'}`] HULL_SUBSET) THEN
  SET_TAC[]);;

(* The coplanar case: two triangles on a common edge in one plane that meet *)
(* near x only on the line lie on opposite sides; near x their union is the *)
(* plane.                                                                    *)

let MOI_S4Z_FLAT_CASE = prove
 (`!(p0:real^3) q0 a a' n v x c r.
     ~(p0 = q0) /\ ~(a = p0) /\ ~(a = q0) /\ ~affine_dependent {p0,q0,a} /\
     ~(a' = p0) /\ ~(a' = q0) /\ ~affine_dependent {p0,q0,a'} /\
     (&1 - inv(&2)) % p0 + inv(&2) % q0 = x /\
     a' IN affine hull {p0,q0,a} /\
     (!z. z IN affine hull {p0,q0,a} <=> n dot (z - x) = &0) /\
     v dot (q0 - p0) = &0 /\ ~(v = vec 0) /\ a - x = v + c % (q0 - p0) /\
     &0 < r /\
     (!z. dist(x,z) < r /\ z IN convex hull {p0,q0,a} /\ z IN convex hull {p0,q0,a'}
          ==> v dot (z - x) = &0)
     ==> ?r1. &0 < r1 /\
              !z. dist(x,z) < r1
                  ==> (z IN convex hull {p0,q0,a} \/ z IN convex hull {p0,q0,a'} <=>
                       n dot (z - x) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < v dot (v:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(n:real^3) dot (q0 - p0) = &0 /\ n dot (a - x) = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `(n:real^3) dot (q0 - x) = &0 /\ n dot (p0 - x) = &0` MP_TAC THENL
       [CONJ_TAC THEN FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o
          check (fun th -> is_forall(concl th) && can (find_term ((=) `n:real^3`)) (concl th))) THEN
        MATCH_MP_TAC HULL_INC THEN SET_TAC[];
        REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC];
      FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `n:real^3`)) (concl th))) THEN
      MATCH_MP_TAC HULL_INC THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(n:real^3) dot v = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `v:real^3 = (a - x) - c % (q0 - p0)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      ASM_REWRITE_TAC[DOT_RSUB; DOT_RMUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the coordinate of a' across the line *)
  UNDISCH_TAC `(a':real^3) IN affine hull {p0,q0,a}` THEN
  REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:real` (X_CHOOSE_THEN `l1:real` (X_CHOOSE_THEN `l2:real`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `v dot (a' - x:real^3) = l2 * (v dot v)` ASSUME_TAC THENL
   [SUBGOAL_THEN `a' - x:real^3 = ((l1 - l0) * inv(&2) + l2 * c) % (q0 - p0) + l2 % v`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `a:real^3 = x + v + c % (q0 - p0)` SUBST1_TAC THENL
       [UNDISCH_TAC `a - x:real^3 = v + c % (q0 - p0)` THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rand(concl th) = `x:real^3`)) THEN
      SUBGOAL_THEN `l0 = &1 - l1 - l2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      VECTOR_ARITH_TAC;
      ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(l2 = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`p0:real^3`; `q0:real^3`; `a':real^3`] MOI_FGB_OFF_LINE) THEN
    ASM_REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`l0:real`; `l1:real`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull {p0,q0,a'} = affine hull {p0:real^3,q0,a}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FGB_SAME_PLANE THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`l0:real`; `l1:real`; `l2:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `a':real^3`)) THEN
  (* the half-plane forms near x *)
  MP_TAC(ISPECL [`p0:real^3`; `q0:real^3`; `a:real^3`; `v:real^3`; `inv(&2)`]
                MOI_FGB_HALF_PLANE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    UNDISCH_TAC `a - x:real^3 = v + c % (q0 - p0)` THEN
    DISCH_THEN(SUBST1_TAC) THEN ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `&0 < l2` THENL
   [(* same side: a common point off the line, impossible *)
    MP_TAC(ISPECL [`p0:real^3`; `q0:real^3`; `a':real^3`; `v:real^3`; `inv(&2)`]
                  MOI_FGB_HALF_PLANE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r3:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `ep = min r (min r2 r3) / (&2 * norm(v:real^3))` THEN
    SUBGOAL_THEN `&0 < norm(v:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < ep /\ ep * norm(v:real^3) < min r (min r2 r3)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "ep" THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `min r (min r2 r3) / (&2 * norm(v:real^3)) * norm v =
                      min r (min r2 r3) / &2` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < norm(v:real^3)` THEN CONV_TAC REAL_FIELD;
          ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `dist(x:real^3,x + ep % v) < min r (min r2 r3)` MP_TAC THENL
     [REWRITE_TAC[dist; VECTOR_ARITH `x - (x + y):real^3 = --y`; NORM_NEG; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x + ep % v:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `v:real^3`)) (concl th) &&
      can (find_term ((=) `r:real`)) (concl th))) THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `(x + y) - x:real^3 = y`; DOT_RMUL] THEN
    ASM_SIMP_TAC[REAL_ENTIRE; REAL_LT_IMP_NZ; REAL_LE_MUL; REAL_LT_IMP_LE] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  (* opposite sides *)
  MP_TAC(ISPECL [`p0:real^3`; `q0:real^3`; `a':real^3`; `--v:real^3`; `inv(&2)`]
                MOI_FGB_HALF_PLANE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DOT_LNEG; REAL_NEG_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ARITH `&0 < --x <=> x < &0`] THEN
    REWRITE_TAC[REAL_ARITH `l * d < &0 <=> &0 < (--l) * d`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r3:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r2 r3:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[DOT_LNEG] THEN REAL_ARITH_TAC);;

(* The union of the two triangles near x: a plane or a wedge along the line. *)

let MOI_S4Z_TWO_HALF = prove
 (`!(p:real^3) q a p' q' a' u u' r.
     ~(p = q) /\ ~(a = p) /\ ~(a = q) /\ ~affine_dependent {p,q,a} /\
     ~(p' = q') /\ ~(a' = p') /\ ~(a' = q') /\ ~affine_dependent {p',q',a'} /\
     &0 < u /\ u < &1 /\ &0 < u' /\ u' < &1 /\
     (&1 - u') % p' + u' % q' = (&1 - u) % p + u % q /\ &0 < r /\
     (!z. dist((&1 - u) % p + u % q,z) < r
          ==> z IN convex hull {p',q'} ==> z IN convex hull {p,q}) /\
     (!z. dist((&1 - u) % p + u % q,z) < r /\
          z IN convex hull {p,q,a} /\ z IN convex hull {p',q',a'}
          ==> z IN affine hull {p,q})
     ==> ?r1. &0 < r1 /\
           ((?n k. ~(n = vec 0) /\ n dot (q - p) = &0 /\
                   ~(k = vec 0) /\ k dot (q - p) = &0 /\ n dot k = &0 /\
                 !z. dist((&1 - u) % p + u % q,z) < r1
                     ==> (z IN convex hull {p,q,a} \/ z IN convex hull {p',q',a'} <=>
                          n dot (z - ((&1 - u) % p + u % q)) = &0)) \/
            (?n1 n2. n1 dot (q - p) = &0 /\ n2 dot (q - p) = &0 /\
                     (!s1 s2. s1 % n1 + s2 % n2 = vec 0 ==> s1 = &0 /\ s2 = &0) /\
                     !z. dist((&1 - u) % p + u % q,z) < r1
                         ==> (z IN convex hull {p,q,a} \/ z IN convex hull {p',q',a'} <=>
                              n1 dot (z - ((&1 - u) % p + u % q)) = &0 /\
                              &0 <= n2 dot (z - ((&1 - u) % p + u % q)) \/
                              n2 dot (z - ((&1 - u) % p + u % q)) = &0 /\
                              &0 <= n1 dot (z - ((&1 - u) % p + u % q)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `p':real^3`; `q':real^3`; `u:real`; `u':real`;
                 `r:real`] MOI_S4Z_LINE_SAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `x:real^3 = (&1 - u) % p + u % q` THEN
  ABBREV_TAC `e:real^3 = q - p` THEN
  SUBGOAL_THEN `~(e:real^3 = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REWRITE_TAC[VECTOR_SUB_EQ]; ALL_TAC] THEN
  (* the common edge [x - e, x + e] *)
  SUBGOAL_THEN `(x - e:real^3) IN affine hull {p,q} /\ (x + e:real^3) IN affine hull {p,q} /\
                ~(x - e:real^3 = x + e) /\
                (&1 - inv(&2)) % (x - e) + inv(&2) % (x + e:real^3) = x`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "e"] THEN REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`&2 - u`; `u - &1`] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; VECTOR_ARITH_TAC];
      MAP_EVERY EXISTS_TAC [`--u`; `&1 + u`] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; VECTOR_ARITH_TAC];
      REWRITE_TAC[VECTOR_ARITH `x - e = x + e <=> e = vec 0:real^3`] THEN
      ASM_REWRITE_TAC[VECTOR_SUB_EQ];
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull {p':real^3,q'} = affine hull {p,q}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{p':real^3,q'}`; `affine hull {p:real^3,q}`] AFF_DIM_EQ_AFFINE_HULL) THEN
    REWRITE_TAC[HULL_HULL] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL; AFF_DIM_2; INT_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a:real^3`; `x - e:real^3`; `x + e:real^3`; `u:real`]
                MOI_S4Z_SUBEDGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`p':real^3`; `q':real^3`; `a':real^3`; `x - e:real^3`; `x + e:real^3`;
                 `u':real`] MOI_S4Z_SUBEDGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `(x + e) - (x - e):real^3 = &2 % e` ASSUME_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(a':real^3) IN affine hull {x - e,x + e,a}` THENL
   [ALL_TAC;
    (* bent: the wedge of MOI_FGB_WEDGE_CASE *)
    MP_TAC(ISPECL [`x - e:real^3`; `x + e:real^3`; `a:real^3`; `a':real^3`; `inv(&2)`]
                  MOI_FGB_WEDGE_CASE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r3:real` (X_CHOOSE_THEN `n1:real^3` (X_CHOOSE_THEN `n2:real^3`
      STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `min r1 (min r2 r3):real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`n1:real^3`; `n2:real^3`] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(n1:real^3) dot (&2 % e) = &0` THEN
      REWRITE_TAC[DOT_RMUL] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(n2:real^3) dot (&2 % e) = &0` THEN
      REWRITE_TAC[DOT_RMUL] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_SIMP_TAC[]]] THEN
  (* coplanar: the triangles lie on opposite sides of the line *)
  MP_TAC(ISPECL [`x - e:real^3`; `x + e:real^3`; `a:real^3`; `inv(&2)`] MOI_FGB_TRI_PLANE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`e:real^3`; `a - x:real^3`] MOI_S4Z_ORTH) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `l:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a:real^3`] MOI_FGB_OFF_LINE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a:real^3 = (&1 - (u + l)) % p + (u + l) % q` SUBST1_TAC THENL
     [UNDISCH_TAC `a - x:real^3 = l % e` THEN EXPAND_TAC "e" THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rand(concl th) = `x:real^3` && can (find_term ((=) `u:real`)) (lhs(concl th)) &&
        not (can (find_term ((=) `u':real`)) (lhs(concl th))))) THEN
      VECTOR_ARITH_TAC;
      REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`&1 - (u + l)`; `u + l:real`] THEN REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `c:real`))))) THEN
  MP_TAC(ISPECL [`x - e:real^3`; `x + e:real^3`; `a:real^3`; `a':real^3`; `n:real^3`;
                 `v:real^3`; `x:real^3`; `c / &2`; `min r (min r1 r2):real`]
                MOI_S4Z_FLAT_CASE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[DOT_RMUL; REAL_MUL_RZERO];
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN affine hull {p,q}` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `affine hull {p:real^3,q}`)) (concl th) &&
          can (find_term ((=) `a':real^3`)) (concl th))) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `s2:real` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `z - x:real^3 = (s2 - u) % e` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN EXPAND_TAC "e" THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rand(concl th) = `x:real^3` && can (find_term ((=) `u:real`)) (lhs(concl th)) &&
          not (can (find_term ((=) `u':real`)) (lhs(concl th))))) THEN
        SUBGOAL_THEN `s1 = &1 - s2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
        ASM_REWRITE_TAC[DOT_RMUL; REAL_MUL_RZERO]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r4:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r1 (min r2 r4):real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  SUBGOAL_THEN `(n:real^3) dot e = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `(n:real^3) dot (&2 % e) = &0` THEN REWRITE_TAC[DOT_RMUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(n:real^3) dot v = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(n:real^3) dot (a - x) = &0` MP_TAC THENL
     [FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `n:real^3`)) (concl th) &&
        can (find_term ((=) `affine hull {p:real^3,q,a}`)) (concl th))) THEN
      MATCH_MP_TAC HULL_INC THEN SET_TAC[];
      ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`n:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Part 7: the crossing models at rim points.  A plane P transverse to      *)
(* the rim line against the local form of F (a plane or a wedge): the       *)
(* surface crossing by MOI_FGB_MODEL_P or MOI_FGB_MODEL_W, the curve        *)
(* crossing of the trace with the rim inside F by the slice chart of an     *)
(* explicit PL homeomorphism of real^3 (rows of normals, then the fold map  *)
(* of MOI_FGB_FOLD1_PLH in the wedge case).                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Z_INDEP3 = prove
 (`!n1 n2 m e:real^3.
     (!s1 s2. s1 % n1 + s2 % n2 = vec 0 ==> s1 = &0 /\ s2 = &0) /\
     n1 dot e = &0 /\ n2 dot e = &0 /\ ~(m dot e = &0)
     ==> !a b c. a % n1 + b % n2 + c % m = vec 0 ==> a = &0 /\ b = &0 /\ c = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `c = &0` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `\w:real^3. w dot e`) THEN
    ASM_REWRITE_TAC[DOT_LADD; DOT_LMUL; DOT_LZERO; REAL_MUL_RZERO; REAL_ADD_LID] THEN
    ASM_REWRITE_TAC[REAL_ENTIRE];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `a % n1 + b % n2 + &0 % m:real^3 = vec 0` THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID]);;

(* The slice chart: a PL homeomorphism of real^3 that straightens X near x  *)
(* to its first coordinate plane, J INTER X to the third axis and K INTER X *)
(* to the second axis gives the curve crossing of J and K in X at x.        *)

let MOI_S4Z_SLICE_CHART = prove
 (`!(f:real^3->real^3) g x r (X:real^3->bool) J K.
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ f x = vec 0 /\ &0 < r /\
     (!z. dist(x,z) < r ==> (z IN X <=> (f z)$1 = &0)) /\
     (!z. dist(x,z) < r ==> (z IN J /\ z IN X <=> (f z)$1 = &0 /\ (f z)$2 = &0)) /\
     (!z. dist(x,z) < r ==> (z IN K /\ z IN X <=> (f z)$1 = &0 /\ (f z)$3 = &0))
     ==> pl_curve_crossing_at X J K x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism; IN_UNIV] th))
    STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `u = X INTER ball(x:real^3,r)` THEN
  SUBGOAL_THEN `!z:real^3. z IN u <=> dist(x,z) < r /\ ((f:real^3->real^3) z)$1 = &0` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `L = \w:real^3. vector[w$2; w$3]:real^2` THEN
  ABBREV_TAC `M = \y:real^2. vector[&0; y$1; y$2]:real^3` THEN
  SUBGOAL_THEN `linear (L:real^3->real^2) /\ linear (M:real^2->real^3)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "M"] THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; VECTOR_2;
                VECTOR_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w$1 = &0 ==> M((L:real^3->real^2) w) = w` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "M"] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_2; VECTOR_3];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. L((M:real^2->real^3) y) = y /\ (M y)$1 = &0` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "M"] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_3];
    ALL_TAC] THEN
  REWRITE_TAC[pl_curve_crossing_at] THEN
  MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `(L:real^3->real^2) o (f:real^3->real^3)`;
                        `(g:real^3->real^3) o (M:real^2->real^3)`] THEN
  SUBGOAL_THEN `(x:real^3) IN u` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DIST_REFL; VEC_COMPONENT]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN u
                           ==> ((g:real^3->real^3) o (M:real^2->real^3))
                               (((L:real^3->real^2) o (f:real^3->real^3)) z) = z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `((f:real^3->real^3) z)$1 = &0` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN u` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((L:real^3->real^2) o (f:real^3->real^3)) (u:real^3->bool) =
                {y | (g:real^3->real^3) ((M:real^2->real^3) y) IN ball(x:real^3,r)}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^2` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; o_THM; IN_BALL] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(z:real^3) IN u` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `(g:real^3->real^3) ((M:real^2->real^3) y)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[pl_homeomorphism] THEN
    SUBGOAL_THEN `pl_map_on (u:real^3->bool) ((L:real^3->real^2) o (f:real^3->real^3))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV] THEN
        SUBGOAL_THEN `(u:real^3->bool) =
                      {z:real^3 | z IN ball(x,r) /\
                                  (f:real^3->real^3) z IN {w:real^3 | basis 1 dot w = &0}}`
        SUBST1_TAC THENL
         [GEN_REWRITE_TAC I [EXTENSION] THEN
          ASM_SIMP_TAC[IN_ELIM_THM; IN_BALL; DOT_BASIS; DIMINDEX_3; ARITH];
          MATCH_MP_TAC MOI_PTR_LOCALLY_POLYHEDRAL_PL_PREIMAGE THEN
          REWRITE_TAC[POLYHEDRON_HYPERPLANE] THEN
          MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
          ASM_SIMP_TAC[SUBSET_UNIV; LOCALLY_POLYHEDRAL_OPEN; OPEN_BALL]];
        SUBGOAL_THEN `(L:real^3->real^2) = (\w. L w + vec 0)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_RID]; ALL_TAC] THEN
        MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
        ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]];
      ALL_TAC] THEN
    SUBGOAL_THEN `homeomorphism ((u:real^3->bool),
                                 IMAGE ((L:real^3->real^2) o (f:real^3->real^3)) u)
                                (L o f,(g:real^3->real^3) o (M:real^2->real^3))`
    ASSUME_TAC THENL
     [REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON_COMPOSE THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
        REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC(SET_RULE `(!z. z IN u ==> (g:real^2->real^3)((f:real^3->real^2) z) = z)
                               ==> IMAGE g (IMAGE f u) = (u:real^3->bool)`) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
      MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `(L:real^3->real^2) o (f:real^3->real^3)`] THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(g:real^3->real^3) o (M:real^2->real^3)`; `(:real^2)`; `ball(x:real^3,r)`]
                  CONTINUOUS_OPEN_PREIMAGE) THEN
    REWRITE_TAC[OPEN_UNIV; OPEN_BALL; IN_UNIV; o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ASM_REWRITE_TAC[o_THM] THEN EXPAND_TAC "L" THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^2` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM; o_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
       [EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(z:real^3) IN u` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        SUBGOAL_THEN `((f:real^3->real^3) z)$2 = &0` MP_TAC THENL
         [ASM_MESON_TAC[]; EXPAND_TAC "L" THEN SIMP_TAC[VECTOR_2]]];
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN REWRITE_TAC[VECTOR_2] THEN DISCH_TAC THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN u` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^2` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM; o_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
       [EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(z:real^3) IN u` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        SUBGOAL_THEN `((f:real^3->real^3) z)$3 = &0` MP_TAC THENL
         [ASM_MESON_TAC[]; EXPAND_TAC "L" THEN SIMP_TAC[VECTOR_2]]];
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN REWRITE_TAC[VECTOR_2] THEN DISCH_TAC THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN u` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]]);;

(* The crossing at a rim point: S (a plane through x transverse to the rim *)
(* line) against FF (near x a plane or a wedge along the line).             *)

let MOI_S4Z_RIM_CROSS = prove
 (`!(S:real^3->bool) FF R x e m r.
     ~(e = vec 0) /\ ~(m dot e = &0) /\ &0 < r /\
     (!z. dist(x,z) < r ==> (z IN S <=> m dot (z - x) = &0)) /\
     (!z. dist(x,z) < r ==> (z IN R <=> ?l. z = x + l % e)) /\
     (!z. dist(x,z) < r /\ z IN R ==> z IN FF) /\
     ((?n k. ~(n = vec 0) /\ n dot e = &0 /\ ~(k = vec 0) /\ k dot e = &0 /\
             n dot k = &0 /\
             !z. dist(x,z) < r ==> (z IN FF <=> n dot (z - x) = &0)) \/
      (?n1 n2. n1 dot e = &0 /\ n2 dot e = &0 /\
               (!s1 s2. s1 % n1 + s2 % n2 = vec 0 ==> s1 = &0 /\ s2 = &0) /\
               !z. dist(x,z) < r
                   ==> (z IN FF <=>
                        n1 dot (z - x) = &0 /\ &0 <= n2 dot (z - x) \/
                        n2 dot (z - x) = &0 /\ &0 <= n1 dot (z - x))))
     ==> pl_crossing_at S FF x /\ pl_curve_crossing_at FF (S INTER FF) R x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "S")
    (CONJUNCTS_THEN2 (LABEL_TAC "R") (CONJUNCTS_THEN2 (LABEL_TAC "RF") MP_TAC)))))) THEN
  (* translation to x *)
  MP_TAC(ISPEC `x:real^3` MOI_FGB_TRANSLATE_PLH) THEN DISCH_TAC THEN
  (* the rows map and its injectivity; the slice chart *)
  SUBGOAL_THEN
   `!a b c:real^3.
      (!s1 s2 s3. s1 % a + s2 % b + s3 % c = vec 0 ==> s1 = &0 /\ s2 = &0 /\ s3 = &0)
      ==> ?g. pl_homeomorphism ((:real^3),(:real^3))
                ((\z. vector[a dot (z - x); b dot (z - x); c dot (z - x)]:real^3),g) /\
              (!w w'. vector[a dot w; b dot w; c dot w]:real^3 =
                      vector[a dot w'; b dot w'; c dot w'] ==> w = w')`
  (LABEL_TAC "rows") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `c:real^3`] MOI_FGB_ROWS_PLH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g0:real^3->real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(\z:real^3. z + x) o (g0:real^3->real^3)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\z:real^3. vector[a dot (z - x); b dot (z - x); c dot (z - x)]:real^3) =
                    (\z. vector[a dot z; b dot z; c dot z]) o (\z. z - x)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `pl_homeomorphism ((:real^3),(:real^3))
                   ((\z. vector[a dot z; b dot z; c dot z]:real^3),g0)` THEN
      REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2
   (X_CHOOSE_THEN `n:real^3` (X_CHOOSE_THEN `k:real^3` STRIP_ASSUME_TAC))
   (X_CHOOSE_THEN `n1:real^3` (X_CHOOSE_THEN `n2:real^3` STRIP_ASSUME_TAC))) THENL
   [(* plane case *)
    SUBGOAL_THEN `!s1 s2 s3. s1 % n + s2 % m + s3 % k = vec 0:real^3
                             ==> s1 = &0 /\ s2 = &0 /\ s3 = &0` ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `s2 = &0` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o AP_TERM `\w:real^3. w dot e`) THEN
        ASM_REWRITE_TAC[DOT_LADD; DOT_LMUL; DOT_LZERO; REAL_MUL_RZERO; REAL_ADD_LID;
                        REAL_ADD_RID; REAL_ENTIRE];
        ALL_TAC] THEN
      SUBGOAL_THEN `s3 = &0` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o AP_TERM `\w:real^3. w dot k`) THEN
        ASM_REWRITE_TAC[DOT_LADD; DOT_LMUL; DOT_LZERO; REAL_MUL_RZERO; REAL_ADD_LID;
                        REAL_MUL_LZERO; REAL_ADD_RID; REAL_ENTIRE; DOT_EQ_0];
        ALL_TAC] THEN
      UNDISCH_TAC `s1 % n + &0 % m + &0 % k:real^3 = vec 0` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_EQ_0];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FGB_CROSS_FROM_MODEL THEN
      MAP_EVERY EXISTS_TAC [`{z:real^3 | m dot (z - x) = &0}`;
                            `{z:real^3 | n dot (z - x) = &0}`; `r:real`] THEN
      (* the two local equalities are assumptions: only the model remains *)
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC MOI_FGB_MODEL_P THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`b:real`; `a:real`; `&0`]) THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[VECTOR_ADD_SYM]; SIMP_TAC[]];
      USE_THEN "rows" (MP_TAC o SPECL [`n:real^3`; `m:real^3`; `k:real^3`]) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC MOI_S4Z_SLICE_CHART THEN
      MAP_EVERY EXISTS_TAC
       [`\z:real^3. vector[n dot (z - x); m dot (z - x); k dot (z - x)]:real^3`;
        `g:real^3->real^3`; `r:real`] THEN
      ASM_REWRITE_TAC[VECTOR_3; VECTOR_SUB_REFL; DOT_RZERO; IN_INTER] THEN
      REPEAT CONJ_TAC THENL
       [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT];
        X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
        USE_THEN "S" (fun th -> MP_TAC(MP (SPEC `z:real^3` th)
          (ASSUME `dist(x:real^3,z) < r`))) THEN
        FIRST_X_ASSUM((fun th -> MP_TAC(MP (SPEC `z:real^3` th)
          (ASSUME `dist(x:real^3,z) < r`))) o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `FF:real^3->bool`)) (concl th) &&
          can (find_term ((=) `n:real^3`)) (concl th))) THEN
        CONV_TAC TAUT;
        X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EQ_TAC THENL
         [STRIP_TAC THEN
          USE_THEN "R" (fun th -> MP_TAC(MP (SPEC `z:real^3` th)
            (ASSUME `dist(x:real^3,z) < r`))) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_THEN(X_CHOOSE_THEN `l:real` SUBST1_TAC) THEN
          ASM_REWRITE_TAC[VECTOR_ARITH `(x + l % e) - x:real^3 = l % e`; DOT_RMUL] THEN
          REAL_ARITH_TAC;
          STRIP_TAC THEN
          SUBGOAL_THEN `(z:real^3) IN R` ASSUME_TAC THENL
           [USE_THEN "R" (fun th -> REWRITE_TAC[MP (SPEC `z:real^3` th)
              (ASSUME `dist(x:real^3,z) < r`)]) THEN
            EXISTS_TAC `(m dot (z - x)) / (m dot e:real^3)` THEN
            MATCH_MP_TAC(VECTOR_ARITH `z - x = w ==> z = x + w:real^3`) THEN
            FIRST_X_ASSUM MATCH_MP_TAC THEN
            ASM_REWRITE_TAC[DOT_RMUL] THEN
            SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
            ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
            UNDISCH_TAC `~((m:real^3) dot e = &0)` THEN CONV_TAC REAL_FIELD;
            ASM_REWRITE_TAC[] THEN USE_THEN "RF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]]];
    (* wedge case *)
    MP_TAC(ISPECL [`n1:real^3`; `n2:real^3`; `m:real^3`; `e:real^3`] MOI_S4Z_INDEP3) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FGB_CROSS_FROM_MODEL THEN
      MAP_EVERY EXISTS_TAC
       [`{z:real^3 | m dot (z - x) = &0}`;
        `{z:real^3 | n1 dot (z - x) = &0 /\ &0 <= n2 dot (z - x) \/
                     n2 dot (z - x) = &0 /\ &0 <= n1 dot (z - x)}`; `r:real`] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`x:real^3`; `n1:real^3`; `n2:real^3`; `m:real^3`] MOI_FGB_MODEL_W) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      USE_THEN "rows" (MP_TAC o SPECL [`n1:real^3`; `n2:real^3`; `m:real^3`]) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC MOI_S4Z_SLICE_CHART THEN
      MAP_EVERY EXISTS_TAC
       [`(\p:real^3. vector[min (p$1) (p$2); p$3; p$1 - p$2]:real^3) o
         (\z:real^3. vector[n1 dot (z - x); n2 dot (z - x); m dot (z - x)]:real^3)`;
        `(g:real^3->real^3) o
         (\q:real^3. vector[q$1 + max (q$3) (&0); q$1 - min (q$3) (&0); q$2]:real^3)`;
        `r:real`] THEN
      ASM_REWRITE_TAC[o_THM; VECTOR_3; VECTOR_SUB_REFL; DOT_RZERO; IN_INTER] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[MOI_FGB_FOLD1_PLH];
        SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT] THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
        FIRST_ASSUM((fun th -> REWRITE_TAC[MP (SPEC `z:real^3` th)
          (ASSUME `dist(x:real^3,z) < r`)]) o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `FF:real^3->bool`)) (concl th) &&
          can (find_term ((=) `n1:real^3`)) (concl th))) THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
        USE_THEN "S" (fun th -> REWRITE_TAC[MP (SPEC `z:real^3` th)
          (ASSUME `dist(x:real^3,z) < r`)]) THEN
        FIRST_ASSUM((fun th -> REWRITE_TAC[MP (SPEC `z:real^3` th)
          (ASSUME `dist(x:real^3,z) < r`)]) o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `FF:real^3->bool`)) (concl th) &&
          can (find_term ((=) `n1:real^3`)) (concl th))) THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `min ((n1:real^3) dot (z - x)) (n2 dot (z - x)) = &0 /\
                      n1 dot (z - x) - n2 dot (z - x) = &0 <=>
                      n1 dot (z - x) = &0 /\ n2 dot (z - x) = &0` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        EQ_TAC THENL
         [STRIP_TAC THEN
          USE_THEN "R" (fun th -> MP_TAC(MP (SPEC `z:real^3` th)
            (ASSUME `dist(x:real^3,z) < r`))) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_THEN(X_CHOOSE_THEN `l:real` SUBST1_TAC) THEN
          ASM_REWRITE_TAC[VECTOR_ARITH `(x + l % e) - x:real^3 = l % e`; DOT_RMUL] THEN
          REAL_ARITH_TAC;
          STRIP_TAC THEN
          SUBGOAL_THEN `(z:real^3) IN R` ASSUME_TAC THENL
           [USE_THEN "R" (fun th -> REWRITE_TAC[MP (SPEC `z:real^3` th)
              (ASSUME `dist(x:real^3,z) < r`)]) THEN
            EXISTS_TAC `(m dot (z - x)) / (m dot e:real^3)` THEN
            MATCH_MP_TAC(VECTOR_ARITH `z - x = w ==> z = x + w:real^3`) THEN
            FIRST_X_ASSUM MATCH_MP_TAC THEN
            ASM_REWRITE_TAC[DOT_RMUL] THEN
            SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
            ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
            UNDISCH_TAC `~((m:real^3) dot e = &0)` THEN CONV_TAC REAL_FIELD;
            ASM_REWRITE_TAC[] THEN USE_THEN "RF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]]]]);;


(* ------------------------------------------------------------------------- *)
(* Part 8: rim points.  Near a relative interior point of a segment the      *)
(* segment is its line; a segment in general position with every simplex   *)
(* of s0 + d meets s0 + d only in the relative interiors of triangles, and *)
(* near such a point s0 + d is a plane transverse to the segment; at a rim  *)
(* point the carrier in t_v is an edge.  Then MOI_S4Z_RIM_POINT: at a rim   *)
(* point x of R_vw on s0 + d both crossing conditions hold (MOI_S4Z_RIM_EDGE *)
(* for v and for w, MOI_S4Z_TWO_HALF, MOI_S4Z_RIM_CROSS).                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Z_SEG_LINE = prove
 (`!(p:real^3) q u.
     ~(p = q) /\ &0 < u /\ u < &1
     ==> ?r. &0 < r /\
             !z. dist((&1 - u) % p + u % q,z) < r
                 ==> (z IN convex hull {p,q} <=>
                      ?l. z = ((&1 - u) % p + u % q) + l % (q - p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(q - p:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `min u (&1 - u) * norm(q - p:real^3)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; IN_SEGMENT] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t - u:real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `l:real` SUBST_ALL_TAC) THEN
    EXISTS_TAC `u + l:real` THEN
    REWRITE_TAC[VECTOR_ARITH `((&1 - u) % p + u % q) + l % (q - p):real^3 =
                              (&1 - (u + l)) % p + (u + l) % q`] THEN
    UNDISCH_TAC `dist((&1 - u) % p + u % q,((&1 - u) % p + u % q) + l % (q - p):real^3) <
                 min u (&1 - u) * norm(q - p:real^3)` THEN
    REWRITE_TAC[dist; VECTOR_ARITH `a - (a + b):real^3 = --b`; NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN REAL_ARITH_TAC]);;

(* A segment in general position with the simplices of s0 + d: near a common *)
(* point s0 + d is a plane transverse to the segment.                        *)

let MOI_S4Z_PLANE_AT = prove
 (`!(s0:(real^3->bool)->bool) d x (p:real^3) q.
     combinatorial_manifold 2 s0 /\ ~(p = q) /\
     (!A. A IN s0 ==> affine_gp_3 (IMAGE (\y. d + y) A) (convex hull {p,q})) /\
     x IN IMAGE (\y. d + y) (UNIONS s0) /\ x IN convex hull {p,q}
     ==> ?r m. &0 < r /\ ~(m = vec 0) /\ ~(m dot (q - p) = &0) /\
               !z. dist(x,z) < r
                   ==> (z IN IMAGE (\y. d + y) (UNIONS s0) <=> m dot (z - x) = &0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "gp") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?y0:real^3. x = d + y0 /\ y0 IN UNIONS s0`
  (X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
   [UNDISCH_TAC `(x:real^3) IN IMAGE (\y. d + y) (UNIONS s0)` THEN REWRITE_TAC[IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (s0:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s0:(real^3->bool)->bool`; `y0:real^3`] MOI_FGB_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y0:real^3) IN A` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `affine_gp_3 (IMAGE (\y:real^3. d + y) A) (convex hull {p,q})` ASSUME_TAC THENL
   [USE_THEN "gp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(d + y0:real^3) IN IMAGE (\y. d + y) A INTER convex hull {p,q}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `y0:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (convex hull {p:real^3,q}) = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_2]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (A:real^3->bool) = &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&3 <= aff_dim (A:real^3->bool) + aff_dim (convex hull {p:real^3,q})`
    MP_TAC THENL
     [UNDISCH_TAC `affine_gp_3 (IMAGE (\y:real^3. d + y) A) (convex hull {p,q})` THEN
      REWRITE_TAC[affine_gp_3; AFF_DIM_TRANSLATION_EQ] THEN
      SUBGOAL_THEN `~DISJOINT (IMAGE (\y:real^3. d + y) A) (convex hull {p,q})`
      (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[DISJOINT] THEN ASM SET_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s0:(real^3->bool)->bool`; `A:real^3->bool`] MOI_FGB_CM2_DIM) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s0:(real^3->bool)->bool`; `A:real^3->bool`; `y0:real^3`; `d:real^3`]
    MOI_FGB_TRI_FORM_T) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `m:real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `m:real^3`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FGB_TRANSV_LINE THEN
  MAP_EVERY EXISTS_TAC [`convex hull {p:real^3,q}`; `IMAGE (\y:real^3. d + y) A`;
                        `d + y0:real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(d + y0:real^3) IN IMAGE (\y. d + y) A INTER convex hull {p,q}` THEN
    REWRITE_TAC[IN_INTER; GSYM SEGMENT_CONVEX_HULL; IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC)) THEN
    X_GEN_TAC `z:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t1 - t0:real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(d + y) - (d + y0):real^3 = y - y0`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `affine:(real^3->bool)->bool`)) (concl th))) THEN
    ASM_SIMP_TAC[HULL_INC];
    ONCE_REWRITE_TAC[UNION_COMM] THEN MATCH_MP_TAC MOI_FGP_GP_MEET_UNIV THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* At a rim point on s0 + d the carrier in t_v is an edge. *)

let MOI_S4Z_RIM_CARRIER = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v w t s0 d x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     ~(w = v) /\ segment[v,w] IN kk /\ moi_s4z_vtri tt kk f1 v t /\
     combinatorial_manifold 2 s0 /\
     (!A B. A IN s0 /\ B IN t ==> affine_gp_3 (IMAGE (\y. d + y) A) B) /\
     x IN IMAGE (\y. d + y) (UNIONS s0) /\
     x IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)
     ==> ?e. e IN t /\ aff_dim e = &1 /\ x IN relative_interior e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`] MOI_S4Z_RIM_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4Z_VTRI_CLOSED) THEN
  SUBGOAL_THEN `combinatorial_manifold 2 (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4z_vtri tt kk (f1:real^N->real^3) v t` THEN
    SIMP_TAC[moi_s4z_vtri];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN UNIONS t` ASSUME_TAC THENL
   [SUBGOAL_THEN `UNIONS t = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `moi_s4z_vtri tt kk (f1:real^N->real^3) v t` THEN
      SIMP_TAC[moi_s4z_vtri];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)
                 SUBSET frontier (IMAGE f1 (moi_s34_vb tt kk v))` THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    REWRITE_TAC[IMP_IMP] THEN
    MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET s' ==> x IN s /\ s' SUBSET t ==> x IN t`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `x:real^3`] MOI_FGB_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`; `t:(real^3->bool)->bool`; `x:real^3`;
                 `e:real^3->bool`] MOI_S4Z_RIM_NOT_TRI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN e` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~(aff_dim (e:real^3->bool) = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `?y0 (A:real^3->bool). x = d + y0 /\ A IN s0 /\ y0 IN A`
    (X_CHOOSE_THEN `y0:real^3` (X_CHOOSE_THEN `A:real^3->bool`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THENL
     [UNDISCH_TAC `(x:real^3) IN IMAGE (\y. d + y) (UNIONS s0)` THEN
      REWRITE_TAC[IN_IMAGE; IN_UNIONS] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `affine_gp_3 (IMAGE (\y:real^3. d + y) A) e` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `affine_gp_3`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[affine_gp_3; AFF_DIM_TRANSLATION_EQ] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s0:(real^3->bool)->bool`; `A:real^3->bool`] MOI_FGB_CM2_DIM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `~p /\ ~q ==> ~(p \/ q /\ r)`) THEN CONJ_TAC THENL
     [REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
      EXISTS_TAC `d + y0:real^3` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `y0:real^3` THEN ASM_REWRITE_TAC[];
      ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `e:real^3->bool`] MOI_FGB_CM2_DIM) THEN
  SUBGOAL_THEN `~(aff_dim (e:real^3->bool) = -- &1)` MP_TAC THENL
   [REWRITE_TAC[AFF_DIM_EQ_MINUS1] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `e:real^3->bool` AFF_DIM_GE) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(aff_dim (e:real^3->bool) = &0)` THEN
  UNDISCH_TAC `~(aff_dim (e:real^3->bool) = &2)` THEN
  INT_ARITH_TAC);;

(* Label the conjuncts of a hypothesis in order. *)

let rec moi_s4z_labels labs th =
  match labs with
    [] -> ALL_TAC
  | [l] -> LABEL_TAC l th
  | l::ls -> CONJUNCTS_THEN2 (LABEL_TAC l) (moi_s4z_labels ls) th;;

(* The local geometry at a rim point x: S a plane transverse to the rim     *)
(* line, F locally A_v UNION A_w, near x A_v and A_w are triangles on edges *)
(* through x, the rim is either edge, A_v INTER A_w lies in the rim.        *)

let MOI_S4Z_RIM_GEOM = prove
 (`!(S:real^3->bool) FF Av Aw R x p q a p' q' a' m r.
     ~(p = q) /\ ~(a = p) /\ ~(a = q) /\ ~affine_dependent {p,q,a} /\
     ~(p' = q') /\ ~(a' = p') /\ ~(a' = q') /\ ~affine_dependent {p',q',a'} /\
     x IN relative_interior (convex hull {p,q}) /\
     x IN relative_interior (convex hull {p',q'}) /\
     ~(m dot (q - p) = &0) /\ &0 < r /\
     (!z. dist(x,z) < r ==> (z IN S <=> m dot (z - x) = &0)) /\
     (!z. dist(x,z) < r ==> (z IN FF <=> z IN Av \/ z IN Aw)) /\
     (!z. dist(x,z) < r ==> (z IN Av <=> z IN convex hull {p,q,a})) /\
     (!z. dist(x,z) < r ==> (z IN Aw <=> z IN convex hull {p',q',a'})) /\
     (!z. dist(x,z) < r ==> (z IN R <=> z IN convex hull {p,q})) /\
     (!z. dist(x,z) < r ==> (z IN R <=> z IN convex hull {p',q'})) /\
     (!z. z IN Av /\ z IN Aw ==> z IN R) /\ R SUBSET FF
     ==> pl_crossing_at S FF x /\ pl_curve_crossing_at FF (S INTER FF) R x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(moi_s4z_labels
    ["pq"; "ap"; "aq"; "ind"; "pq'"; "ap'"; "aq'"; "ind'"; "xr"; "xr'"; "me"; "r";
     "S"; "F"; "Av"; "Aw"; "R1"; "R2"; "AvAw"; "RF"]) THEN
  SUBGOAL_THEN `?u. &0 < u /\ u < &1 /\ (&1 - u) % p + u % q = x:real^3`
  (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THENL
   [USE_THEN "xr" (MP_TAC o REWRITE_RULE[GSYM SEGMENT_CONVEX_HULL;
      RELATIVE_INTERIOR_SEGMENT; ASSUME `~(p:real^3 = q)`; IN_SEGMENT]) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u'. &0 < u' /\ u' < &1 /\ (&1 - u') % p' + u' % q' = x:real^3`
  (X_CHOOSE_THEN `u':real` STRIP_ASSUME_TAC) THENL
   [USE_THEN "xr'" (MP_TAC o REWRITE_RULE[GSYM SEGMENT_CONVEX_HULL;
      RELATIVE_INTERIOR_SEGMENT; ASSUME `~(p':real^3 = q')`; IN_SEGMENT]) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `u:real`] MOI_S4Z_SEG_LINE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "line"))) THEN
  SUBGOAL_THEN `!z:real^3. dist(x,z) < r ==> z IN convex hull {p',q'} ==> z IN convex hull {p,q}`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "R1" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `z:real^3` th)
      (ASSUME `dist(x:real^3,z) < r`))]) THEN
    USE_THEN "R2" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `z:real^3` th)
      (ASSUME `dist(x:real^3,z) < r`))]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. dist(x,z) < r /\ z IN convex hull {p,q,a} /\
                           z IN convex hull {p',q',a'} ==> z IN affine hull {p,q}`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
    USE_THEN "R1" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `z:real^3` th)
      (ASSUME `dist(x:real^3,z) < r`))]) THEN
    USE_THEN "AvAw" MATCH_MP_TAC THEN
    USE_THEN "Av" (fun th -> REWRITE_TAC[MP (SPEC `z:real^3` th)
      (ASSUME `dist(x:real^3,z) < r`)]) THEN
    USE_THEN "Aw" (fun th -> REWRITE_TAC[MP (SPEC `z:real^3` th)
      (ASSUME `dist(x:real^3,z) < r`)]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^3`; `q:real^3`; `a:real^3`; `p':real^3`; `q':real^3`; `a':real^3`;
                 `u:real`; `u':real`; `r:real`] MOI_S4Z_TWO_HALF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "two"))) THEN
  MATCH_MP_TAC MOI_S4Z_RIM_CROSS THEN
  MAP_EVERY EXISTS_TAC [`q - p:real^3`; `m:real^3`; `min r (min r1 r4)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[REAL_LT_MIN];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN USE_THEN "S" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `dist(x:real^3,z) < r /\ dist(x,z) < r4` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "R1" (fun th -> REWRITE_TAC[MP (SPEC `z:real^3` th)
      (ASSUME `dist(x:real^3,z) < r`)]) THEN
    USE_THEN "line" (fun th -> REWRITE_TAC[MP (SPEC `z:real^3` th)
      (ASSUME `dist(x:real^3,z) < r4`)]);
    REPEAT STRIP_TAC THEN USE_THEN "RF" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. dist(x,z) < min r (min r1 r4)
                           ==> dist(x,z) < r /\ dist(x,z) < r1` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "two" (DISJ_CASES_THEN2
    (X_CHOOSE_THEN `n:real^3` (X_CHOOSE_THEN `k:real^3` STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `n1:real^3` (X_CHOOSE_THEN `n2:real^3` STRIP_ASSUME_TAC))) THENL
   [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`n:real^3`; `k:real^3`];
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`n1:real^3`; `n2:real^3`]] THEN
  (ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
   SUBGOAL_THEN `dist(x:real^3,z) < r /\ dist(x,z) < r1` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
   USE_THEN "F" (fun th -> REWRITE_TAC[MP (SPEC `z:real^3` th)
     (ASSUME `dist(x:real^3,z) < r`)]) THEN
   USE_THEN "Av" (fun th -> REWRITE_TAC[MP (SPEC `z:real^3` th)
     (ASSUME `dist(x:real^3,z) < r`)]) THEN
   USE_THEN "Aw" (fun th -> REWRITE_TAC[MP (SPEC `z:real^3` th)
     (ASSUME `dist(x:real^3,z) < r`)]) THEN
   FIRST_X_ASSUM((fun th -> REWRITE_TAC[MP (SPEC `z:real^3` th)
     (ASSUME `dist(x:real^3,z) < r1`)]) o check (fun th -> is_forall(concl th) &&
     can (find_term ((=) `r1:real`)) (concl th) &&
     can (find_term ((=) `p':real^3`)) (concl th)))));;

(* Both crossing conditions at a rim point of R_vw on s0 + d. *)

let MOI_S4Z_RIM_POINT = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v w tv tw s0 d x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     ~(w = v) /\ segment[v,w] IN kk /\
     moi_s4z_vtri tt kk f1 v tv /\ moi_s4z_vtri tt kk f1 w tw /\
     combinatorial_manifold 2 s0 /\
     (!A B. A IN s0 /\ (B IN tv \/ B IN tw) ==> affine_gp_3 (IMAGE (\y. d + y) A) B) /\
     x IN IMAGE (\y. d + y) (UNIONS s0) /\
     x IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)
     ==> pl_crossing_at (IMAGE (\y. d + y) (UNIONS s0)) (IMAGE f1 (moi_s34_bd tt kk)) x /\
         pl_curve_crossing_at (IMAGE f1 (moi_s34_bd tt kk))
           (IMAGE (\y. d + y) (UNIONS s0) INTER IMAGE f1 (moi_s34_bd tt kk))
           (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                      moi_s34_bd tt kk)) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `v:real^N`; `w:real^N`] MOI_S4L_EDGE_SD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `segment[w:real^N,v] IN kk /\ ~(v:real^N = w) /\
    IMAGE (f1:real^N->real^3)
      (moi_s34_vb tt kk w INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk) =
    IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[];
      AP_TERM_TAC THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!A B. A IN s0 /\ B IN tv ==> affine_gp_3 (IMAGE (\y:real^3. d + y) A) B) /\
    (!A B. A IN s0 /\ B IN tw ==> affine_gp_3 (IMAGE (\y:real^3. d + y) A) B)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `tw:(real^3->bool)->bool`)) (concl th) &&
      can (find_term ((=) `tv:(real^3->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) /\
                x IN IMAGE f1 (moi_s34_vb tt kk w)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the carriers of x in t_v and t_w are edges *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`; `tv:(real^3->bool)->bool`;
                 `s0:(real^3->bool)->bool`; `d:real^3`; `x:real^3`] MOI_S4Z_RIM_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ev:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `w:real^N`; `v:real^N`; `tw:(real^3->bool)->bool`;
                 `s0:(real^3->bool)->bool`; `d:real^3`; `x:real^3`] MOI_S4Z_RIM_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ew:real^3->bool` STRIP_ASSUME_TAC) THEN
  (* the triangles of A_v and A_w at the two edges *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`; `tv:(real^3->bool)->bool`; `x:real^3`;
                 `ev:real^3->bool`] MOI_S4Z_RIM_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `q:real^3` (X_CHOOSE_THEN `a:real^3`
    (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `ev:real^3->bool`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `w:real^N`; `v:real^N`; `tw:(real^3->bool)->bool`; `x:real^3`;
                 `ew:real^3->bool`] MOI_S4Z_RIM_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p':real^3` (X_CHOOSE_THEN `q':real^3` (X_CHOOSE_THEN `a':real^3`
    (X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `ew:real^3->bool`)) THEN
  (* near x: s0 + d is a plane transverse to the edge *)
  MP_TAC(ISPECL [`s0:(real^3->bool)->bool`; `d:real^3`; `x:real^3`; `p:real^3`; `q:real^3`]
    MOI_S4Z_PLANE_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `A:real^3->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `tv:(real^3->bool)->bool`)) (concl th) &&
        can (find_term ((=) `affine_gp_3`)) (concl th) &&
        not (can (find_term ((=) `tw:(real^3->bool)->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    DISCH_THEN(X_CHOOSE_THEN `r0:real` (X_CHOOSE_THEN `m:real^3` STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`; `x:real^3`] MOI_S4L_LOCAL_AV_AW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `oo:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
    IMAGE f1 (moi_s34_bd tt kk) /\
    IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w INTER moi_s34_bd tt kk) SUBSET
    IMAGE f1 (moi_s34_bd tt kk)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
        z IN IMAGE f1 (moi_s34_vb tt kk w INTER moi_s34_bd tt kk)
        ==> z IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                           moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN IMAGE (f1:real^N->real^3)
                     (moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                   `v:real^N`; `w:real^N`; `z:real^3`] MOI_S4L_AV_NO_OTHER) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?rr. &0 < rr /\ rr <= r0 /\ rr <= r1 /\ rr <= r2 /\ rr <= r3`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min r0 (min r1 (min r2 r3))` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4Z_RIM_GEOM THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`;
    `p:real^3`; `q:real^3`; `a:real^3`; `p':real^3`; `q':real^3`; `a':real^3`;
    `m:real^3`; `rr:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REAL_ARITH_TAC)) THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN oo` ASSUME_TAC THENL
       [UNDISCH_TAC `ball(x:real^3,r3) SUBSET oo` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER oo SUBSET
                   IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
                   IMAGE f1 (moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNION] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
                      SUBSET IMAGE f1 (moi_s34_bd tt kk)`)) THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w INTER moi_s34_bd tt kk)
                      SUBSET IMAGE f1 (moi_s34_bd tt kk)`)) THEN ASM_REWRITE_TAC[]]];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Part 9: trace points off the rims.  A splitting disk at v lies in         *)
(* the vertex ball of its other end; so near a point of A_v in no other      *)
(* vertex ball no disk at v passes, Sigma_v = A_v = F there, and the surface *)
(* crossing of s0 + d with UNIONS t_v (MOI_FGB_LOCAL_CROSS) is a crossing   *)
(* with F (MOI_FGB_CROSSING_LOCAL).                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4Z_DISK_OTHER = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) g v.
     moi_s34_tube tt kk /\ g IN moi_s34_simp kk (&1) /\ {v} IN kk /\ v IN g
     ==> ?w. {w} IN kk /\ ~(w = v) /\
             IMAGE f1 (moi_s34_sd tt kk g) SUBSET IMAGE f1 (moi_s34_vb tt kk w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
    MOI_S4L_EDGE_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(v:real^N) IN {u,w}` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `{u:real^N,w}`)) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
   [EXISTS_TAC `w:real^N`; EXISTS_TAC `u:real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]) THEN ASM_MESON_TAC[]);;

let MOI_S4Z_DISKS_AWAY = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     (!w. {w} IN kk /\ ~(w = v) ==> ~(x IN IMAGE f1 (moi_s34_vb tt kk w)))
     ==> ?r. &0 < r /\
             !z. dist(x,z) < r
                 ==> ~(z IN UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g |
                                    g IN moi_s34_simp kk (&1) /\ v IN g})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "away")))) THEN
  ABBREV_TAC `D = UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
                          g IN moi_s34_simp kk (&1) /\ v IN g}` THEN
  SUBGOAL_THEN `closed (D:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC MOI_S4Z_EDGES_FINITE THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
      MATCH_MP_TAC MOI_S4K_CELL_POLY THEN
      MAP_EVERY EXISTS_TAC
       [`2`; `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`] THEN
      MATCH_MP_TAC MOI_S4Z_FRAME_DISK THEN
      MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                            `car:(real^N->bool)->real^3->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^3) IN D)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `E:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `f1:real^N->real^3`; `g:real^N->bool`; `v:real^N`] MOI_S4Z_DISK_OTHER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    USE_THEN "away" (fun th -> MP_TAC(MP (SPEC `w:real^N` th)
      (CONJ (ASSUME `{w:real^N} IN kk`) (ASSUME `~(w:real^N = v)`)))) THEN
    UNDISCH_TAC `(x:real^3) IN E` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) SUBSET
                 IMAGE f1 (moi_s34_vb tt kk w)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:real^3) DIFF D` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[GSYM closed] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  UNDISCH_TAC `ball(x:real^3,r) SUBSET (:real^3) DIFF D` THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The surface crossing at a trace point of A_v in no other vertex ball. *)

let MOI_S4Z_OFF_RIM = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v t s0 d x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     moi_s4z_vtri tt kk f1 v t /\ combinatorial_manifold 2 s0 /\
     (!A B. A IN s0 /\ B IN t ==> affine_gp_3 (IMAGE (\y. d + y) A) B) /\
     x IN IMAGE (\y. d + y) (UNIONS s0) /\
     x IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
     (!w. {w} IN kk /\ ~(w = v) ==> ~(x IN IMAGE f1 (moi_s34_vb tt kk w)))
     ==> pl_crossing_at (IMAGE (\y. d + y) (UNIONS s0)) (IMAGE f1 (moi_s34_bd tt kk)) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `combinatorial_manifold 2 (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4z_vtri tt kk (f1:real^N->real^3) v t` THEN
    SIMP_TAC[moi_s4z_vtri];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN UNIONS t <=>
        y IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) \/
        y IN UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g |
                     g IN moi_s34_simp kk (&1) /\ v IN g}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM IN_UNION; GSYM(last(CONJUNCTS th))]) THEN
    UNDISCH_TAC `moi_s4z_vtri tt kk (f1:real^N->real^3) v t` THEN
    SIMP_TAC[moi_s4z_vtri];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
                IMAGE f1 (moi_s34_bd tt kk)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s0:(real^3->bool)->bool`; `t:(real^3->bool)->bool`; `d:real^3`;
                 `x:real^3`] MOI_FGB_LOCAL_CROSS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `x:real^3`] MOI_S4Z_DISKS_AWAY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `x:real^3`] MOI_S4L_LOCAL_AV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_FGB_CROSSING_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (\y:real^3. d + y) (UNIONS s0)`; `UNIONS t:real^3->bool`;
                        `oo INTER ball(x:real^3,r)`] THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER; CENTRE_IN_BALL] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th)
    (ASSUME `dist(x:real^3,y) < r`)]) o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `r:real`)) (concl th))) THEN
  EQ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      is_binary "SUBSET" (concl th) &&
      not (can (find_term ((=) `oo:real^3->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      is_binary "SUBSET" (concl th) &&
      can (find_term ((=) `oo:real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER]]);;


(* ------------------------------------------------------------------------- *)
(* Part 10: the translated configuration.  moi_s4z_cfg collects the          *)
(* data after the generic translation: s0 triangulates frontier c0, V0 the  *)
(* finitely many vertices whose vertex balls meet s0 + d, TV v the sphere   *)
(* triangulations, every simplex of s0 + d in general position with every   *)
(* simplex of every TV v.  From it: the surface crossing at every trace     *)
(* point, the curve crossing at every rim point.                            *)
(* ------------------------------------------------------------------------- *)

let moi_s4z_cfg = new_definition
 `moi_s4z_cfg (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
              (ep:real^N->real) (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool)
              (s0:(real^3->bool)->bool) (d:real^3) (V0:real^N->bool)
              (TV:real^N->(real^3->bool)->bool) <=>
    moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
    FINITE s0 /\ combinatorial_manifold 2 s0 /\ FINITE V0 /\
    (!v. v IN V0 ==> {v} IN kk /\ moi_s4z_vtri tt kk f1 v (TV v)) /\
    (!v. {v} IN kk /\
         ~(IMAGE (\y. d + y) (UNIONS s0) INTER IMAGE f1 (moi_s34_vb tt kk v) = {})
         ==> v IN V0) /\
    (!A B v. A IN s0 /\ v IN V0 /\ B IN TV v
             ==> affine_gp_3 (IMAGE (\y. d + y) A) B)`;;

let MOI_S4Z_CFG_BASIC = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s0 d V0 TV.
     moi_s4z_cfg tt kk h ep f1 car s0 d V0 TV
     ==> moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
         FINITE s0 /\ combinatorial_manifold 2 s0 /\ FINITE V0`,
  SIMP_TAC[moi_s4z_cfg]);;

let MOI_S4Z_CFG_V = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s0 d V0 TV v.
     moi_s4z_cfg tt kk h ep f1 car s0 d V0 TV /\ v IN V0
     ==> {v} IN kk /\ moi_s4z_vtri tt kk f1 v (TV v) /\
         (!A B. A IN s0 /\ B IN TV v ==> affine_gp_3 (IMAGE (\y. d + y) A) B)`,
  REWRITE_TAC[moi_s4z_cfg] THEN MESON_TAC[]);;

let MOI_S4Z_CFG_IN_V0 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s0 d V0 TV v x.
     moi_s4z_cfg tt kk h ep f1 car s0 d V0 TV /\ {v} IN kk /\
     x IN IMAGE (\y. d + y) (UNIONS s0) /\ x IN IMAGE f1 (moi_s34_vb tt kk v)
     ==> v IN V0`,
  REWRITE_TAC[moi_s4z_cfg] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `{}:real^3->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[]);;

(* The surface crossing at every trace point. *)

let MOI_S4Z_CFG_TRACE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s0 d V0 TV x.
     moi_s4z_cfg tt kk h ep f1 car s0 d V0 TV /\
     x IN IMAGE (\y. d + y) (UNIONS s0) /\ x IN IMAGE f1 (moi_s34_bd tt kk)
     ==> pl_crossing_at (IMAGE (\y. d + y) (UNIONS s0)) (IMAGE f1 (moi_s34_bd tt kk)) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4Z_CFG_BASIC) THEN
  SUBGOAL_THEN `?v:real^N. {v} IN kk /\
                  x IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(fun th -> UNDISCH_TAC
      `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN V0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4Z_CFG_IN_V0 THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
      `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
      `car:(real^N->bool)->real^3->bool`; `s0:(real^3->bool)->bool`; `d:real^3`;
      `TV:real^N->(real^3->bool)->bool`; `x:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `s0:(real^3->bool)->bool`; `d:real^3`; `V0:real^N->bool`;
                 `TV:real^N->(real^3->bool)->bool`; `v:real^N`] MOI_S4Z_CFG_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `?w:real^N. {w} IN kk /\ ~(w = v) /\
                            x IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`; `w:real^N`;
                   `x:real^3`] MOI_S4L_AV_NO_OTHER) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^N) IN V0` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4Z_CFG_IN_V0 THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
        `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
        `car:(real^N->bool)->real^3->bool`; `s0:(real^3->bool)->bool`; `d:real^3`;
        `TV:real^N->(real^3->bool)->bool`; `x:real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`;
                   `s0:(real^3->bool)->bool`; `d:real^3`; `V0:real^N->bool`;
                   `TV:real^N->(real^3->bool)->bool`; `w:real^N`] MOI_S4Z_CFG_V) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`; `w:real^N`;
                   `(TV:real^N->(real^3->bool)->bool) v`;
                   `(TV:real^N->(real^3->bool)->bool) w`;
                   `s0:(real^3->bool)->bool`; `d:real^3`; `x:real^3`] MOI_S4Z_RIM_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC);
      SIMP_TAC[]];
    MATCH_MP_TAC MOI_S4Z_OFF_RIM THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`; `v:real^N`;
                          `(TV:real^N->(real^3->bool)->bool) v`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* The curve crossing at every rim point. *)

let MOI_S4Z_CFG_CURVE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s0 d V0 TV g x.
     moi_s4z_cfg tt kk h ep f1 car s0 d V0 TV /\ g IN moi_s34_simp kk (&1) /\
     x IN IMAGE (\y. d + y) (UNIONS s0) /\
     x IN IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
     ==> pl_curve_crossing_at (IMAGE f1 (moi_s34_bd tt kk))
           (IMAGE (\y. d + y) (UNIONS s0) INTER IMAGE f1 (moi_s34_bd tt kk))
           (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4Z_CFG_BASIC) THEN
  SUBGOAL_THEN `(g:real^N->bool) IN kk` ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^N->bool) IN moi_s34_simp kk (&1)` THEN
    SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
    MOI_S4L_EDGE_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `g:real^N->bool`)) THEN
  SUBGOAL_THEN
   `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[u,w]) INTER moi_s34_bd tt kk) =
    IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[INTER_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u) /\
                x IN IMAGE f1 (moi_s34_vb tt kk w)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N) IN V0 /\ (w:real^N) IN V0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S4Z_CFG_IN_V0 THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
      `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
      `car:(real^N->bool)->real^3->bool`; `s0:(real^3->bool)->bool`; `d:real^3`;
      `TV:real^N->(real^3->bool)->bool`; `x:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `s0:(real^3->bool)->bool`; `d:real^3`; `V0:real^N->bool`;
                 `TV:real^N->(real^3->bool)->bool`; `u:real^N`] MOI_S4Z_CFG_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `s0:(real^3->bool)->bool`; `d:real^3`; `V0:real^N->bool`;
                 `TV:real^N->(real^3->bool)->bool`; `w:real^N`] MOI_S4Z_CFG_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(w:real^N = u)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `u:real^N`; `w:real^N`; `(TV:real^N->(real^3->bool)->bool) u`;
                 `(TV:real^N->(real^3->bool)->bool) w`;
                 `s0:(real^3->bool)->bool`; `d:real^3`; `x:real^3`] MOI_S4Z_RIM_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC);
    SIMP_TAC[]]);;

(* A rim is a union of simplices of t_v, all of dimension at most 1. *)

let MOI_S4Z_RIM_UNION = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v w t x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     ~(w = v) /\ segment[v,w] IN kk /\ moi_s4z_vtri tt kk f1 v t /\
     x IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)
     ==> ?a. a IN t /\ x IN a /\
             a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                                moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`] MOI_S4Z_RIM_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4Z_VTRI_CLOSED) THEN
  SUBGOAL_THEN
   `?a1. a1 IN t /\ (x:real^3) IN a1 /\
         a1 SUBSET IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3)
                    (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)` MP_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                     (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
      MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> x IN s ==> x IN t`) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_s4z_vtri tt kk (f1:real^N->real^3) v t` THEN
    REWRITE_TAC[moi_s4z_vtri] THEN
    DISCH_THEN(MP_TAC o SPEC `segment[v:real^N,w]` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?b1. b1 IN t /\ (x:real^3) IN b1 /\
         b1 SUBSET IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3)
                    (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` MP_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                     (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
      MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> x IN s ==> x IN t`) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`;
                   `t:(real^3->bool)->bool`] MOI_S4Z_AV_UNION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `x:real^3`] MOI_FGB_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `a1:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(c:real^3->bool) SUBSET a1 /\ c SUBSET b1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f1:real^N->real^3)
      (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) =
    IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) INTER
    IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
   [EXISTS_TAC `a1:real^3->bool`; EXISTS_TAC `b1:real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4Z_RIM_SIMPLEX_DIM = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v w t a.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     ~(w = v) /\ segment[v,w] IN kk /\ moi_s4z_vtri tt kk f1 v t /\ a IN t /\
     a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)
     ==> aff_dim a <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4Z_VTRI_CLOSED) THEN
  SUBGOAL_THEN `combinatorial_manifold 2 (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4z_vtri tt kk (f1:real^N->real^3) v t` THEN
    SIMP_TAC[moi_s4z_vtri];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `a:real^3->bool`] MOI_FGB_CM2_DIM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `aff_dim (a:real^3->bool) = &2` THENL [ALL_TAC; ASM_INT_ARITH_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN `convex (a:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^3. z IN relative_interior a` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN
    DISCH_TAC THEN UNDISCH_TAC `aff_dim (a:real^3->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(a:real^3->bool) SUBSET IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`; `t:(real^3->bool)->bool`; `z:real^3`;
                 `a:real^3->bool`] MOI_S4Z_RIM_NOT_TRI) THEN
  ASM_REWRITE_TAC[]);;

(* The trace is the finite union of the convex sets (A + d) INTER a. *)

let MOI_S4Z_CFG_TRACE_UNIONS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s0 d V0 TV.
     moi_s4z_cfg tt kk h ep f1 car s0 d V0 TV
     ==> IMAGE (\y. d + y) (UNIONS s0) INTER IMAGE f1 (moi_s34_bd tt kk) =
         UNIONS {IMAGE (\y. d + y) A INTER a | A IN s0 /\ a IN UNIONS (IMAGE TV V0) /\
                                              a SUBSET IMAGE f1 (moi_s34_bd tt kk)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4Z_CFG_BASIC) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`A:real^3->bool`; `a:real^3->bool`] THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(A:real^3->bool) IN s0` THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `a:real^3->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET]]] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INTER] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?A. A IN s0 /\ (x:real^3) IN IMAGE (\y. d + y) A` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN IMAGE (\y. d + y) (UNIONS s0)` THEN
    REWRITE_TAC[IN_IMAGE; IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v:real^N. {v} IN kk /\
                  x IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(fun th -> UNDISCH_TAC
      `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN V0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4Z_CFG_IN_V0 THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
      `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
      `car:(real^N->bool)->real^3->bool`; `s0:(real^3->bool)->bool`; `d:real^3`;
      `TV:real^N->(real^3->bool)->bool`; `x:real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `s0:(real^3->bool)->bool`; `d:real^3`; `V0:real^N->bool`;
                 `TV:real^N->(real^3->bool)->bool`; `v:real^N`] MOI_S4Z_CFG_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?a. a IN (TV:real^N->(real^3->bool)->bool) v /\ (x:real^3) IN a /\
                    a SUBSET IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                   `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`;
                   `(TV:real^N->(real^3->bool)->bool) v`] MOI_S4Z_AV_UNION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `IMAGE (\y:real^3. d + y) A INTER a` THEN ASM_REWRITE_TAC[IN_INTER] THEN
  MAP_EVERY EXISTS_TAC [`A:real^3->bool`; `a:real^3->bool`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `(TV:real^N->(real^3->bool)->bool) v` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]);;

(* Finitely many pieces (A + d) INTER a with A IN s0, a a simplex of some TV v. *)

let MOI_S4Z_CFG_PIECES_FINITE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s0 d V0 TV.
     moi_s4z_cfg tt kk h ep f1 car s0 d V0 TV
     ==> FINITE {IMAGE (\y. d + y) A INTER a | A IN s0 /\ a IN UNIONS (IMAGE TV V0)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4Z_CFG_BASIC) THEN
  MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `A:real^3->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `s0:(real^3->bool)->bool`; `d:real^3`; `V0:real^N->bool`;
                 `TV:real^N->(real^3->bool)->bool`; `v:real^N`] MOI_S4Z_CFG_V) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S4Z_VTRI_CLOSED o CONJUNCT1 o CONJUNCT2) THEN
  SIMP_TAC[]);;

let MOI_S4Z_CFG_COMPONENTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s0 d V0 TV.
     moi_s4z_cfg tt kk h ep f1 car s0 d V0 TV
     ==> FINITE (components (IMAGE (\y. d + y) (UNIONS s0) INTER
                             IMAGE f1 (moi_s34_bd tt kk)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_S4Z_CFG_TRACE_UNIONS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4Z_CFG_BASIC) THEN
  MATCH_MP_TAC MOI_LTD_FINITE_COMPONENTS_UNIONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{IMAGE (\y:real^3. d + y) A INTER a | A IN s0 /\
                 a IN UNIONS (IMAGE (TV:real^N->(real^3->bool)->bool) V0)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4Z_CFG_PIECES_FINITE THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
        `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
        `car:(real^N->bool)->real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      SET_TAC[]];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`A:real^3->bool`; `a:real^3->bool`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_TRANSLATION THEN MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
      EXISTS_TAC `s0:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[combinatorial_manifold];
      UNDISCH_TAC `(a:real^3->bool) IN UNIONS (IMAGE (TV:real^N->(real^3->bool)->bool) V0)` THEN
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
        `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
        `car:(real^N->bool)->real^3->bool`; `s0:(real^3->bool)->bool`; `d:real^3`;
        `V0:real^N->bool`; `TV:real^N->(real^3->bool)->bool`; `v:real^N`] MOI_S4Z_CFG_V) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP MOI_S4Z_VTRI_CLOSED o CONJUNCT1 o CONJUNCT2) THEN
      STRIP_TAC THEN MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
      EXISTS_TAC `(TV:real^N->(real^3->bool)->bool) v` THEN ASM_REWRITE_TAC[]]]);;

(* s0 + d meets the rims in finitely many points. *)

let MOI_S4Z_CFG_RIMS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s0 d V0 TV.
     moi_s4z_cfg tt kk h ep f1 car s0 d V0 TV
     ==> FINITE (IMAGE (\y. d + y) (UNIONS s0) INTER moi_s34_rims tt kk f1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4Z_CFG_BASIC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `UNIONS {IMAGE (\y:real^3. d + y) A INTER a | A IN s0 /\
                      a IN UNIONS (IMAGE (TV:real^N->(real^3->bool)->bool) V0) /\
                      aff_dim a <= &1}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{IMAGE (\y:real^3. d + y) A INTER a | A IN s0 /\
                   a IN UNIONS (IMAGE (TV:real^N->(real^3->bool)->bool) V0)}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S4Z_CFG_PIECES_FINITE THEN
        MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
          `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
          `car:(real^N->bool)->real^3->bool`] THEN
        ASM_REWRITE_TAC[];
        SET_TAC[]];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`A:real^3->bool`; `a:real^3->bool`] THEN STRIP_TAC THEN
      UNDISCH_TAC `(a:real^3->bool) IN UNIONS (IMAGE (TV:real^N->(real^3->bool)->bool) V0)` THEN
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
        `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
        `car:(real^N->bool)->real^3->bool`; `s0:(real^3->bool)->bool`; `d:real^3`;
        `V0:real^N->bool`; `TV:real^N->(real^3->bool)->bool`; `v:real^N`] MOI_S4Z_CFG_V) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_S4Z_GP_FINITE THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[AFF_DIM_TRANSLATION_EQ] THEN
        MP_TAC(ISPECL [`s0:(real^3->bool)->bool`; `A:real^3->bool`] MOI_FGB_CM2_DIM) THEN
        ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INTER] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?A. A IN s0 /\ (x:real^3) IN IMAGE (\y. d + y) A` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN IMAGE (\y. d + y) (UNIONS s0)` THEN
    REWRITE_TAC[IN_IMAGE; IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?g. g IN moi_s34_simp kk (&1) /\
                    (x:real^3) IN IMAGE (f1:real^N->real^3)
                                    (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN moi_s34_rims tt kk (f1:real^N->real^3)` THEN
    REWRITE_TAC[moi_s34_rims; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->bool) IN kk` ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^N->bool) IN moi_s34_simp kk (&1)` THEN
    SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `g:real^N->bool`]
    MOI_S4L_EDGE_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `g:real^N->bool`)) THEN
  SUBGOAL_THEN
   `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[u,w]) INTER moi_s34_bd tt kk) =
    IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[INTER_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N) IN V0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4Z_CFG_IN_V0 THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
      `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
      `car:(real^N->bool)->real^3->bool`; `s0:(real^3->bool)->bool`; `d:real^3`;
      `TV:real^N->(real^3->bool)->bool`; `x:real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `s0:(real^3->bool)->bool`; `d:real^3`; `V0:real^N->bool`;
                 `TV:real^N->(real^3->bool)->bool`; `u:real^N`] MOI_S4Z_CFG_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(w:real^N = u)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `u:real^N`; `w:real^N`; `(TV:real^N->(real^3->bool)->bool) u`;
                 `x:real^3`] MOI_S4Z_RIM_UNION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
                 `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
                 `u:real^N`; `w:real^N`; `(TV:real^N->(real^3->bool)->bool) u`;
                 `a:real^3->bool`] MOI_S4Z_RIM_SIMPLEX_DIM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `IMAGE (\y:real^3. d + y) A INTER a` THEN ASM_REWRITE_TAC[IN_INTER] THEN
  MAP_EVERY EXISTS_TAC [`A:real^3->bool`; `a:real^3->bool`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
  EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Part 11: the theorem GP_BALL.  V0 = the vertices whose vertex balls       *)
(* meet w0 (finite by hypothesis), TV v their sphere triangulations         *)
(* (MOI_S4Z_VTRI_EXISTS), s0 a triangulation of frontier c0                 *)
(* (MOI_S4Z_BALL_TRI); one small generic translation d                       *)
(* (MOI_FGB_GENERIC_TRANSLATE, MOI_S4Z_MARGIN for k in interior c0 and c0   *)
(* in w0); c = d + c0 has frontier s0 + d, and the translated configuration  *)
(* gives the four conditions (Part 10).                                      *)
(* ------------------------------------------------------------------------- *)

let GP_BALL = prove
 (MOI_S4Z_GP_BALL,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `V0 = {v:real^N | {v} IN kk /\
                    ~(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) INTER w0 = {})}` THEN
  SUBGOAL_THEN
   `(!v:real^N. v IN V0 ==> {v} IN kk) /\
    (!v:real^N. {v} IN kk /\
                ~(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) INTER w0 = {})
                ==> v IN V0)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "V0" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?TV:real^N->(real^3->bool)->bool.
      !v. v IN V0 ==> moi_s4z_vtri tt kk (f1:real^N->real^3) v (TV v)`
  (X_CHOOSE_TAC `TV:real^N->(real^3->bool)->bool`) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S4Z_VTRI_EXISTS THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c0:real^3->bool`; `{}:(real^3->bool)->bool`] MOI_S4Z_BALL_TRI) THEN
  ASM_REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:(real^3->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  SUBGOAL_THEN `compact (c0:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN ASM_MESON_TAC[MOI_S4Z_PL_BALL_CELL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `interior c0:real^3->bool`] MOI_S4Z_MARGIN) THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e1"))) THEN
  MP_TAC(ISPECL [`c0:real^3->bool`; `w0:real^3->bool`] MOI_S4Z_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e2"))) THEN
  MP_TAC(ISPECL [`s0:(real^3->bool)->bool`;
                 `UNIONS (IMAGE (TV:real^N->(real^3->bool)->bool) V0)`;
                 `min e1 e2`] MOI_FGB_GENERIC_TRANSLATE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN; FINITE_UNIONS] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_s4z_vtri tt kk (f1:real^N->real^3) v
                    ((TV:real^N->(real^3->bool)->bool) v)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_S4Z_VTRI_CLOSED) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^3` (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "gp"))) THEN
  REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\x:real^3. d + x) c0 SUBSET w0` ASSUME_TAC THENL
   [USE_THEN "e2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4z_cfg tt kk h ep (f1:real^N->real^3) car s0 d V0 TV` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s4z_cfg] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN CONJ_TAC THEN
      FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC);
      X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `w0:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(IMAGE (\y:real^3. d + y) (UNIONS s0) INTER
                     IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v) = {})` THEN
      SUBGOAL_THEN `IMAGE (\y:real^3. d + y) (UNIONS s0) SUBSET w0` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `UNIONS s0:real^3->bool`)) THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (\x:real^3. d + x) c0` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
        SET_TAC[]];
      MAP_EVERY X_GEN_TAC [`A:real^3->bool`; `B:real^3->bool`; `v:real^N`] THEN
      STRIP_TAC THEN USE_THEN "gp" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
      EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\x:real^3. d + x) c0` THEN
  SUBGOAL_THEN `frontier (IMAGE (\x:real^3. d + x) c0) = IMAGE (\y. d + y) (UNIONS s0)`
  (fun th -> REWRITE_TAC[th; moi_s34_trace]) THENL
   [ASM_REWRITE_TAC[FRONTIER_TRANSLATION]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S4Z_TRANSLATE_PL_BALL] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INTERIOR_TRANSLATION] THEN
    USE_THEN "e1" (MP_TAC o SPEC `--d:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NORM_NEG]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN
    DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `--d + y:real^3` THEN ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_S4Z_CFG_TRACE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
      `car:(real^N->bool)->real^3->bool`; `V0:real^N->bool`;
      `TV:real^N->(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_S4Z_CFG_CURVE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
      `car:(real^N->bool)->real^3->bool`; `V0:real^N->bool`;
      `TV:real^N->(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4Z_CFG_COMPONENTS THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
      `car:(real^N->bool)->real^3->bool`; `V0:real^N->bool`;
      `TV:real^N->(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S4Z_CFG_RIMS THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
      `car:(real^N->bool)->real^3->bool`; `V0:real^N->bool`;
      `TV:real^N->(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* pc_moi_fnd_tubeh: foundations of the Moise PL core, the holed traces of  *)
(* the dual cells of a graph tube (Moise GTM 47, 33.1 Lemmas 12-13, p.236). *)
(* Main theorem (the statement term of pc_moi_fnd_stmt.ml):                  *)
(*   GRAPH_TUBE_HOLED_TRACE = MOI_FND_GRAPH_TUBE_HOLES: for a vertex v of   *)
(*   degree d + 1, C_v INTER Bd N is PL holed_disk_model d, the model       *)
(*   frontier going onto the rims of the splitting disks at v.              *)
(* Route: the boundary of the 3-cell C_v is a PL 2-sphere containing the     *)
(* d + 1 splitting disks, which are pairwise disjoint 2-cells; a PL          *)
(* 2-sphere minus d + 1 disjoint open 2-cells is the holed disk: one disk    *)
(* complement is a 2-cell (DISK_COMPLEMENT), pulled back to a triangle of    *)
(* the plane, where the planar holed-disk theorem applies. The planar        *)
(* theorem is the statement of MOI_FSB_PLANAR_HOLES (pc_moi_fnd_surfb); it   *)
(* enters as the one antecedent of MOI_FTH_HOLES_COND.                       *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_fnd_euler.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_s35_minc.ml";;
needs "src/pc_moi_fnd_surfb.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The planar holed-disk theorem: the statement of MOI_FSB_PLANAR_HOLES of   *)
(* pc_moi_fnd_surfb. It is the one antecedent of the lemmas below; the last  *)
(* section discharges it.                                                    *)
(* ------------------------------------------------------------------------- *)

let moi_fth_planar_holes =
 `!k (k0:real^2->bool) (s:num->real^2->bool).
     &2 simplex k0 /\
     (!i. i < k ==> pl_sphere 1 (s i) /\ s i UNION inside (s i) SUBSET interior k0) /\
     (!i j. i < k /\ j < k /\ ~(i = j)
            ==> DISJOINT (s i UNION inside (s i)) (s j UNION inside (s j)))
     ==> ?f g. pl_homeomorphism (holed_disk_model k,
                                 k0 DIFF UNIONS {inside (s i) | i < k}) (f,g) /\
               IMAGE f (frontier (holed_disk_model k)) =
               relative_frontier k0 UNION UNIONS {s i | i < k}`;;

(* ------------------------------------------------------------------------- *)
(* PL cells, spheres and restrictions.                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_FTH_PLH_RESTRICT = prove
 (`!(f:real^M->real^N) g s t s'.
     pl_homeomorphism (s,t) (f,g) /\ s' SUBSET s /\ pl_polyhedron s'
     ==> pl_homeomorphism (s',IMAGE f s') (f,g) /\ pl_polyhedron (IMAGE f s')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_map_on s' (f:real^M->real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN ASM_MESON_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (IMAGE (f:real^M->real^N) s')` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCD_PLH_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `t:real^N->bool`] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]);;

let MOI_FTH_CELL_POLY = prove
 (`!n (s:real^N->bool) b.
     pl_cell_with_boundary n s b /\ 1 <= n
     ==> pl_polyhedron s /\ pl_polyhedron b /\ b SUBSET s /\ compact s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `s = IMAGE (f:real^N->real^N) k` SUBST1_TAC THENL
   [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `b:real^N->bool`)) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `&n:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[INT_OF_NUM_LE]; STRIP_TAC] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^N->bool) /\ compact k /\ pl_polyhedron k`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
      REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `{k:real^N->bool}` THEN
      REWRITE_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[homeomorphism]]);;

(* The boundary of a PL (n + 1)-cell is a PL n-sphere. *)
let MOI_FTH_CELL_SPHERE = prove
 (`!n (s:real^N->bool) b. pl_cell_with_boundary (n + 1) s b ==> pl_sphere n b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary]) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[pl_sphere] THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `&(n + 1):int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `g:real^N->real^N`; `k:real^N->bool`;
                 `s:real^N->bool`; `relative_frontier k:real^N->bool`] MOI_FTH_PLH_RESTRICT) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
  ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED]);;

(* PL cells transport along PL homeomorphisms to a space with an n-simplex. *)
let MOI_FTH_CELL_TRANSPORT = prove
 (`!n (d:real^M->bool) j (e:real^N->bool) f g.
     pl_cell_with_boundary n d j /\ pl_homeomorphism (d,e) (f,g) /\
     (?k:real^N->bool. &n simplex k)
     ==> pl_cell_with_boundary n e (IMAGE f j)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `k2:real^N->bool`))) THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^M->bool` (X_CHOOSE_THEN `f1:real^M->real^M`
    (X_CHOOSE_THEN `g1:real^M->real^M` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k2:real^N->bool`; `k1:real^M->bool`; `&n:int`] MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^M` (X_CHOOSE_THEN `q:real^M->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_homeomorphism (k2,d) ((f1:real^M->real^M) o (p:real^N->real^M),
                                         (q:real^M->real^N) o (g1:real^M->real^M))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k1:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`k2:real^N->bool`; `(f:real^M->real^N) o (f1:real^M->real^M) o (p:real^N->real^M)`;
    `(q:real^M->real^N) o (g1:real^M->real^M) o (g:real^N->real^M)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`k2:real^N->bool`; `d:real^M->bool`; `e:real^N->bool`;
                   `(f1:real^M->real^M) o (p:real^N->real^M)`;
                   `(q:real^M->real^N) o (g1:real^M->real^M)`;
                   `f:real^M->real^N`; `g:real^N->real^M`] PL_HOMEOMORPHISM_COMPOSE) THEN
    ASM_REWRITE_TAC[o_ASSOC];
    REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN ASM_MESON_TAC[pl_homeomorphism; homeomorphism]]);;

(* The standard 3-simplex. *)
let MOI_FTH_STD_SIMPLEX3 = prove
 (`&3 simplex (convex hull {vec 0:real^3,basis 1,basis 2,basis 3})`,
  REWRITE_TAC[simplex] THEN
  EXISTS_TAC `{vec 0:real^3,basis 1,basis 2,basis 3}` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(INST_TYPE [`:3`,`:N`] AFFINE_INDEPENDENT_STDBASIS) THEN
    REWRITE_TAC[MOI_SS2_STD_SB];
    SUBGOAL_THEN `~(basis 1:real^3 = basis 2) /\ ~(basis 1:real^3 = basis 3) /\
                  ~(basis 2:real^3 = basis 3) /\ ~(vec 0:real^3 = basis 1) /\
                  ~(vec 0:real^3 = basis 2) /\ ~(vec 0:real^3 = basis 3)`
    STRIP_ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
      SIMP_TAC[BASIS_INJ_EQ; DIMINDEX_3; ARITH; BASIS_NONZERO];
      ALL_TAC] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV)]);;

(* In the plane, a 2-simplex minus its relative frontier is its interior. *)
let MOI_FTH_SIMPLEX2_INTERIOR = prove
 (`!k0:real^2->bool. &2 simplex k0 ==> interior k0 = k0 DIFF relative_frontier k0`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `affine hull (k0:real^2->bool) = (:real^2)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_2] THEN ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM RELATIVE_INTERIOR_INTERIOR; relative_frontier] THEN
  SUBGOAL_THEN `closure (k0:real^2->bool) = k0` SUBST1_TAC THENL
   [ASM_MESON_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPEC `k0:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set identities for images of indexed unions.                             *)
(* ------------------------------------------------------------------------- *)

let MOI_FTH_IMAGE_DIFF_UNIONS = prove
 (`!(f:A->B) g s t (a:num->A->bool) (b:num->B->bool) P.
     (!x. x IN s ==> g (f x) = x) /\ IMAGE f s = t /\ (!y. y IN t ==> f (g y) = y) /\
     (!i. P i ==> a i = IMAGE g (b i) /\ b i SUBSET t)
     ==> IMAGE f (s DIFF UNIONS {a i | P i}) = t DIFF UNIONS {b i | P i}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `y:B` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:B->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
    EXISTS_TAC `(a:num->A->bool) i` THEN CONJ_TAC THENL
     [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(a:num->A->bool) i = IMAGE g ((b:num->B->bool) i)` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:B` THEN ASM_MESON_TAC[];
    STRIP_TAC THEN EXISTS_TAC `(g:B->A) y` THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `IMAGE (f:A->B) s = t` THEN UNDISCH_TAC `(y:B) IN t` THEN
      UNDISCH_TAC `!x:A. x IN s ==> (g:B->A) (f x) = x` THEN SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `u:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
      EXISTS_TAC `(b:num->B->bool) i` THEN CONJ_TAC THENL
       [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(g:B->A) y IN IMAGE g ((b:num->B->bool) i)` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(z:B) IN t` ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `y:B = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[]]]);;

let MOI_FTH_IMAGE_UNIONS_IMAGE = prove
 (`!(f:A->B) g t (b:num->B->bool) P.
     (!y. y IN t ==> f (g y) = y) /\ (!i. P i ==> b i SUBSET t)
     ==> IMAGE f (UNIONS {IMAGE g (b i) | P i}) = UNIONS {b i | P i}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:B` THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `u:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)))) THEN
    EXISTS_TAC `(b:num->B->bool) i` THEN CONJ_TAC THENL
     [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:A) IN u` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC) THEN
    ASM_MESON_TAC[SUBSET];
    DISCH_THEN(X_CHOOSE_THEN `u:B->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `(g:B->A) y` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    EXISTS_TAC `IMAGE (g:B->A) ((b:num->B->bool) i)` THEN CONJ_TAC THENL
     [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[]]);;

let MOI_FTH_UNIONS_SHIFT = prove
 (`!(X:num->A->bool) d. UNIONS {X i | i <= d} = X 0 UNION UNIONS {X (i + 1) | i < d}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:A->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    ASM_CASES_TAC `i = 0` THENL
     [DISJ1_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISJ2_TAC THEN EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `i - 1` THEN
    SUBGOAL_THEN `i - 1 + 1 = i` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    STRIP_TAC THENL
     [EXISTS_TAC `(X:num->A->bool) 0` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `0` THEN REWRITE_TAC[LE_0];
      EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `i + 1` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The neighbours of a graph vertex and the disjointness of its splitting   *)
(* disks.                                                                    *)
(* ------------------------------------------------------------------------- *)

(* The d + 1 edges at v are the segments to an enumeration of the          *)
(* neighbours of v.                                                          *)
let MOI_FTH_NBRS = prove
 (`!(t:(real^N->bool)->bool) l v d.
     graph_in_complex t l /\ {v} IN l /\
     CARD {e | e IN l /\ aff_dim e = &1 /\ v IN e} = d + 1
     ==> ?w:num->real^N.
           (!i. i <= d ==> ~(w i = v) /\ segment[v,w i] IN l) /\
           (!i j. i <= d /\ j <= d /\ w i = w j ==> i = j) /\
           (!u. ~(u = v) /\ segment[v,u] IN l ==> ?i. i <= d /\ u = w i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) SUBSET t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{e | e IN l /\ aff_dim e = &1 /\ (v:real^N) IN e} =
    IMAGE (\u. segment[v,u]) {u | ~(u = v) /\ segment[v,u] IN l}`
  (LABEL_TAC "EV") THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `e:real^N->bool`; `v:real^N`]
        MOI_FTA_SIMPLEX_LE1) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[INT_LE_REFL] THEN CONJ_TAC THENL
         [ASM SET_TAC[];
          DISCH_THEN SUBST_ALL_TAC THEN
          UNDISCH_TAC `aff_dim {v:real^N} = &1` THEN REWRITE_TAC[AFF_DIM_SING] THEN
          INT_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(v:real^N = u)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {e | e IN l /\ aff_dim e = &1 /\ (v:real^N) IN e}` ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (t:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o last o CONJUNCTS) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{s | s IN t /\ ~(s INTER U = {})}:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{u | ~(u = v) /\ segment[v:real^N,u] IN l} HAS_SIZE (d + 1)` MP_TAC THENL
   [MP_TAC(ISPECL [`\u:real^N. segment[v,u]`; `{u | ~(u = v) /\ segment[v:real^N,u] IN l}`;
                   `d + 1`] HAS_SIZE_IMAGE_INJ_EQ) THEN
    ANTS_TAC THENL
     [BETA_TAC THEN REWRITE_TAC[IN_ELIM_THM; SEGMENT_EQ] THEN SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "EV" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[HAS_SIZE]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_INDEX) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->real^N` (CONJUNCTS_THEN2
    (LABEL_TAC "WIN") (LABEL_TAC "WUQ"))) THEN
  EXISTS_TAC `w:num->real^N` THEN
  SUBGOAL_THEN `!i. i <= d <=> i < d + 1` (fun th -> REWRITE_TAC[th]) THENL
   [ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "WIN" (fun th -> MP_TAC(MP (SPEC `i:num` th) (ASSUME `i < d + 1`))) THEN
    REWRITE_TAC[IN_ELIM_THM];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:num->real^N) i IN {u | ~(u = v) /\ segment[v,u] IN l}` ASSUME_TAC THENL
     [USE_THEN "WIN" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "WUQ" (fun th -> MP_TAC(MP (SPEC `(w:num->real^N) i` th)
      (ASSUME `(w:num->real^N) i IN {u | ~(u = v) /\ segment[v,u] IN l}`))) THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `u:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(u:real^N) IN {u | ~(u = v) /\ segment[v,u] IN l}` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    USE_THEN "WUQ" (fun th -> MP_TAC(MP (SPEC `u:real^N` th)
      (ASSUME `(u:real^N) IN {u | ~(u = v) /\ segment[v,u] IN l}`))) THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]]);;

(* An affine function vanishing on a set vanishes on its convex hull. *)
let MOI_FTH_LEVEL_ZERO = prove
 (`!(f:real^N->real) s.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     (!x. x IN s ==> f x = &0)
     ==> !x. x IN convex hull s ==> f x = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex hull s SUBSET {x:real^N | f x = &0}` MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
      REWRITE_TAC[convex; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `a:real`; `b:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `a = &1 - b` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    SET_TAC[]]);;

(* Two splitting disks at v are disjoint: in the level picture of THETA a  *)
(* common point lies in a face of the link without midpoints, where the    *)
(* level function vanishes.                                                  *)
let MOI_FTH_DISKS_DISJOINT = prove
 (`!(t:(real^N->bool)->bool) l v w w'.
     graph_in_complex t l /\ {v} IN l /\
     ~(w = v) /\ segment[v,w] IN l /\ ~(w' = v) /\ segment[v,w'] IN l /\ ~(w = w')
     ==> DISJOINT (derived_dual_cell t l v INTER derived_dual_cell t l w)
                  (derived_dual_cell t l v INTER derived_dual_cell t l w')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v:real^N = w) /\ ~(v = w')` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
    MOI_FTA_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
    MOI_FTA_THETA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `k:real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LEV"))))) THEN
  SUBGOAL_THEN `!x:real^N. x IN UNIONS {s | s IN barycentric_subdivision t /\ v IN s}
                           ==> (k:real^N->real^N) ((h:real^N->real^N) x) = x`
  ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`; `w:real^N`;
                 `h:real^N->real^N`; `k:real^N->real^N`] MOI_FTA_DISK_THETA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`; `w':real^N`;
                 `h:real^N->real^N`; `k:real^N->real^N`] MOI_FTA_DISK_THETA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(h:real^N->real^N) x IN IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l w) /\
    h x IN IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l w')`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `q':real^N->bool` STRIP_ASSUME_TAC))) THEN
  (* the simplex m of the star of v over q' and its level function *)
  UNDISCH_TAC `q' IN simplicial_link (barycentric_subdivision t) (v:real^N)` THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `m:real^N->bool` STRIP_ASSUME_TAC))) THEN
  USE_THEN "LEV" (MP_TAC o SPEC `m:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(q':real^N->bool) SUBSET m` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= (f:real^N->real) (h(x:real^N))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(h:real^N->real^N) x` o check (fun th ->
      is_forall(concl th) && is_iff(snd(dest_forall(concl th))) &&
      not (can (find_term (fun u -> is_const u && fst(dest_const u) = "derived_frontier"))
               (concl th)))) THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  (* the face r = q INTER q' of m has no vertex on the graph *)
  SUBGOAL_THEN `q IN barycentric_subdivision t /\ q' IN barycentric_subdivision (t:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `q IN simplicial_link (barycentric_subdivision t) (v:real^N)` THEN
      REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN SIMP_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q INTER q':real^N->bool) face_of q /\ (q INTER q') face_of q'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(q INTER q':real^N->bool) face_of m` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^N. a extreme_point_of (q INTER q') ==> f a = &0` ASSUME_TAC THENL
   [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^N) extreme_point_of m /\ a IN q /\ a IN q'` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`q INTER q':real^N->bool`; `m:real^N->bool`; `a:real^N`]
        EXTREME_POINT_OF_FACE) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((a:real^N) IN UNIONS l)` (fun th -> ASM_SIMP_TAC[th]) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`; `w':real^N`;
                   `m:real^N->bool`; `a:real^N`] MOI_FTA_MID_UNIQUE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [ASM_MESON_TAC[];
      ALL_TAC] THEN
    (* a is the midpoint of [v,w'], a vertex of q, which already has the     *)
    (* midpoint of [v,w]                                                     *)
    UNDISCH_TAC `q IN simplicial_link (barycentric_subdivision t) (v:real^N)` THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `m1:real^N->bool` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(a:real^N) extreme_point_of m1` ASSUME_TAC THENL
     [SUBGOAL_THEN `(a:real^N) extreme_point_of q` MP_TAC THENL
       [MP_TAC(ISPECL [`q INTER q':real^N->bool`; `q:real^N->bool`; `a:real^N`]
          EXTREME_POINT_OF_FACE) THEN ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`q:real^N->bool`; `m1:real^N->bool`; `a:real^N`]
        EXTREME_POINT_OF_FACE) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`; `w:real^N`;
                   `m1:real^N->bool`; `a:real^N`] MOI_FTA_MID_UNIQUE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(q:real^N->bool) SUBSET m1` MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [ASM_MESON_TAC[MIDPOINT_EQ_ENDPOINT];
      ASM_MESON_TAC[MOI_FTA_MIDPOINT_INJ]];
    ALL_TAC] THEN
  (* so the level function vanishes on q INTER q', which contains h x *)
  SUBGOAL_THEN `(f:real^N->real) (h(x:real^N)) = &0` MP_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real`; `{a:real^N | a extreme_point_of (q INTER q')}`]
      MOI_FTH_LEVEL_ZERO) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `q INTER q' = convex hull {a:real^N | a extreme_point_of (q INTER q')}`
    (fun th -> REWRITE_TAC[GSYM th]) THENL
     [MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
      SUBGOAL_THEN `?n. n simplex (q:real^N->bool)` (X_CHOOSE_TAC `nq:int`) THENL
       [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_CONVEX];
        MATCH_MP_TAC FACE_OF_IMP_COMPACT THEN EXISTS_TAC `q:real^N->bool` THEN
        ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]];
      ASM_REWRITE_TAC[IN_INTER]];
    UNDISCH_TAC `&1 / &2 <= (f:real^N->real) (h(x:real^N))` THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Disks with holes and spheres with holes, from the planar theorem.         *)
(* ------------------------------------------------------------------------- *)

let moi_fth_head_is s th =
  try fst(dest_const(fst(strip_comb(concl th)))) = s with Failure _ -> false;;

let MOI_FTH_USE lab tms =
  USE_THEN lab (fun th -> MP_TAC(SPECL tms th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC];;

(* A 2-cell pulled back to the standard triangle: a planar 2-cell in the    *)
(* interior, i.e. a filled PL circle.                                        *)
let MOI_FTH_PULLBACK_DISK = prove
 (`!(phi:real^2->real^N) psi k0 E J0 D J.
     &2 simplex k0 /\ pl_homeomorphism (k0,E) (phi,psi) /\
     IMAGE phi (relative_frontier k0) = J0 /\
     pl_cell_with_boundary 2 D J /\ D SUBSET E DIFF J0
     ==> IMAGE psi D = IMAGE psi J UNION inside (IMAGE psi J) /\
         pl_sphere 1 (IMAGE psi J) /\
         IMAGE psi D SUBSET interior k0 /\
         inside (IMAGE psi J) = IMAGE psi (D DIFF J)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (D:real^N->bool) /\ pl_polyhedron (J:real^N->bool) /\ J SUBSET D`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `D:real^N->bool`; `J:real^N->bool`] MOI_FTH_CELL_POLY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!x. x IN k0 ==> (psi:real^N->real^2) (phi x) = x) /\
                IMAGE (phi:real^2->real^N) k0 = E /\
                (!y. y IN E ==> phi (psi y) = y) /\ IMAGE psi E = k0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `pl_homeomorphism (k0,E) (phi:real^2->real^N,psi:real^N->real^2)`) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (E,k0) (psi:real^N->real^2,phi:real^2->real^N)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(D:real^N->bool) SUBSET E` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real^N->real^2`; `phi:real^2->real^N`; `E:real^N->bool`;
                 `k0:real^2->bool`; `D:real^N->bool`] MOI_FTH_PLH_RESTRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (IMAGE (psi:real^N->real^2) D) (IMAGE psi J)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTH_CELL_TRANSPORT THEN
    MAP_EVERY EXISTS_TAC [`D:real^N->bool`; `phi:real^2->real^N`] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `k0:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (psi:real^N->real^2) D`; `IMAGE (psi:real^N->real^2) J`]
    MOI_S5C_PLANE_CELL_FACTS) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (psi:real^N->real^2) D`; `IMAGE (psi:real^N->real^2) J`]
    MOI_S5C_PLANE_FILL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!x y. x IN D /\ y IN D /\ (psi:real^N->real^2) x = psi y ==> x = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN E /\ (y:real^N) IN E` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(D:real^N->bool) SUBSET E` THEN
      UNDISCH_TAC `(x:real^N) IN D` THEN UNDISCH_TAC `(y:real^N) IN D` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `E:real^N->bool`)) (concl th) &&
      can (find_term ((=) `phi:real^2->real^N`)) (concl th)
      then MP_TAC(CONJ (SPEC `x:real^N` th) (SPEC `y:real^N` th)) else failwith "no") THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(MATCH_MP MOI_FTH_SIMPLEX2_INTERIOR (ASSUME `&2 simplex (k0:real^2->bool)`)) THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN E /\ ~(y IN J0)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(D:real^N->bool) SUBSET E DIFF J0` THEN
      UNDISCH_TAC `(y:real^N) IN D` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (psi:real^N->real^2) E = k0` THEN
      UNDISCH_TAC `(y:real^N) IN E` THEN SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(phi:real^2->real^N) (psi (y:real^N)) IN J0` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `J0:real^N->bool`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(phi:real^2->real^N) (psi (y:real^N)) = y` SUBST1_TAC THENL
       [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
          can (find_term ((=) `E:real^N->bool`)) (concl th) &&
          can (find_term ((=) `phi:real^2->real^N`)) (concl th)
          then MATCH_MP_TAC th else failwith "no") THEN
        FIRST_ASSUM ACCEPT_TAC;
        ASM_REWRITE_TAC[]]];
    SUBGOAL_THEN `inside (IMAGE (psi:real^N->real^2) J) = IMAGE psi D DIFF IMAGE psi J`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `inside (IMAGE (psi:real^N->real^2) J)`)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_DIFF_INJ_ALT THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]]);;

let MOI_FTH_DISJOINT_IMAGE = prove
 (`!(f:A->B) s a b.
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     a SUBSET s /\ b SUBSET s /\ DISJOINT a b
     ==> DISJOINT (IMAGE f a) (IMAGE f b)`,
  SET_TAC[]);;

let MOI_FTH_LEFT_INV_INJ = prove
 (`!(f:A->B) g s.
     (!y. y IN s ==> g (f y) = y)
     ==> !x y. x IN s /\ y IN s /\ f x = f y ==> x = y`,
  MESON_TAC[]);;

let MOI_FTH_PLH_FACTS = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g.
     pl_homeomorphism (s,t) (f,g)
     ==> (!x. x IN s ==> g (f x) = x) /\ IMAGE f s = t /\
         (!y. y IN t ==> f (g y) = y) /\ IMAGE g t = s /\
         pl_map_on s f /\ pl_map_on t g`,
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SIMP_TAC[]);;

(* A PL 2-cell minus k disjoint open 2-cells inside it is holed_disk_model k. *)
let MOI_FTH_DISK_HOLES = prove
 (mk_imp(moi_fth_planar_holes,
  `!k (E:real^N->bool) J0 (D:num->real^N->bool) J.
     pl_cell_with_boundary 2 E J0 /\
     (!i. i < k ==> pl_cell_with_boundary 2 (D i) (J i) /\ D i SUBSET E DIFF J0) /\
     (!i j. i < k /\ j < k /\ ~(i = j) ==> DISJOINT (D i) (D j))
     ==> ?(f:real^2->real^N) g.
           pl_homeomorphism (holed_disk_model k,
                             E DIFF UNIONS {D i DIFF J i | i < k}) (f,g) /\
           IMAGE f (frontier (holed_disk_model k)) = J0 UNION UNIONS {J i | i < k}`),
  DISCH_THEN(LABEL_TAC "PH") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (LABEL_TAC "DJ") (LABEL_TAC "DD"))) THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^N->bool` (X_CHOOSE_THEN `f1:real^N->real^N`
    (X_CHOOSE_THEN `g1:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k1:real^N->bool`; `vec 0:real^2`; `basis 1:real^2`; `basis 2:real^2`]
    MOI_SS2_TRI_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SS2_STD_NONCOLLINEAR THEN
    REWRITE_TAC[DIMINDEX_2; LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `k0 = convex hull {vec 0:real^2,basis 1,basis 2}` THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^N` (X_CHOOSE_THEN `g2:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&2 simplex (k0:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "k0" THEN MATCH_MP_TAC MOI_SS2_STD_TRIANGLE THEN
    REWRITE_TAC[DIMINDEX_2; LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `phi = (f1:real^N->real^N) o (f2:real^2->real^N)` THEN
  ABBREV_TAC `psi = (g2:real^N->real^2) o (g1:real^N->real^N)` THEN
  SUBGOAL_THEN `pl_homeomorphism (k0,E) (phi:real^2->real^N,psi:real^N->real^2)`
  ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN EXPAND_TAC "psi" THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k1:real^N->bool` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (phi:real^2->real^N) (relative_frontier k0) = J0` ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `J0:real^N->bool`)) THEN
  SUBGOAL_THEN `(!x. x IN k0 ==> (psi:real^N->real^2) (phi x) = x) /\
                IMAGE (phi:real^2->real^N) k0 = E /\
                (!y. y IN E ==> phi (psi y) = y) /\ IMAGE psi E = k0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `pl_homeomorphism (k0,E) (phi:real^2->real^N,psi:real^N->real^2)`) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the pulled back disks *)
  SUBGOAL_THEN
   `!i. i < k
        ==> IMAGE (psi:real^N->real^2) ((D:num->real^N->bool) i) =
            IMAGE psi ((J:num->real^N->bool) i) UNION inside (IMAGE psi (J i)) /\
            pl_sphere 1 (IMAGE psi (J i)) /\
            IMAGE psi (D i) SUBSET interior k0 /\
            inside (IMAGE psi (J i)) = IMAGE psi (D i DIFF J i)`
  (LABEL_TAC "PB") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FTH_PULLBACK_DISK THEN
    MAP_EVERY EXISTS_TAC [`phi:real^2->real^N`; `E:real^N->bool`; `J0:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN MOI_FTH_USE "DJ" [`i:num`] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the planar theorem *)
  USE_THEN "PH" (MP_TAC o SPECL [`k:num`; `k0:real^2->bool`;
    `\i. IMAGE (psi:real^N->real^2) ((J:num->real^N->bool) i)`]) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MOI_FTH_USE "PB" [`i:num`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      MOI_FTH_USE "PB" [`i:num`] THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
      MOI_FTH_USE "PB" [`j:num`] THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
      MATCH_MP_TAC MOI_FTH_DISJOINT_IMAGE THEN EXISTS_TAC `E:real^N->bool` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FTH_LEFT_INV_INJ THEN EXISTS_TAC `phi:real^2->real^N` THEN
        FIRST_ASSUM ACCEPT_TAC;
        MOI_FTH_USE "DJ" [`i:num`] THEN SET_TAC[];
        MOI_FTH_USE "DJ" [`j:num`] THEN SET_TAC[];
        MOI_FTH_USE "DD" [`i:num`; `j:num`] THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `X = (k0:real^2->bool) DIFF
                  UNIONS {inside (IMAGE (psi:real^N->real^2) ((J:num->real^N->bool) i)) | i < k}` THEN
  DISCH_THEN(X_CHOOSE_THEN `F0:real^2->real^2` (X_CHOOSE_THEN `G0:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_polyhedron (X:real^2->bool) /\ X SUBSET k0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; EXPAND_TAC "X" THEN SET_TAC[]] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTH_PLH_FACTS o check (fun th ->
      moi_fth_head_is "pl_homeomorphism" th &&
      can (find_term ((=) `F0:real^2->real^2`)) (concl th))) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `IMAGE (F0:real^2->real^2) (holed_disk_model k)`)) THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FEU_EULER_COMPACT_PL_POLYHEDRON THEN
    EXISTS_TAC `&1 - &k` THEN REWRITE_TAC[MOI_FEU_EULER_HOLED_DISK_MODEL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^2->real^N`; `psi:real^N->real^2`; `k0:real^2->bool`;
                 `E:real^N->bool`; `X:real^2->bool`] MOI_FTH_PLH_RESTRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (phi:real^2->real^N) X =
                E DIFF UNIONS {(D:num->real^N->bool) i DIFF J i | i < k}`
  ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC MOI_FTH_IMAGE_DIFF_UNIONS THEN
    EXISTS_TAC `psi:real^N->real^2` THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MOI_FTH_USE "PB" [`i:num`] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 th))]) THEN
    MOI_FTH_USE "DJ" [`i:num`] THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(phi:real^2->real^N) o (F0:real^2->real^2)`;
                        `(G0:real^2->real^2) o (psi:real^N->real^2)`] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `IMAGE (phi:real^2->real^N) X`)) THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `X:real^2->bool` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[IMAGE_UNION] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MOI_FTH_IMAGE_UNIONS_IMAGE THEN EXISTS_TAC `E:real^N->bool` THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MOI_FTH_USE "DJ" [`i:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `(D:num->real^N->bool) i`; `(J:num->real^N->bool) i`]
    MOI_FTH_CELL_POLY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ASM SET_TAC[]]);;

(* A PL 2-sphere in real^3 minus d + 1 disjoint open 2-cells is            *)
(* holed_disk_model d: the complement of the first disk is a 2-cell.        *)
let MOI_FTH_SPHERE_HOLES_3 = prove
 (mk_imp(moi_fth_planar_holes,
  `!d (S:real^3->bool) (D:num->real^3->bool) J.
     pl_sphere 2 S /\
     (!i. i <= d ==> pl_cell_with_boundary 2 (D i) (J i) /\ D i SUBSET S) /\
     (!i j. i <= d /\ j <= d /\ ~(i = j) ==> DISJOINT (D i) (D j))
     ==> ?(f:real^2->real^3) g.
           pl_homeomorphism (holed_disk_model d,
                             S DIFF UNIONS {D i DIFF J i | i <= d}) (f,g) /\
           IMAGE f (frontier (holed_disk_model d)) = UNIONS {J i | i <= d}`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "DJ") (LABEL_TAC "DD"))) THEN
  SUBGOAL_THEN `!i. i <= d ==> (J:num->real^3->bool) i SUBSET D i` (LABEL_TAC "JD") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MOI_FTH_USE "DJ" [`i:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`2`; `(D:num->real^3->bool) i`; `(J:num->real^3->bool) i`]
      MOI_FTH_CELL_POLY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL
   [`d:num`; `(S DIFF (D:num->real^3->bool) 0) UNION (J:num->real^3->bool) 0`;
    `(J:num->real^3->bool) 0`; `\i. (D:num->real^3->bool) (i + 1)`;
    `\i. (J:num->real^3->bool) (i + 1)`] o
    MATCH_MP (INST_TYPE [`:3`,`:N`] MOI_FTH_DISK_HOLES)) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC DISK_COMPLEMENT THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "DJ" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_0] THEN SIMP_TAC[];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "DJ" (MP_TAC o SPEC `i + 1`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "DD" (MP_TAC o SPECL [`i + 1`; `0`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "JD" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_0] THEN
      ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      USE_THEN "DD" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `g:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`f:real^2->real^3`; `g:real^3->real^2`] THEN
  ONCE_REWRITE_TAC[MOI_FTH_UNIONS_SHIFT] THEN BETA_TAC THEN
  SUBGOAL_THEN
   `S DIFF ((D 0 DIFF J 0) UNION
            UNIONS {(D:num->real^3->bool) (i + 1) DIFF (J:num->real^3->bool) (i + 1) | i < d}) =
    ((S DIFF D 0) UNION J 0) DIFF UNIONS {D (i + 1) DIFF J (i + 1) | i < d}`
  SUBST1_TAC THENL
   [USE_THEN "JD" (MP_TAC o SPEC `0`) THEN USE_THEN "DJ" (MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[LE_0] THEN SET_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The same in real^N, transported through the boundary of a 3-simplex. *)
let MOI_FTH_SPHERE_HOLES = prove
 (mk_imp(moi_fth_planar_holes,
  `!d (S:real^N->bool) (D:num->real^N->bool) J.
     pl_sphere 2 S /\
     (!i. i <= d ==> pl_cell_with_boundary 2 (D i) (J i) /\ D i SUBSET S) /\
     (!i j. i <= d /\ j <= d /\ ~(i = j) ==> DISJOINT (D i) (D j))
     ==> ?(f:real^2->real^N) g.
           pl_homeomorphism (holed_disk_model d,
                             S DIFF UNIONS {D i DIFF J i | i <= d}) (f,g) /\
           IMAGE f (frontier (holed_disk_model d)) = UNIONS {J i | i <= d}`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (LABEL_TAC "DJ") (LABEL_TAC "DD"))) THEN
  REWRITE_TAC[pl_sphere; ARITH_RULE `2 + 1 = 3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `h1:real^N->real^N`
    (X_CHOOSE_THEN `h2:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `S3 = convex hull {vec 0:real^3,basis 1,basis 2,basis 3}` THEN
  SUBGOAL_THEN `&3 simplex (S3:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S3" THEN REWRITE_TAC[MOI_FTH_STD_SIMPLEX3]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S3:real^3->bool`; `k:real^N->bool`; `&3:int`] MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^N` (X_CHOOSE_THEN `q:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `chi = (h1:real^N->real^N) o (p:real^3->real^N)` THEN
  ABBREV_TAC `chi' = (q:real^N->real^3) o (h2:real^N->real^N)` THEN
  SUBGOAL_THEN `pl_homeomorphism (relative_frontier S3,S)
                                 (chi:real^3->real^N,chi':real^N->real^3)`
  ASSUME_TAC THENL
   [EXPAND_TAC "chi" THEN EXPAND_TAC "chi'" THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier k:real^N->bool` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(!x. x IN relative_frontier S3 ==> (chi':real^N->real^3) (chi x) = x) /\
                IMAGE (chi:real^3->real^N) (relative_frontier S3) = S /\
                (!y. y IN S ==> chi (chi' y) = y) /\ IMAGE chi' S = relative_frontier S3`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `pl_homeomorphism (relative_frontier S3,S)
                                    (chi:real^3->real^N,chi':real^N->real^3)`) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (S,relative_frontier S3)
                                 (chi':real^N->real^3,chi:real^3->real^N)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i <= d
        ==> pl_cell_with_boundary 2 (IMAGE (chi':real^N->real^3) ((D:num->real^N->bool) i))
                                    (IMAGE chi' ((J:num->real^N->bool) i)) /\
            IMAGE chi' (D i) SUBSET relative_frontier S3 /\
            J i SUBSET D i /\ D i SUBSET S`
  (LABEL_TAC "TD") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MOI_FTH_USE "DJ" [`i:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`2`; `(D:num->real^N->bool) i`; `(J:num->real^N->bool) i`]
      MOI_FTH_CELL_POLY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTH_CELL_TRANSPORT THEN
      MAP_EVERY EXISTS_TAC [`(D:num->real^N->bool) i`; `chi:real^3->real^N`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`chi':real^N->real^3`; `chi:real^3->real^N`; `S:real^N->bool`;
                       `relative_frontier S3:real^3->bool`; `(D:num->real^N->bool) i`]
          MOI_FTH_PLH_RESTRICT) THEN
        ASM_SIMP_TAC[];
        EXISTS_TAC `convex hull {vec 0:real^3,basis 1,basis 2}` THEN
        MATCH_MP_TAC MOI_SS2_STD_TRIANGLE THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FTH_SPHERE_HOLES_3) THEN
  DISCH_THEN(MP_TAC o SPECL [`d:num`; `relative_frontier S3:real^3->bool`;
     `\i. IMAGE (chi':real^N->real^3) ((D:num->real^N->bool) i)`;
     `\i. IMAGE (chi':real^N->real^3) ((J:num->real^N->bool) i)`]) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
      ASM_REWRITE_TAC[ARITH_RULE `2 + 1 = 3`];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "TD" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      MOI_FTH_USE "DD" [`i:num`; `j:num`] THEN
      MOI_FTH_USE "TD" [`i:num`] THEN MOI_FTH_USE "TD" [`j:num`] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  ABBREV_TAC `Z = relative_frontier S3 DIFF
                  UNIONS {IMAGE (chi':real^N->real^3) ((D:num->real^N->bool) i) DIFF
                          IMAGE chi' ((J:num->real^N->bool) i) | i <= d}` THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^2->real^3` (X_CHOOSE_THEN `g0:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_polyhedron (Z:real^3->bool) /\ Z SUBSET relative_frontier S3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; EXPAND_TAC "Z" THEN SET_TAC[]] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTH_PLH_FACTS o check (fun th ->
      moi_fth_head_is "pl_homeomorphism" th &&
      can (find_term ((=) `f0:real^2->real^3`)) (concl th))) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `IMAGE (f0:real^2->real^3) (holed_disk_model d)`)) THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FEU_EULER_COMPACT_PL_POLYHEDRON THEN
    EXISTS_TAC `&1 - &d` THEN REWRITE_TAC[MOI_FEU_EULER_HOLED_DISK_MODEL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`chi:real^3->real^N`; `chi':real^N->real^3`;
                 `relative_frontier S3:real^3->bool`; `S:real^N->bool`; `Z:real^3->bool`]
    MOI_FTH_PLH_RESTRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (chi:real^3->real^N) Z =
                S DIFF UNIONS {(D:num->real^N->bool) i DIFF J i | i <= d}`
  ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN MATCH_MP_TAC MOI_FTH_IMAGE_DIFF_UNIONS THEN
    EXISTS_TAC `chi':real^N->real^3` THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MOI_FTH_USE "TD" [`i:num`] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_DIFF; IN_IMAGE] THEN ASM_MESON_TAC[SUBSET];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(chi:real^3->real^N) o (f0:real^2->real^3)`;
                        `(g0:real^3->real^2) o (chi':real^N->real^3)`] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `IMAGE (chi:real^3->real^N) Z`)) THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `Z:real^3->bool` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FTH_IMAGE_UNIONS_IMAGE THEN EXISTS_TAC `S:real^N->bool` THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MOI_FTH_USE "TD" [`i:num`] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The holed trace of a dual cell, from the planar theorem.                  *)
(* ------------------------------------------------------------------------- *)

(* Unions over the neighbours of v as unions over their enumeration. *)
let MOI_FTH_NBR_UNIONS = prove
 (`!(l:(real^N->bool)->bool) v d (w:num->real^N) (X:real^N->real^N->bool).
     (!i. i <= d ==> ~(w i = v) /\ segment[v,w i] IN l) /\
     (!u. ~(u = v) /\ segment[v,u] IN l ==> ?i. i <= d /\ u = w i)
     ==> UNIONS {X u | u | ~(u = v) /\ segment[v,u] IN l} = UNIONS {X (w i) | i <= d}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term is_exists) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `i:num` THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `(w:num->real^N) i` THEN ASM_MESON_TAC[]]);;

let MOI_FTH_TRACE_IDENT = prove
 (`!(C:real^N->bool) F0 (D:num->real^N->bool) J d.
     (!i. i <= d ==> D i SUBSET C /\ J i = D i INTER F0)
     ==> ((C INTER F0) UNION UNIONS {D i | i <= d}) DIFF UNIONS {D i DIFF J i | i <= d} =
         C INTER F0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_DIFF; IN_UNION; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
  EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(D:num->real^N->bool) i DIFF J i` o
      REWRITE_RULE[NOT_EXISTS_THM] o check (is_neg o concl)) THEN
    SUBGOAL_THEN `?i'. i' <= d /\ (D:num->real^N->bool) i DIFF J i = D i' DIFF J i'`
    (fun th -> REWRITE_TAC[th]) THENL
     [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    STRIP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN F0` THEN SET_TAC[]]);;

let MOI_FTH_HOLES_COND = prove
 (mk_imp(moi_fth_planar_holes, MOI_FND_GRAPH_TUBE_HOLES),
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `v:real^N`; `d:num`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`; `d:num`]
    MOI_FTH_NBRS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->real^N` (CONJUNCTS_THEN2 (LABEL_TAC "W1")
    (CONJUNCTS_THEN2 (LABEL_TAC "W2") (LABEL_TAC "W3")))) THEN
  SUBGOAL_THEN
   `!X:real^N->real^N->bool.
      UNIONS {X u | u | ~(u = v) /\ segment[v,u] IN l} = UNIONS {X ((w:num->real^N) i) | i <= d}`
  (LABEL_TAC "IX") THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_FTH_NBR_UNIONS THEN
    USE_THEN "W1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "W3" ACCEPT_TAC;
    ALL_TAC] THEN
  (* the boundary sphere of the 3-cell C_v *)
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
    MOI_FTA_CELL3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "IX" (fun th -> REWRITE_TAC[BETA_RULE(ISPEC
    `\u:real^N. derived_dual_cell t l v INTER derived_dual_cell t l u` th)]) THEN
  DISCH_TAC THEN
  ABBREV_TAC `B = (derived_dual_cell t l v INTER derived_frontier t l) UNION
                  UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l ((w:num->real^N) i) |
                          i <= d}` THEN
  SUBGOAL_THEN `pl_sphere 2 (B:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTH_CELL_SPHERE THEN
    EXISTS_TAC `derived_dual_cell t l (v:real^N)` THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 + 1 = 3`];
    ALL_TAC] THEN
  (* the splitting disks *)
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FTH_SPHERE_HOLES) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`d:num`; `B:real^N->bool`;
    `\i. derived_dual_cell t l v INTER derived_dual_cell t l ((w:num->real^N) i)`;
    `\i. derived_dual_cell t l v INTER derived_dual_cell t l ((w:num->real^N) i) INTER
         derived_frontier t l`]) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MOI_FTH_USE "W1" [`i:num`] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FTA_CELL2 THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        EXPAND_TAC "B" THEN REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN DISJ2_TAC THEN
        EXISTS_TAC `derived_dual_cell t l v INTER derived_dual_cell t l ((w:num->real^N) i)` THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_FTH_DISKS_DISJOINT THEN
      MOI_FTH_USE "W1" [`i:num`] THEN MOI_FTH_USE "W1" [`j:num`] THEN
      REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN MOI_FTH_USE "W2" [`i:num`; `j:num`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`f:real^2->real^N`; `g:real^N->real^2`] THEN
  USE_THEN "IX" (fun th -> REWRITE_TAC[BETA_RULE(ISPEC
    `\u:real^N. derived_dual_cell t l v INTER derived_dual_cell t l u INTER
                derived_frontier t l` th)]) THEN
  MP_TAC(ISPECL [`derived_dual_cell t l (v:real^N)`; `derived_frontier t (l:(real^N->bool)->bool)`;
                 `\i. derived_dual_cell t l v INTER derived_dual_cell t l ((w:num->real^N) i)`;
                 `\i. derived_dual_cell t l v INTER derived_dual_cell t l ((w:num->real^N) i) INTER
                      derived_frontier t l`; `d:num`] MOI_FTH_TRACE_IDENT) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN CONJ_TAC THEN SET_TAC[];
    DISCH_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (moi_fth_head_is "pl_homeomorphism")) THEN
    EXPAND_TAC "B" THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `IMAGE (f:real^2->real^N) (frontier (holed_disk_model d))`)) THEN
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem. The planar holed-disk theorem is MOI_FSB_PLANAR_HOLES   *)
(* of pc_moi_fnd_surfb (the statement moi_fth_planar_holes).                 *)
(* ------------------------------------------------------------------------- *)

let MOI_FTH_PLANAR_HOLES = prove(moi_fth_planar_holes, ACCEPT_TAC MOI_FSB_PLANAR_HOLES);;

let GRAPH_TUBE_HOLED_TRACE = MP MOI_FTH_HOLES_COND MOI_FTH_PLANAR_HOLES;;


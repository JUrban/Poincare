needs "src/pc_moi_core_stmt.ml";;
needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_real.ml";;
needs "src/pc_moi_cone.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_cells: assembly of PL embeddings from labelled cell diagrams,      *)
(* MOISE_CELL_ASSEMBLY_STATEMENT of pc_moi_core_stmt.ml (Moise GTM 47, the  *)
(* final stages (1)-(7) of the proof of 34.1, pp.245-246; the last steps of  *)
(* 33.1, p.238, and of 35.1-35.2, pp.250-252).  The embedding is built       *)
(* skeleton by skeleton; over each cell it is the cone (Alexander)           *)
(* extension of its values on the boundary (Moise Sec 5, Problems 5.11-5.12, *)
(* p.45; here PL_HOMEOMORPHISM_CONE_EXTENSION of pc_moi_cone.ml).            *)
(* First: general PL facts and the extension over one cell.                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 1. PL maps on unions of locally finite families of closed sets.          *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_PL_MAP_ON_EMPTY = prove
 (`!f:real^M->real^N. pl_map_on {} f`,
  REWRITE_TAC[pl_map_on; NOT_IN_EMPTY]);;

let MOI_CEL_PL_MAP_ON_UNIONS_FINITE = prove
 (`!(c:(real^M->bool)->bool) (f:real^M->real^N).
     FINITE c /\ (!s. s IN c ==> closed s /\ pl_map_on s f)
     ==> pl_map_on (UNIONS c) f`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; MOI_CEL_PL_MAP_ON_EMPTY; IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`t:real^M->bool`; `c:(real^M->bool)->bool`] THEN
  STRIP_TAC THEN X_GEN_TAC `f:real^M->real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `closed (t:real^M->bool) /\ pl_map_on t (f:real^M->real^N)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (UNIONS c:real^M->bool) (f:real^M->real^N)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS c:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_UNION THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[] THEN
  SET_TAC[]);;

let MOI_CEL_PL_MAP_ON_UNIONS_LF = prove
 (`!(c:(real^M->bool)->bool) (f:real^M->real^N).
     (!s. s IN c ==> closed s /\ pl_map_on s f) /\
     (!x. x IN UNIONS c
          ==> ?w. open w /\ x IN w /\
                  FINITE {s | s IN c /\ ~(s INTER w = {})})
     ==> pl_map_on (UNIONS c) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[PL_MAP_ON_LOCAL] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `UNIONS c INTER w =
    UNIONS {s | s IN c /\ ~(s INTER w = {})} INTER (w:real^M->bool)`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_map_on (UNIONS {s | s IN c /\ ~(s INTER w = {})}:real^M->bool)
              (f:real^M->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CEL_PL_MAP_ON_UNIONS_FINITE THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
  EXISTS_TAC `UNIONS {s | s IN c /\ ~(s INTER w = {})}:real^M->bool` THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL]);;

(* The same for a labelled family, with local finiteness of the labels.      *)

let MOI_CEL_PL_MAP_ON_UNIONS_LF_INDEXED = prove
 (`!(a:L->real^M->bool) (P:L->bool) (f:real^M->real^N).
     (!l. P l ==> closed (a l) /\ pl_map_on (a l) f) /\
     (!x. x IN UNIONS {a l | P l}
          ==> ?w. open w /\ x IN w /\ FINITE {l | ~(a l INTER w = {})})
     ==> pl_map_on (UNIONS {a l | P l}) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_CEL_PL_MAP_ON_UNIONS_LF THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (a:L->real^M->bool) {l | ~(a l INTER w = {})}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. Restriction of PL homeomorphisms; relative frontiers of polytopes.    *)
(* ------------------------------------------------------------------------- *)

(* The same as MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER of pc_moi_comb.ml     *)
(* (with its proof), which this file does not load.                          *)

let MOI_CEL_PL_POLYHEDRON_RELATIVE_FRONTIER = prove
 (`!k:real^N->bool. polytope k ==> pl_polyhedron (relative_frontier k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{f:real^N->bool | f facet_of k}` THEN
  ASM_SIMP_TAC[FINITE_POLYTOPE_FACETS; IN_ELIM_THM;
               RELATIVE_FRONTIER_OF_POLYHEDRON; POLYTOPE_IMP_POLYHEDRON] THEN
  ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE; facet_of]);;

let MOI_CEL_PLH_RESTRICT = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g s'.
     pl_homeomorphism (s,t) (f,g) /\ s' SUBSET s /\ locally_polyhedral s'
     ==> pl_homeomorphism (s',IMAGE f s') (f,g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_CEL_PLH_SIMPLEX_RF = prove
 (`!n (k:real^M->bool) (s:real^N->bool) f g.
     &n simplex k /\ pl_homeomorphism (k,s) (f,g)
     ==> pl_homeomorphism (relative_frontier k,IMAGE f (relative_frontier k))
                          (f,g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CEL_PLH_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `s:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_CEL_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]]);;

(* ------------------------------------------------------------------------- *)
(* 3. Cells with boundary: compactness, and the extension over one cell.    *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_CELL_COMPACT = prove
 (`!n (s:real^N->bool) bs.
     pl_cell_with_boundary n s bs
     ==> compact s /\ compact bs /\ bs SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `compact (k:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[COMPACT_RELATIVE_FRONTIER_BOUNDED; COMPACT_IMP_BOUNDED] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM SET_TAC[]]);;

let MOI_CEL_CELL_EXTENSION = prove
 (`!n (s:real^N->bool) bs (t:real^M->bool) bt h h'.
     pl_cell_with_boundary n s bs /\ pl_cell_with_boundary n t bt /\
     pl_homeomorphism (bs,bt) (h,h')
     ==> ?f g. pl_homeomorphism (s,t) (f,g) /\ !x. x IN bs ==> f x = h x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `ks:real^N->bool` (X_CHOOSE_THEN `fs:real^N->real^N`
     (X_CHOOSE_THEN `gs:real^N->real^N` STRIP_ASSUME_TAC)))
   (CONJUNCTS_THEN2
   (X_CHOOSE_THEN `kt:real^M->bool` (X_CHOOSE_THEN `ft:real^M->real^M`
     (X_CHOOSE_THEN `gt:real^M->real^M` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_homeomorphism (relative_frontier ks,bs)
                  (fs:real^N->real^N,gs)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_CEL_PLH_SIMPLEX_RF THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `s:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (bt,relative_frontier kt)
                  (gt:real^M->real^M,ft)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_CEL_PLH_SIMPLEX_RF THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `t:real^M->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier ks,relative_frontier kt)
      ((gt:real^M->real^M) o (h:real^N->real^M) o (fs:real^N->real^N),
       ((gs:real^N->real^N) o (h':real^M->real^N)) o (ft:real^M->real^M))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `bt:real^M->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `bs:real^N->bool` THEN CONJ_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`ks:real^N->bool`; `kt:real^M->bool`; `n:num`;
    `(gt:real^M->real^M) o (h:real^N->real^M) o (fs:real^N->real^N)`;
    `((gs:real^N->real^N) o (h':real^M->real^N)) o (ft:real^M->real^M)`]
   PL_HOMEOMORPHISM_CONE_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^N->real^M` (X_CHOOSE_THEN
    `gg:real^M->real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(!x. x IN ks ==> (gs:real^N->real^N) (fs x) = x) /\
    (!x. x IN kt ==> (gt:real^M->real^M) (ft x) = x) /\
    IMAGE (h:real^N->real^M) bs = bt`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier ks SUBSET (ks:real^N->bool) /\
                relative_frontier kt SUBSET (kt:real^M->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
  EXISTS_TAC `(ft:real^M->real^M) o (ff:real^N->real^M) o (gs:real^N->real^N)`
  THEN
  EXISTS_TAC `((fs:real^N->real^N) o (gg:real^M->real^N)) o (gt:real^M->real^M)`
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `kt:real^M->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `ks:real^N->bool` THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `bs = IMAGE (fs:real^N->real^N) (relative_frontier ks)` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(gs:real^N->real^N) (fs y) = y` SUBST1_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(ff:real^N->real^M) y = gt ((h:real^N->real^M) (fs (y:real^N)))`
  SUBST1_TAC THENL [ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^M) (fs (y:real^N)) IN bt` MP_TAC THENL
   [UNDISCH_TAC `IMAGE (h:real^N->real^M) bs = bt` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^M` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_MESON_TAC[SUBSET]);;

(* ========================================================================= *)
(* The combinatorics of labelled cells (faces, injectivity of maps that are  *)
(* injective on each cell and respect the cells), the boundary of a cell as  *)
(* a PL homeomorphism, the gluing of the cone extensions over the cells of   *)
(* one dimension, the induction over the skeleta, and MOISE_CELL_ASSEMBLY.   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 1. Faces.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_INTER_FACES = prove
 (`!(a:L->real^N->bool) (face:L->L->bool).
     (!l m. a l INTER a m = UNIONS {a n | n | face l n /\ face m n})
     ==> !l m z. z IN a l /\ z IN a m ==> ?n. face l n /\ face m n /\ z IN a n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM IN_INTER] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_CEL_FACE_SUBSET = prove
 (`!(a:L->real^N->bool) (face:L->L->bool).
     (!l. face l l) /\
     (!l m. a l INTER a m = UNIONS {a n | n | face l n /\ face m n})
     ==> !l n. face l n ==> a n SUBSET a l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:L`; `n:L`]) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM; SUBSET] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. Small set facts.                                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_IMAGE_UNIONS = prove
 (`!(f:real^N->real^M) (a:L->real^N->bool) (b:L->real^M->bool) (P:L->bool).
     (!l. P l ==> IMAGE f (a l) = b l)
     ==> IMAGE f (UNIONS {a l | P l}) = UNIONS {b l | P l}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^M` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `l:L` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `l:L` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o C MATCH_MP (ASSUME `(P:L->bool) l`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `l:L` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(y:real^M) IN b (l:L)` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o C MATCH_MP (ASSUME `(P:L->bool) l`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]]);;

let MOI_CEL_INJ_SUBSET = prove
 (`!(f:real^N->real^M) s t.
     s SUBSET t /\ (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y)
     ==> (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)`,
  MESON_TAC[SUBSET]);;

let MOI_CEL_TRANSFER = prove
 (`!(s:real^N->bool) (f:real^N->real^M) g t.
     (!x. x IN s ==> g x = f x) /\
     pl_map_on s f /\ IMAGE f s = t /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
     ==> pl_map_on s g /\ IMAGE g s = t /\
         (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `f:real^N->real^M` THEN
    ASM_MESON_TAC[];
    UNDISCH_TAC `IMAGE (f:real^N->real^M) s = t` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. A map injective on each cell of a face-closed family and mapping each *)
(* cell onto its target is injective on the union (the targets meet in the *)
(* targets of the common faces).                                             *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_INJECTIVE_UNIONS = prove
 (`!(a:L->real^N->bool) (b:L->real^M->bool) (face:L->L->bool)
    (f:real^N->real^M) (P:L->bool).
     (!l. face l l) /\
     (!l m. a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l m. b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
     (!l n. P l /\ face l n ==> P n) /\
     (!l. P l ==> IMAGE f (a l) = b l /\
                  (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y))
     ==> !x y. x IN UNIONS {a l | P l} /\ y IN UNIONS {a l | P l} /\
               f x = f y
               ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:L->real^N->bool`; `face:L->L->bool`] MOI_CEL_FACE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`b:L->real^M->bool`; `face:L->L->bool`] MOI_CEL_INTER_FACES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:L` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:L` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(f:real^N->real^M) x IN b (l:L) /\ f x IN b (m:L)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE (f:real^N->real^M) (a (l:L)) = b l`
        (SUBST1_TAC o SYM) THENL [ASM_MESON_TAC[]; ALL_TAC];
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `IMAGE (f:real^N->real^M) (a (m:L)) = b m`
        (SUBST1_TAC o SYM) THENL [ASM_MESON_TAC[]; ALL_TAC]] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?n:L. (face:L->L->bool) l n /\ face m n /\
          (f:real^N->real^M) x IN (b:L->real^M->bool) n`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(P:L->bool) n` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^N. z IN a (n:L) /\ (f:real^N->real^M) z = f x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(f:real^N->real^M) x IN (b:L->real^M->bool) n` THEN
    SUBGOAL_THEN `IMAGE (f:real^N->real^M) (a (n:L)) = b n`
      (SUBST1_TAC o SYM) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN a (l:L) /\ z IN a (m:L)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `x:real^N = z /\ y = z` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 4. The boundary of a cell: a map with the induction hypothesis below the *)
(* dimension of the cell is a PL homeomorphism of the boundaries.            *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_BOUNDARY_PLH = prove
 (`!(a:L->real^N->bool) (b:L->real^3->bool) (d:L->num) (face:L->L->bool)
    (f:real^N->real^3) l.
     (!l. face l l) /\
     (!l m. face l m ==> m = l \/ d m < d l) /\
     (!l. pl_cell_with_boundary (d l) (a l)
             (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
     (!l m. a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l m. b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
     (!x. x IN UNIONS {a l | l IN (:L)}
          ==> ?w. open w /\ x IN w /\ FINITE {l | ~(a l INTER w = {})}) /\
     (!m. d m < d l
          ==> pl_map_on (a m) f /\ IMAGE f (a m) = b m /\
              (!x y. x IN a m /\ y IN a m /\ f x = f y ==> x = y))
     ==> ?g. pl_homeomorphism (UNIONS {a m | m | face l m /\ ~(m = l)},
                               UNIONS {b m | m | face l m /\ ~(m = l)})
                              (f,g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m:L. (face:L->L->bool) l m /\ ~(m = l) ==> (d:L->num) m < d l`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m:L. closed ((a:L->real^N->bool) m)` ASSUME_TAC THENL
   [X_GEN_TAC `m:L` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_CEL_CELL_COMPACT o SPEC `m:L`)
    THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_CEL_CELL_COMPACT o SPEC `l:L`) THEN
  SUBGOAL_THEN
   `pl_map_on (UNIONS {(a:L->real^N->bool) m | m |
                       (face:L->L->bool) l m /\ ~(m = l)})
              (f:real^N->real^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CEL_PL_MAP_ON_UNIONS_LF_INDEXED THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC
       `(x:real^N) IN UNIONS {(a:L->real^N->bool) m | m |
                              (face:L->L->bool) l m /\ ~(m = l)}` THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^N->real^3)
      (UNIONS {(a:L->real^N->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}) =
    UNIONS {(b:L->real^3->bool) m | m | face l m /\ ~(m = l)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CEL_IMAGE_UNIONS THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN UNIONS {(a:L->real^N->bool) m | m |
                       (face:L->L->bool) l m /\ ~(m = l)} /\
          y IN UNIONS {a m | m | face l m /\ ~(m = l)} /\
          (f:real^N->real^3) x = f y
          ==> x = y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CEL_INJ_SUBSET THEN
    EXISTS_TAC `UNIONS {(a:L->real^N->bool) m | (d:L->num) m < d l}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:L->real^N->bool`; `b:L->real^3->bool`; `face:L->L->bool`;
                   `f:real^N->real^3`; `\m:L. (d:L->num) m < d l`]
      MOI_CEL_INJECTIVE_UNIONS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[LT_TRANS];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`UNIONS {(a:L->real^N->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}`;
    `f:real^N->real^3`;
    `UNIONS {(b:L->real^3->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}`]
   HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^3->real^N` THEN
  DISCH_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. The extension over one cell: a PL embedding of the cell onto its       *)
(* target agreeing with the given map on the proper faces.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_EXTEND_ONE = prove
 (`!(a:L->real^N->bool) (b:L->real^3->bool) (d:L->num) (face:L->L->bool)
    (f:real^N->real^3) l.
     (!l. face l l) /\
     (!l m. face l m ==> m = l \/ d m < d l) /\
     (!l. pl_cell_with_boundary (d l) (a l)
             (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
     (!l. pl_cell_with_boundary (d l) (b l)
             (UNIONS {b m | m | face l m /\ ~(m = l)})) /\
     (!l m. a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l m. b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
     (!x. x IN UNIONS {a l | l IN (:L)}
          ==> ?w. open w /\ x IN w /\ FINITE {l | ~(a l INTER w = {})}) /\
     (!m. d m < d l
          ==> pl_map_on (a m) f /\ IMAGE f (a m) = b m /\
              (!x y. x IN a m /\ y IN a m /\ f x = f y ==> x = y))
     ==> ?g. pl_map_on (a l) g /\ IMAGE g (a l) = b l /\
             (!x y. x IN a l /\ y IN a l /\ g x = g y ==> x = y) /\
             (!n x. face l n /\ ~(n = l) /\ x IN a n ==> g x = f x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:L->real^N->bool`; `b:L->real^3->bool`; `d:L->num`;
                 `face:L->L->bool`; `f:real^N->real^3`; `l:L`]
    MOI_CEL_BOUNDARY_PLH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `g0:real^3->real^N`) THEN
  MP_TAC(ISPECL
   [`(d:L->num) l`; `(a:L->real^N->bool) l`;
    `UNIONS {(a:L->real^N->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}`;
    `(b:L->real^3->bool) l`;
    `UNIONS {(b:L->real^3->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}`;
    `f:real^N->real^3`; `g0:real^3->real^N`] MOI_CEL_CELL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^3` (X_CHOOSE_THEN
    `g':real^3->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `g:real^N->real^3` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o
    check (fun th -> rand(concl th) = `(g:real^N->real^3,g':real^3->real^N)`))
  THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 6. Gluing the extensions over the cells of dimension k.                  *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_GLUE_STEP = prove
 (`!(a:L->real^N->bool) (b:L->real^3->bool) (d:L->num) (face:L->L->bool) k
    (f:real^N->real^3) (ff:L->real^N->real^3).
     (!l m. face l m ==> m = l \/ d m < d l) /\
     (!l m. a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l. d l < k
          ==> pl_map_on (a l) f /\ IMAGE f (a l) = b l /\
              (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y)) /\
     (!l. d l = k
          ==> pl_map_on (a l) (ff l) /\ IMAGE (ff l) (a l) = b l /\
              (!x y. x IN a l /\ y IN a l /\ ff l x = ff l y ==> x = y) /\
              (!n x. face l n /\ ~(n = l) /\ x IN a n ==> ff l x = f x))
     ==> ?g:real^N->real^3.
           !l. d l < SUC k
               ==> pl_map_on (a l) g /\ IMAGE g (a l) = b l /\
                   (!x y. x IN a l /\ y IN a l /\ g x = g y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:L->real^N->bool`; `face:L->L->bool`] MOI_CEL_INTER_FACES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!l m x. (d:L->num) l = k /\ d m < k /\
            (x:real^N) IN (a:L->real^N->bool) l /\ x IN a m
            ==> (ff:L->real^N->real^3) l x = (f:real^N->real^3) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `?n:L. (face:L->L->bool) l n /\ face m n /\
            (x:real^N) IN (a:L->real^N->bool) n`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(n:L = l)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(l:L) = m \/ (d:L->num) l < d m` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      STRIP_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l l' x. (d:L->num) l = k /\ d l' = k /\
             (x:real^N) IN (a:L->real^N->bool) l /\ x IN a l'
             ==> (ff:L->real^N->real^3) l x = ff l' x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `l':L = l` THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?n:L. (face:L->L->bool) l n /\ face l' n /\
            (x:real^N) IN (a:L->real^N->bool) n`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(n:L = l) /\ ~(n = l')` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
       [SUBGOAL_THEN `(d:L->num) l < d l'` MP_TAC THENL
         [ASM_MESON_TAC[]; ASM_ARITH_TAC];
        SUBGOAL_THEN `(d:L->num) l' < d l` MP_TAC THENL
         [ASM_MESON_TAC[]; ASM_ARITH_TAC]];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?lab:real^N->L.
      !x. (?l. (d:L->num) l = k /\ x IN (a:L->real^N->bool) l)
          ==> d (lab x) = k /\ x IN a (lab x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?g:real^N->real^3.
      (!m x. (d:L->num) m < k /\ x IN (a:L->real^N->bool) m
             ==> g x = (f:real^N->real^3) x) /\
      (!l x. d l = k /\ x IN a l ==> g x = (ff:L->real^N->real^3) l x)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC
     `\x:real^N. if ?l:L. (d:L->num) l = k /\ x IN (a:L->real^N->bool) l
                 then (ff:L->real^N->real^3) (lab x) x
                 else (f:real^N->real^3) x` THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `g:real^N->real^3` THEN X_GEN_TAC `l:L` THEN
  REWRITE_TAC[LT] THEN STRIP_TAC THEN MATCH_MP_TAC MOI_CEL_TRANSFER THENL
   [EXISTS_TAC `(ff:L->real^N->real^3) l`;
    EXISTS_TAC `f:real^N->real^3`] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 7. The induction over the skeleta.                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_STEP = prove
 (`!(a:L->real^N->bool) (b:L->real^3->bool) (d:L->num) (face:L->L->bool) k.
     (!l. face l l) /\
     (!l m. face l m ==> m = l \/ d m < d l) /\
     (!l. pl_cell_with_boundary (d l) (a l)
             (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
     (!l. pl_cell_with_boundary (d l) (b l)
             (UNIONS {b m | m | face l m /\ ~(m = l)})) /\
     (!l m. a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l m. b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
     (!x. x IN UNIONS {a l | l IN (:L)}
          ==> ?w. open w /\ x IN w /\ FINITE {l | ~(a l INTER w = {})})
     ==> (?f:real^N->real^3.
            !l. d l < k
                ==> pl_map_on (a l) f /\ IMAGE f (a l) = b l /\
                    (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y))
         ==> (?f:real^N->real^3.
                !l. d l < SUC k
                    ==> pl_map_on (a l) f /\ IMAGE f (a l) = b l /\
                        (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `f:real^N->real^3`) THEN
  SUBGOAL_THEN
   `!l. ?g:real^N->real^3.
      (d:L->num) l = k
      ==> pl_map_on ((a:L->real^N->bool) l) g /\ IMAGE g (a l) = b l /\
          (!x y. x IN a l /\ y IN a l /\ g x = g y ==> x = y) /\
          (!n x. (face:L->L->bool) l n /\ ~(n = l) /\ x IN a n
                 ==> g x = (f:real^N->real^3) x)`
  MP_TAC THENL
   [X_GEN_TAC `l:L` THEN ASM_CASES_TAC `(d:L->num) l = k` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:L->real^N->bool`; `b:L->real^3->bool`; `d:L->num`;
                   `face:L->L->bool`; `f:real^N->real^3`; `l:L`]
      MOI_CEL_EXTEND_ONE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `ff:L->real^N->real^3`) THEN
  MP_TAC(ISPECL [`a:L->real^N->bool`; `b:L->real^3->bool`; `d:L->num`;
                 `face:L->L->bool`; `k:num`; `f:real^N->real^3`;
                 `ff:L->real^N->real^3`] MOI_CEL_GLUE_STEP) THEN
  ASM_REWRITE_TAC[]);;

let MOI_CEL_ALL_SKELETA = prove
 (`!(a:L->real^N->bool) (b:L->real^3->bool) (d:L->num) (face:L->L->bool).
     (!l. face l l) /\
     (!l m. face l m ==> m = l \/ d m < d l) /\
     (!l. pl_cell_with_boundary (d l) (a l)
             (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
     (!l. pl_cell_with_boundary (d l) (b l)
             (UNIONS {b m | m | face l m /\ ~(m = l)})) /\
     (!l m. a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l m. b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
     (!x. x IN UNIONS {a l | l IN (:L)}
          ==> ?w. open w /\ x IN w /\ FINITE {l | ~(a l INTER w = {})})
     ==> !k. ?f:real^N->real^3.
               !l. d l < k
                   ==> pl_map_on (a l) f /\ IMAGE f (a l) = b l /\
                       (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:L->real^N->bool`; `b:L->real^3->bool`; `d:L->num`;
                 `face:L->L->bool`; `k:num`] MOI_CEL_STEP) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 8. MOISE_CELL_ASSEMBLY.                                                   *)
(* ------------------------------------------------------------------------- *)

let MOISE_CELL_ASSEMBLY = prove
 (`!(i:L->bool) (u:N->bool). MOISE_CELL_ASSEMBLY_STATEMENT i u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOISE_CELL_ASSEMBLY_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`a:L->real^N->bool`; `b:L->real^3->bool`; `d:L->num`;
    `face:L->L->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`a:L->real^N->bool`; `b:L->real^3->bool`; `d:L->num`;
                 `face:L->L->bool`] MOI_CEL_ALL_SKELETA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `4`) THEN
  DISCH_THEN(X_CHOOSE_TAC `f:real^N->real^3`) THEN
  SUBGOAL_THEN
   `!l. pl_map_on ((a:L->real^N->bool) l) (f:real^N->real^3) /\
        IMAGE f (a l) = (b:L->real^3->bool) l /\
        (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:L` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[ARITH_RULE `n <= 3 ==> n < 4`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l:L. closed ((a:L->real^N->bool) l)` ASSUME_TAC THENL
   [X_GEN_TAC `l:L` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_CEL_CELL_COMPACT o
      check (fun th -> rand(rator(concl th)) = `(a:L->real^N->bool) l`) o
      SPEC `l:L`) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  EXISTS_TAC `f:real^N->real^3` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CEL_PL_MAP_ON_UNIONS_LF_INDEXED THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`a:L->real^N->bool`; `b:L->real^3->bool`;
                   `face:L->L->bool`; `f:real^N->real^3`; `\l:L. l IN (:L)`]
      MOI_CEL_INJECTIVE_UNIONS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The set form MOISE_CELL_ASSEMBLY_ON_STATEMENT of pc_moi_core_stmt.ml.     *)
(* The construction above with every label quantifier restricted to an       *)
(* explicit label set lab, which is closed under faces: the cells of lab of  *)
(* dimension below k are mapped correctly by one map, the cone extensions    *)
(* over the k-cells of lab are glued, and the final map is PL on the locally *)
(* finite union of the cells of lab and injective there.                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 1. PL maps on the union of a locally finite labelled family, with the    *)
(* local finiteness counted only over the labels in use.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_ON_PL_MAP_ON_UNIONS_LF_INDEXED = prove
 (`!(a:L->real^M->bool) (P:L->bool) (f:real^M->real^N).
     (!l. P l ==> closed (a l) /\ pl_map_on (a l) f) /\
     (!x. x IN UNIONS {a l | P l}
          ==> ?w. open w /\ x IN w /\ FINITE {l | P l /\ ~(a l INTER w = {})})
     ==> pl_map_on (UNIONS {a l | P l}) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_CEL_PL_MAP_ON_UNIONS_LF THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `IMAGE (a:L->real^M->bool) {l | (P:L->bool) l /\ ~(a l INTER w = {})}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. Faces within a label set.                                             *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_ON_INTER_FACES = prove
 (`!(lab:L->bool) (a:L->real^N->bool) (face:L->L->bool).
     (!l m. l IN lab /\ m IN lab
            ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n})
     ==> !l m z. l IN lab /\ m IN lab /\ z IN a l /\ z IN a m
                 ==> ?n. face l n /\ face m n /\ z IN a n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`l:L`; `m:L`; `z:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:L`; `m:L`]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;

let MOI_CEL_ON_FACE_SUBSET = prove
 (`!(lab:L->bool) (a:L->real^N->bool) (face:L->L->bool).
     (!l. l IN lab ==> face l l) /\
     (!l m. l IN lab /\ face l m ==> m IN lab) /\
     (!l m. l IN lab /\ m IN lab
            ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n})
     ==> !l n. l IN lab /\ face l n ==> a n SUBSET a l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "int"))) THEN
  MAP_EVERY X_GEN_TAC [`l:L`; `n:L`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(n:L) IN lab` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(face:L->L->bool) n n` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "int" (MP_TAC o SPECL [`l:L`; `n:L`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM; SUBSET] THEN
  UNDISCH_TAC `(face:L->L->bool) n n` THEN
  UNDISCH_TAC `(face:L->L->bool) l n` THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 3. Injectivity on the union of the cells of lab satisfying P.           *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_ON_INJECTIVE_UNIONS = prove
 (`!(lab:L->bool) (a:L->real^N->bool) (b:L->real^M->bool)
    (face:L->L->bool) (f:real^N->real^M) (P:L->bool).
     (!l. l IN lab ==> face l l) /\
     (!l m. l IN lab /\ face l m ==> m IN lab) /\
     (!l m. l IN lab /\ m IN lab
            ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l m. l IN lab /\ m IN lab
            ==> b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
     (!l n. l IN lab /\ P l /\ face l n ==> P n) /\
     (!l. l IN lab /\ P l
          ==> IMAGE f (a l) = b l /\
              (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y))
     ==> !x y. x IN UNIONS {a l | l IN lab /\ P l} /\
               y IN UNIONS {a l | l IN lab /\ P l} /\ f x = f y
               ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `face:L->L->bool`]
    MOI_CEL_ON_FACE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`lab:L->bool`; `b:L->real^M->bool`; `face:L->L->bool`]
    MOI_CEL_ON_INTER_FACES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:L` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:L` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(f:real^N->real^M) x IN b (l:L) /\ f x IN b (m:L)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE (f:real^N->real^M) (a (l:L)) = b l`
        (SUBST1_TAC o SYM) THENL [ASM_MESON_TAC[]; ALL_TAC];
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `IMAGE (f:real^N->real^M) (a (m:L)) = b m`
        (SUBST1_TAC o SYM) THENL [ASM_MESON_TAC[]; ALL_TAC]] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?n:L. (face:L->L->bool) l n /\ face m n /\
          (f:real^N->real^M) x IN (b:L->real^M->bool) n`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(n:L) IN lab /\ (P:L->bool) n` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^N. z IN a (n:L) /\ (f:real^N->real^M) z = f x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(f:real^N->real^M) x IN (b:L->real^M->bool) n` THEN
    SUBGOAL_THEN `IMAGE (f:real^N->real^M) (a (n:L)) = b n`
      (SUBST1_TAC o SYM) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN a (l:L) /\ z IN a (m:L)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `x:real^N = z /\ y = z` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 4. The boundary of a cell of lab is mapped PL homeomorphically by a map  *)
(* with the induction hypothesis below the dimension of the cell.           *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_ON_BOUNDARY_PLH = prove
 (`!(lab:L->bool) (a:L->real^N->bool) (b:L->real^3->bool) (d:L->num)
    (face:L->L->bool) (f:real^N->real^3) l.
     (!l. l IN lab ==> face l l) /\
     (!l m. l IN lab /\ face l m ==> m IN lab /\ (m = l \/ d m < d l)) /\
     (!l. l IN lab ==> pl_cell_with_boundary (d l) (a l)
                         (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
     (!l m. l IN lab /\ m IN lab
            ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l m. l IN lab /\ m IN lab
            ==> b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
     (!x. x IN UNIONS {a l | l IN lab}
          ==> ?w. open w /\ x IN w /\
                  FINITE {l | l IN lab /\ ~(a l INTER w = {})}) /\
     (!m. m IN lab /\ d m < d l
          ==> pl_map_on (a m) f /\ IMAGE f (a m) = b m /\
              (!x y. x IN a m /\ y IN a m /\ f x = f y ==> x = y)) /\
     l IN lab
     ==> ?g. pl_homeomorphism (UNIONS {a m | m | face l m /\ ~(m = l)},
                               UNIONS {b m | m | face l m /\ ~(m = l)})
                              (f,g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m:L. (face:L->L->bool) l m /\ ~(m = l)
                      ==> m IN lab /\ (d:L->num) m < d l`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m:L. m IN lab ==> closed ((a:L->real^N->bool) m)`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:L` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `pl_cell_with_boundary ((d:L->num) m) ((a:L->real^N->bool) m)
        (UNIONS {a n | n | (face:L->L->bool) m n /\ ~(n = m)})`
    (fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_CEL_CELL_COMPACT th)) THENL
     [ASM_MESON_TAC[]; ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary ((d:L->num) l) ((a:L->real^N->bool) l)
      (UNIONS {a m | m | (face:L->L->bool) l m /\ ~(m = l)})`
  (fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_CEL_CELL_COMPACT th)) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_map_on (UNIONS {(a:L->real^N->bool) m | m |
                       (face:L->L->bool) l m /\ ~(m = l)})
              (f:real^N->real^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CEL_ON_PL_MAP_ON_UNIONS_LF_INDEXED THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS {(a:L->real^N->bool) l | l IN lab}`
    (fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THENL
     [UNDISCH_TAC
       `(x:real^N) IN UNIONS {(a:L->real^N->bool) m | m |
                              (face:L->L->bool) l m /\ ~(m = l)}` THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{m:L | m IN lab /\ ~((a:L->real^N->bool) m INTER w = {})}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^N->real^3)
      (UNIONS {(a:L->real^N->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}) =
    UNIONS {(b:L->real^3->bool) m | m | face l m /\ ~(m = l)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CEL_IMAGE_UNIONS THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN UNIONS {(a:L->real^N->bool) m | m |
                       (face:L->L->bool) l m /\ ~(m = l)} /\
          y IN UNIONS {a m | m | face l m /\ ~(m = l)} /\
          (f:real^N->real^3) x = f y
          ==> x = y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CEL_INJ_SUBSET THEN
    EXISTS_TAC
     `UNIONS {(a:L->real^N->bool) m | m IN lab /\ (d:L->num) m < d l}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^3->bool`;
                   `face:L->L->bool`; `f:real^N->real^3`;
                   `\m:L. (d:L->num) m < d l`]
      MOI_CEL_ON_INJECTIVE_UNIONS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[LT_TRANS];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`UNIONS {(a:L->real^N->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}`;
    `f:real^N->real^3`;
    `UNIONS {(b:L->real^3->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}`]
   HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^3->real^N` THEN
  DISCH_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. The extension over one cell of lab.                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_ON_EXTEND_ONE = prove
 (`!(lab:L->bool) (a:L->real^N->bool) (b:L->real^3->bool) (d:L->num)
    (face:L->L->bool) (f:real^N->real^3) l.
     (!l. l IN lab ==> face l l) /\
     (!l m. l IN lab /\ face l m ==> m IN lab /\ (m = l \/ d m < d l)) /\
     (!l. l IN lab ==> pl_cell_with_boundary (d l) (a l)
                         (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
     (!l. l IN lab ==> pl_cell_with_boundary (d l) (b l)
                         (UNIONS {b m | m | face l m /\ ~(m = l)})) /\
     (!l m. l IN lab /\ m IN lab
            ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l m. l IN lab /\ m IN lab
            ==> b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
     (!x. x IN UNIONS {a l | l IN lab}
          ==> ?w. open w /\ x IN w /\
                  FINITE {l | l IN lab /\ ~(a l INTER w = {})}) /\
     (!m. m IN lab /\ d m < d l
          ==> pl_map_on (a m) f /\ IMAGE f (a m) = b m /\
              (!x y. x IN a m /\ y IN a m /\ f x = f y ==> x = y)) /\
     l IN lab
     ==> ?g. pl_map_on (a l) g /\ IMAGE g (a l) = b l /\
             (!x y. x IN a l /\ y IN a l /\ g x = g y ==> x = y) /\
             (!n x. face l n /\ ~(n = l) /\ x IN a n ==> g x = f x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^3->bool`;
                 `d:L->num`; `face:L->L->bool`; `f:real^N->real^3`; `l:L`]
    MOI_CEL_ON_BOUNDARY_PLH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `g0:real^3->real^N`) THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary ((d:L->num) l) ((a:L->real^N->bool) l)
      (UNIONS {a m | m | (face:L->L->bool) l m /\ ~(m = l)}) /\
    pl_cell_with_boundary (d l) ((b:L->real^3->bool) l)
      (UNIONS {b m | m | face l m /\ ~(m = l)})`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(d:L->num) l`; `(a:L->real^N->bool) l`;
    `UNIONS {(a:L->real^N->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}`;
    `(b:L->real^3->bool) l`;
    `UNIONS {(b:L->real^3->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}`;
    `f:real^N->real^3`; `g0:real^3->real^N`] MOI_CEL_CELL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^3` (X_CHOOSE_THEN
    `g':real^3->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `g:real^N->real^3` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o
    check (fun th -> rand(concl th) = `(g:real^N->real^3,g':real^3->real^N)`))
  THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 6. Gluing the extensions over the cells of lab of dimension k.           *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_ON_GLUE_STEP = prove
 (`!(lab:L->bool) (a:L->real^N->bool) (b:L->real^3->bool) (d:L->num)
    (face:L->L->bool) k (f:real^N->real^3) (ff:L->real^N->real^3).
     (!l m. l IN lab /\ face l m ==> m IN lab /\ (m = l \/ d m < d l)) /\
     (!l m. l IN lab /\ m IN lab
            ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l. l IN lab /\ d l < k
          ==> pl_map_on (a l) f /\ IMAGE f (a l) = b l /\
              (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y)) /\
     (!l. l IN lab /\ d l = k
          ==> pl_map_on (a l) (ff l) /\ IMAGE (ff l) (a l) = b l /\
              (!x y. x IN a l /\ y IN a l /\ ff l x = ff l y ==> x = y) /\
              (!n x. face l n /\ ~(n = l) /\ x IN a n ==> ff l x = f x))
     ==> ?g:real^N->real^3.
           !l. l IN lab /\ d l < SUC k
               ==> pl_map_on (a l) g /\ IMAGE g (a l) = b l /\
                   (!x y. x IN a l /\ y IN a l /\ g x = g y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `face:L->L->bool`]
    MOI_CEL_ON_INTER_FACES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!l m x. l IN lab /\ m IN lab /\ (d:L->num) l = k /\ d m < k /\
            (x:real^N) IN (a:L->real^N->bool) l /\ x IN a m
            ==> (ff:L->real^N->real^3) l x = (f:real^N->real^3) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `?n:L. (face:L->L->bool) l n /\ face m n /\
            (x:real^N) IN (a:L->real^N->bool) n`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(n:L = l)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(l:L) = m \/ (d:L->num) l < d m` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      STRIP_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l l' x. l IN lab /\ l' IN lab /\ (d:L->num) l = k /\ d l' = k /\
             (x:real^N) IN (a:L->real^N->bool) l /\ x IN a l'
             ==> (ff:L->real^N->real^3) l x = ff l' x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `l':L = l` THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?n:L. (face:L->L->bool) l n /\ face l' n /\
            (x:real^N) IN (a:L->real^N->bool) n`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(n:L = l) /\ ~(n = l')` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
       [SUBGOAL_THEN `(d:L->num) l < d l'` MP_TAC THENL
         [ASM_MESON_TAC[]; ASM_ARITH_TAC];
        SUBGOAL_THEN `(d:L->num) l' < d l` MP_TAC THENL
         [ASM_MESON_TAC[]; ASM_ARITH_TAC]];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?lb:real^N->L.
      !x. (?l. l IN lab /\ (d:L->num) l = k /\ x IN (a:L->real^N->bool) l)
          ==> lb x IN lab /\ d (lb x) = k /\ x IN a (lb x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?g:real^N->real^3.
      (!m x. m IN lab /\ (d:L->num) m < k /\ x IN (a:L->real^N->bool) m
             ==> g x = (f:real^N->real^3) x) /\
      (!l x. l IN lab /\ d l = k /\ x IN a l
             ==> g x = (ff:L->real^N->real^3) l x)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC
     `\x:real^N. if ?l:L. l IN lab /\ (d:L->num) l = k /\
                          x IN (a:L->real^N->bool) l
                 then (ff:L->real^N->real^3) ((lb:real^N->L) x) x
                 else (f:real^N->real^3) x` THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `g:real^N->real^3` THEN X_GEN_TAC `l:L` THEN
  REWRITE_TAC[LT] THEN STRIP_TAC THEN MATCH_MP_TAC MOI_CEL_TRANSFER THENL
   [EXISTS_TAC `(ff:L->real^N->real^3) l`;
    EXISTS_TAC `f:real^N->real^3`] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 7. The induction over the skeleta of lab.                                *)
(* ------------------------------------------------------------------------- *)

let MOI_CEL_ON_STEP = prove
 (`!(lab:L->bool) (a:L->real^N->bool) (b:L->real^3->bool) (d:L->num)
    (face:L->L->bool) k.
     (!l. l IN lab ==> face l l) /\
     (!l m. l IN lab /\ face l m ==> m IN lab /\ (m = l \/ d m < d l)) /\
     (!l. l IN lab ==> pl_cell_with_boundary (d l) (a l)
                         (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
     (!l. l IN lab ==> pl_cell_with_boundary (d l) (b l)
                         (UNIONS {b m | m | face l m /\ ~(m = l)})) /\
     (!l m. l IN lab /\ m IN lab
            ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l m. l IN lab /\ m IN lab
            ==> b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
     (!x. x IN UNIONS {a l | l IN lab}
          ==> ?w. open w /\ x IN w /\
                  FINITE {l | l IN lab /\ ~(a l INTER w = {})})
     ==> (?f:real^N->real^3.
            !l. l IN lab /\ d l < k
                ==> pl_map_on (a l) f /\ IMAGE f (a l) = b l /\
                    (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y))
         ==> (?f:real^N->real^3.
                !l. l IN lab /\ d l < SUC k
                    ==> pl_map_on (a l) f /\ IMAGE f (a l) = b l /\
                        (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `f:real^N->real^3`) THEN
  SUBGOAL_THEN
   `!l. ?g:real^N->real^3.
      l IN lab /\ (d:L->num) l = k
      ==> pl_map_on ((a:L->real^N->bool) l) g /\ IMAGE g (a l) = b l /\
          (!x y. x IN a l /\ y IN a l /\ g x = g y ==> x = y) /\
          (!n x. (face:L->L->bool) l n /\ ~(n = l) /\ x IN a n
                 ==> g x = (f:real^N->real^3) x)`
  MP_TAC THENL
   [X_GEN_TAC `l:L` THEN
    ASM_CASES_TAC `(l:L) IN lab` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(d:L->num) l = k` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^3->bool`;
                   `d:L->num`; `face:L->L->bool`; `f:real^N->real^3`; `l:L`]
      MOI_CEL_ON_EXTEND_ONE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `ff:L->real^N->real^3`) THEN
  MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^3->bool`;
                 `d:L->num`; `face:L->L->bool`; `k:num`; `f:real^N->real^3`;
                 `ff:L->real^N->real^3`] MOI_CEL_ON_GLUE_STEP) THEN
  ASM_REWRITE_TAC[]);;

let MOI_CEL_ON_ALL_SKELETA = prove
 (`!(lab:L->bool) (a:L->real^N->bool) (b:L->real^3->bool) (d:L->num)
    (face:L->L->bool).
     (!l. l IN lab ==> face l l) /\
     (!l m. l IN lab /\ face l m ==> m IN lab /\ (m = l \/ d m < d l)) /\
     (!l. l IN lab ==> pl_cell_with_boundary (d l) (a l)
                         (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
     (!l. l IN lab ==> pl_cell_with_boundary (d l) (b l)
                         (UNIONS {b m | m | face l m /\ ~(m = l)})) /\
     (!l m. l IN lab /\ m IN lab
            ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l m. l IN lab /\ m IN lab
            ==> b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
     (!x. x IN UNIONS {a l | l IN lab}
          ==> ?w. open w /\ x IN w /\
                  FINITE {l | l IN lab /\ ~(a l INTER w = {})})
     ==> !k. ?f:real^N->real^3.
               !l. l IN lab /\ d l < k
                   ==> pl_map_on (a l) f /\ IMAGE f (a l) = b l /\
                       (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^3->bool`;
                 `d:L->num`; `face:L->L->bool`; `k:num`] MOI_CEL_ON_STEP) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 8. MOISE_CELL_ASSEMBLY_ON (the set form).                                 *)
(* ------------------------------------------------------------------------- *)

let MOISE_CELL_ASSEMBLY_ON = prove
 (`!(i:L->bool) (u:N->bool). MOISE_CELL_ASSEMBLY_ON_STATEMENT i u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOISE_CELL_ASSEMBLY_ON_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^3->bool`; `d:L->num`;
    `face:L->L->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!l:L. l IN lab ==> (face:L->L->bool) l l` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^3->bool`;
                 `d:L->num`; `face:L->L->bool`] MOI_CEL_ON_ALL_SKELETA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `4`) THEN
  DISCH_THEN(X_CHOOSE_TAC `f:real^N->real^3`) THEN
  SUBGOAL_THEN
   `!l. l IN lab
        ==> pl_map_on ((a:L->real^N->bool) l) (f:real^N->real^3) /\
            IMAGE f (a l) = (b:L->real^3->bool) l /\
            (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:L` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[ARITH_RULE `n <= 3 ==> n < 4`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l:L. l IN lab ==> closed ((a:L->real^N->bool) l)`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:L` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `pl_cell_with_boundary ((d:L->num) l) ((a:L->real^N->bool) l)
        (UNIONS {a m | m | (face:L->L->bool) l m /\ ~(m = l)})`
    (fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_CEL_CELL_COMPACT th)) THENL
     [ASM_MESON_TAC[]; ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  EXISTS_TAC `f:real^N->real^3` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CEL_ON_PL_MAP_ON_UNIONS_LF_INDEXED THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; FIRST_ASSUM ACCEPT_TAC];
    MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^3->bool`;
                   `face:L->L->bool`; `f:real^N->real^3`; `\l:L. T`]
      MOI_CEL_ON_INJECTIVE_UNIONS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;


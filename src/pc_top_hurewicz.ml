(* ========================================================================= *)
(* pc_top_hurewicz: Hurewicz theorems in low degrees for general topological *)
(* spaces, HOL Light singular homology (homology.ml).                        *)
(*   Degree 1 (G7, ATOP_HUREWICZ1_STATEMENT): in a path-connected space      *)
(*   every class of H_1 is the class of one loop at a base point, and loops  *)
(*   null-homotopic rel endpoints give zero; with the class of a path as a   *)
(*   singular 1-simplex: additivity under concatenation and invariance under *)
(*   homotopy rel endpoints and under free homotopy of loops.                *)
(*   Degree 2 (G4, ATOP_HUREWICZ2_STATEMENT): in a simply connected space a  *)
(*   map of the 2-sphere that is zero on H_2 is null-homotopic.              *)
(* Depends on the library, pc_top_iface (statement constants), pc_top_cover *)
(* (paths in simply connected spaces) and pc_top_pi2 (pi_2 as a group, the  *)
(* homotopy addition theorem).                                               *)
(*                                                                           *)
(* The singular 1-simplex of a path, its faces and boundary,                *)
(* loops are cycles, constant simplices are boundaries.                      *)
(* ========================================================================= *)

needs "src/pc_top_iface.ml";;
needs "src/pc_top_cover.ml";;
needs "src/pc_top_pi2.ml";;

prioritize_real();;
type_invention_error := true;;

let path_simplex = new_definition
 `path_simplex (g:real->A) = RESTRICTION (standard_simplex 1) (\v:num->real. g(v 1))`;;

let STANDARD_SIMPLEX_1_COORD = prove
 (`!v. v IN standard_simplex 1 ==> &0 <= v 1 /\ v 1 <= &1 /\ v 0 = &1 - v 1`,
  GEN_TAC THEN REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CONTINUOUS_MAP_STANDARD_SIMPLEX_COORD = prove
 (`!p k. continuous_map (subtopology (product_topology (:num) (\i. euclideanreal))
                                     (standard_simplex p),euclideanreal) (\v. v k)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV]);;

let SINGULAR_SIMPLEX_PATH_SIMPLEX = prove
 (`!top g:real->A. path_in top g ==> singular_simplex (1,top) (path_simplex g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[singular_simplex; path_simplex] THEN
  REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
  SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; TOPSPACE_STANDARD_SIMPLEX; SUBSET_REFL] THEN
  SUBGOAL_THEN `(\v:num->real. (g:real->A)(v 1)) = g o (\v. v 1)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[path_in]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_STANDARD_SIMPLEX_COORD] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_STANDARD_SIMPLEX; IN_REAL_INTERVAL] THEN
  SIMP_TAC[STANDARD_SIMPLEX_1_COORD]);;

(* Points as singular 0-simplices.                                           *)

let SINGULAR_FACES_PATH_SIMPLEX = prove
 (`!g:real->A.
        singular_face 1 0 (path_simplex g) =
        RESTRICTION (standard_simplex 0) (\v. g(&1)) /\
        singular_face 1 1 (path_simplex g) =
        RESTRICTION (standard_simplex 0) (\v. g(&0))`,
  GEN_TAC THEN REWRITE_TAC[singular_face; ARITH_RULE `1 - 1 = 0`] THEN
  REWRITE_TAC[RESTRICTION_EXTENSION; STANDARD_SIMPLEX_0; IN_SING] THEN
  SIMP_TAC[o_THM; path_simplex; RESTRICTION] THEN
  CONJ_TAC THEN X_GEN_TAC `v:num->real` THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[simplicial_face] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC(MESON[] `P /\ x = y ==> (if P then (g:real->A) x else ARB) = g y`) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM(REWRITE_CONV[] `\i. if i = 0 then &1 else &0`)] THEN
  ONCE_REWRITE_TAC[GSYM BASIS_IN_STANDARD_SIMPLEX] THEN
  REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN TRY ASM_ARITH_TAC);;

let CHAIN_BOUNDARY_PATH_SIMPLEX = prove
 (`!g:real->A.
        chain_boundary 1 (frag_of (path_simplex g)) =
        frag_sub (frag_of (RESTRICTION (standard_simplex 0) (\v. g(&1))))
                 (frag_of (RESTRICTION (standard_simplex 0) (\v. g(&0))))`,
  GEN_TAC THEN REWRITE_TAC[CHAIN_BOUNDARY_OF] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NUMSEG_CONV `0..1`] THEN
  SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ; NEUTRAL_FRAG_ADD] THEN
  REWRITE_TAC[SINGULAR_FACES_PATH_SIMPLEX] THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC FRAG_MODULE);;

let SINGULAR_RELCYCLE_LOOP = prove
 (`!top (g:real->A).
      path_in top g /\ g(&0) = g(&1)
      ==> singular_relcycle (1,top,{})
            (frag_of (RESTRICTION (standard_simplex 1) (\v:num->real. g(v 1))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM path_simplex; SINGULAR_CYCLE] THEN
  ASM_SIMP_TAC[SINGULAR_CHAIN_OF; SINGULAR_SIMPLEX_PATH_SIMPLEX] THEN
  ASM_REWRITE_TAC[CHAIN_BOUNDARY_PATH_SIMPLEX; FRAG_MODULE `frag_sub x x:((num->real)->A)frag = frag_0`]);;

(* Constant simplices.                                                        *)

let SINGULAR_FACE_CONST = prove
 (`!p k a:A.
        1 <= p /\ k <= p
        ==> singular_face p k (RESTRICTION (standard_simplex p) (\v. a)) =
            RESTRICTION (standard_simplex (p - 1)) (\v. a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[singular_face; RESTRICTION_EXTENSION] THEN
  ASM_SIMP_TAC[o_THM; RESTRICTION; SIMPLICIAL_FACE_IN_STANDARD_SIMPLEX]);;

let CHAIN_BOUNDARY_CONST_2 = prove
 (`!a:A. chain_boundary 2 (frag_of (RESTRICTION (standard_simplex 2) (\v. a))) =
         frag_of (RESTRICTION (standard_simplex 1) (\v. a))`,
  GEN_TAC THEN REWRITE_TAC[CHAIN_BOUNDARY_OF] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NUMSEG_CONV `0..2`] THEN
  SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ; NEUTRAL_FRAG_ADD] THEN
  SIMP_TAC[SINGULAR_FACE_CONST; ARITH] THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC FRAG_MODULE);;

let SINGULAR_SIMPLEX_CONST = prove
 (`!p top a:A.
        a IN topspace top
        ==> singular_simplex (p,top) (RESTRICTION (standard_simplex p) (\v. a))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[singular_simplex] THEN
  REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
  SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; TOPSPACE_STANDARD_SIMPLEX; SUBSET_REFL] THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_CONST]);;

let SINGULAR_RELBOUNDARY_CONST_PATH = prove
 (`!top a:A.
        a IN topspace top
        ==> singular_relboundary (1,top,{}) (frag_of (path_simplex (\t. a)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SINGULAR_BOUNDARY; path_simplex] THEN
  EXISTS_TAC `frag_of (RESTRICTION (standard_simplex 2) (\v:num->real. a:A))` THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CHAIN_BOUNDARY_CONST_2] THEN
  ASM_SIMP_TAC[SINGULAR_CHAIN_OF; SINGULAR_SIMPLEX_CONST]);;

(* ========================================================================= *)
(* Group operations on homology classes; the class of a                     *)
(* concatenation of paths is the sum of the classes.                         *)
(* ========================================================================= *)

let RELATIVE_HOMOLOGY_GROUP_MUL_CLASS = prove
 (`!p top s (a:((num->real)->A)frag) b.
        group_mul (relative_homology_group(&p,top,s))
                  (homologous_rel (p,top,s) a) (homologous_rel (p,top,s) b) =
        homologous_rel (p,top,s) (frag_add a b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `c:((num->real)->A)frag` THEN
  REWRITE_TAC[IN] THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`c1:((num->real)->A)frag`; `c2:((num->real)->A)frag`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOLOGOUS_REL_ADD THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`frag_sub c (b:((num->real)->A)frag)`; `b:((num->real)->A)frag`] THEN
    REWRITE_TAC[HOMOLOGOUS_REL_REFL; FRAG_MODULE `frag_add (frag_sub c b) b:((num->real)->A)frag = c`] THEN
    UNDISCH_TAC `homologous_rel (p,top,s) (frag_add a b) (c:((num->real)->A)frag)` THEN
    REWRITE_TAC[homologous_rel] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    CONV_TAC FRAG_MODULE]);;

let RELATIVE_HOMOLOGY_GROUP_INV_CLASS = prove
 (`!p top s (a:((num->real)->A)frag).
        group_inv (relative_homology_group(&p,top,s)) (homologous_rel (p,top,s) a) =
        homologous_rel (p,top,s) (frag_neg a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `c:((num->real)->A)frag` THEN
  REWRITE_TAC[IN] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `d:((num->real)->A)frag` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homologous_rel (p,top,s) a (d:((num->real)->A)frag)` THEN
    REWRITE_TAC[homologous_rel] THEN
    DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [GSYM SINGULAR_RELBOUNDARY_NEG]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC FRAG_MODULE;
    DISCH_TAC THEN EXISTS_TAC `frag_neg c:((num->real)->A)frag` THEN
    REWRITE_TAC[FRAG_MODULE `frag_neg(frag_neg c):((num->real)->A)frag = c`] THEN
    UNDISCH_TAC `homologous_rel (p,top,s) (frag_neg a) (c:((num->real)->A)frag)` THEN
    REWRITE_TAC[homologous_rel] THEN
    DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [GSYM SINGULAR_RELBOUNDARY_NEG]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC FRAG_MODULE]);;

let SINGULAR_FACE_RESTRICTION = prove
 (`!p k (f:(num->real)->A).
        1 <= p /\ k <= p
        ==> singular_face p k (RESTRICTION (standard_simplex p) f) =
            RESTRICTION (standard_simplex (p - 1)) (f o simplicial_face k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[singular_face; RESTRICTION_EXTENSION] THEN
  ASM_SIMP_TAC[o_THM; RESTRICTION; SIMPLICIAL_FACE_IN_STANDARD_SIMPLEX]);;

let CHAIN_BOUNDARY_OF_2 = prove
 (`!f:(num->real)->A.
        chain_boundary 2 (frag_of f) =
        frag_add (frag_sub (frag_of (singular_face 2 0 f)) (frag_of (singular_face 2 1 f)))
                 (frag_of (singular_face 2 2 f))`,
  GEN_TAC THEN REWRITE_TAC[CHAIN_BOUNDARY_OF] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NUMSEG_CONV `0..2`] THEN
  SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ; NEUTRAL_FRAG_ADD] THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC FRAG_MODULE);;

let STANDARD_SIMPLEX_2_COORDS = prove
 (`!x. x IN standard_simplex 2
       ==> &0 <= x 0 /\ &0 <= x 1 /\ &0 <= x 2 /\ x 0 + x 1 + x 2 = &1`,
  GEN_TAC THEN REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[]);;

let SINGULAR_SIMPLEX_REAL_PARAM = prove
 (`!p top (g:real->A) phi.
        path_in top g /\
        continuous_map (subtopology (product_topology (:num) (\i. euclideanreal))
                                    (standard_simplex p),euclideanreal) phi /\
        (!x. x IN standard_simplex p ==> &0 <= phi x /\ phi x <= &1)
        ==> singular_simplex (p,top) (RESTRICTION (standard_simplex p) (g o phi))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[singular_simplex] THEN
  REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
  SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; TOPSPACE_STANDARD_SIMPLEX; SUBSET_REFL] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[path_in]) THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_STANDARD_SIMPLEX; IN_REAL_INTERVAL]);;

let HOMOLOGOUS_REL_JOINPATHS = prove
 (`!top (g:real->A) h.
      path_in top g /\ path_in top h /\ g(&1) = h(&0)
      ==> homologous_rel (1,top,{})
            (frag_of (RESTRICTION (standard_simplex 1)
               (\v:num->real. if v 1 <= &1 / &2 then g(&2 * v 1)
                              else h(&2 * v 1 - &1))))
            (frag_add (frag_of (RESTRICTION (standard_simplex 1)
                                            (\v:num->real. g(v 1))))
                      (frag_of (RESTRICTION (standard_simplex 1)
                                            (\v:num->real. h(v 1)))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `J = \t. if t <= &1 / &2 then (g:real->A)(&2 * t) else h(&2 * t - &1)` THEN
  SUBGOAL_THEN `path_in top (J:real->A)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN MATCH_MP_TAC TOPC_PATH_IN_JOIN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\v:num->real. if v 1 <= &1 / &2 then (g:real->A)(&2 * v 1) else h(&2 * v 1 - &1)) =
    (\v. J(v 1))` SUBST1_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `sig = RESTRICTION (standard_simplex 2)
                      ((J:real->A) o (\x:num->real. x 1 / &2 + x 2))` THEN
  SUBGOAL_THEN `singular_simplex (2,top) (sig:(num->real)->A)` ASSUME_TAC THENL
   [EXPAND_TAC "sig" THEN MATCH_MP_TAC SINGULAR_SIMPLEX_REAL_PARAM THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN CONJ_TAC THEN
      TRY(MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL) THEN
      REWRITE_TAC[real_div] THEN TRY(MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL) THEN
      REWRITE_TAC[CONTINUOUS_MAP_STANDARD_SIMPLEX_COORD];
      GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP STANDARD_SIMPLEX_2_COORDS) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `singular_face 2 0 (sig:(num->real)->A) = RESTRICTION (standard_simplex 1) (\v. h(v 1)) /\
    singular_face 2 1 sig = RESTRICTION (standard_simplex 1) (\v. J(v 1)) /\
    singular_face 2 2 sig = RESTRICTION (standard_simplex 1) (\v. g(v 1))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sig" THEN SIMP_TAC[SINGULAR_FACE_RESTRICTION; ARITH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[RESTRICTION_EXTENSION; o_THM] THEN
    REWRITE_TAC[simplicial_face] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `y:num->real` THEN
    DISCH_THEN(MP_TAC o MATCH_MP STANDARD_SIMPLEX_1_COORD) THEN STRIP_TAC THEN
    EXPAND_TAC "J" THEN ASM_REWRITE_TAC[] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    TRY(AP_TERM_TAC THEN ASM_REAL_ARITH_TAC) THEN
    TRY(MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC) THEN
    SUBGOAL_THEN `(y:num->real) 1 = &0` SUBST_ALL_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[homologous_rel; SINGULAR_BOUNDARY] THEN
  EXISTS_TAC `frag_neg (frag_of (sig:(num->real)->A))` THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[SINGULAR_CHAIN_NEG; SINGULAR_CHAIN_OF] THEN
  ASM_REWRITE_TAC[CHAIN_BOUNDARY_NEG; CHAIN_BOUNDARY_OF_2] THEN
  CONV_TAC FRAG_MODULE);;

let HOMOLOGY_GROUP_MUL_JOINPATHS = prove
 (`!top a (g:real->A) h.
      path_in top g /\ g(&0) = a /\ g(&1) = a /\
      path_in top h /\ h(&0) = a /\ h(&1) = a
      ==> group_mul (homology_group(&1,top))
            (homologous_rel (1,top,{})
               (frag_of (RESTRICTION (standard_simplex 1) (\v:num->real. g(v 1)))))
            (homologous_rel (1,top,{})
               (frag_of (RESTRICTION (standard_simplex 1) (\v:num->real. h(v 1))))) =
          homologous_rel (1,top,{})
            (frag_of (RESTRICTION (standard_simplex 1)
               (\v:num->real. if v 1 <= &1 / &2 then g(&2 * v 1)
                              else h(&2 * v 1 - &1))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[homology_group; RELATIVE_HOMOLOGY_GROUP_MUL_CLASS; HOMOLOGOUS_REL_EQ] THEN
  ONCE_REWRITE_TAC[HOMOLOGOUS_REL_SYM] THEN MATCH_MP_TAC HOMOLOGOUS_REL_JOINPATHS THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Homotopic paths (rel endpoints) and freely homotopic                      *)
(* loops have homologous 1-simplices.                                        *)
(* ========================================================================= *)

let SINGULAR_SIMPLEX_HOMOTOPY_PARAM = prove
 (`!p top (H:real#real->A) phi1 phi2.
        continuous_map (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                      (subtopology euclideanreal (real_interval[&0,&1])),
                        top) H /\
        continuous_map (subtopology (product_topology (:num) (\i. euclideanreal))
                                    (standard_simplex p),euclideanreal) phi1 /\
        continuous_map (subtopology (product_topology (:num) (\i. euclideanreal))
                                    (standard_simplex p),euclideanreal) phi2 /\
        (!x. x IN standard_simplex p
             ==> &0 <= phi1 x /\ phi1 x <= &1 /\ &0 <= phi2 x /\ phi2 x <= &1)
        ==> singular_simplex (p,top)
              (RESTRICTION (standard_simplex p) (\x. H(phi1 x,phi2 x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[singular_simplex] THEN
  REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
  SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; TOPSPACE_STANDARD_SIMPLEX; SUBSET_REFL] THEN
  SUBGOAL_THEN `(\x:num->real. (H:real#real->A)(phi1 x,phi2 x)) =
                H o (\x. phi1 x,phi2 x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                            (subtopology euclideanreal (real_interval[&0,&1]))` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX] THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_STANDARD_SIMPLEX; IN_REAL_INTERVAL]);;

(* The two triangles of the square [0,1] x [0,1] (homotopy parameter first). *)

let HOMOTOPY_TRIANGLES_LEMMA = prove
 (`!top (H:real#real->A).
        continuous_map (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                      (subtopology euclideanreal (real_interval[&0,&1])),
                        top) H
        ==> singular_relboundary (1,top,{})
              (frag_sub
                (frag_add (frag_of (path_simplex (\t. H(t,&1))))
                          (frag_of (path_simplex (\t. H(&0,t)))))
                (frag_add (frag_of (path_simplex (\t. H(&1,t))))
                          (frag_of (path_simplex (\t. H(t,&0))))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SINGULAR_BOUNDARY] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `s1 = RESTRICTION (standard_simplex 2)
                     (\x:num->real. (H:real#real->A)(x 2,x 1 + x 2))` THEN
  ABBREV_TAC `s2 = RESTRICTION (standard_simplex 2)
                     (\x:num->real. (H:real#real->A)(x 1 + x 2,x 2))` THEN
  EXISTS_TAC `frag_sub (frag_of (s1:(num->real)->A)) (frag_of s2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SINGULAR_CHAIN_SUB THEN REWRITE_TAC[SINGULAR_CHAIN_OF] THEN
    CONJ_TAC THEN MAP_EVERY EXPAND_TAC ["s1"; "s2"] THEN
    MATCH_MP_TAC SINGULAR_SIMPLEX_HOMOTOPY_PARAM THEN ASM_REWRITE_TAC[] THEN
    (REPEAT CONJ_TAC THENL
      [TRY(MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN CONJ_TAC) THEN
       REWRITE_TAC[CONTINUOUS_MAP_STANDARD_SIMPLEX_COORD];
       TRY(MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN CONJ_TAC) THEN
       REWRITE_TAC[CONTINUOUS_MAP_STANDARD_SIMPLEX_COORD];
       GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP STANDARD_SIMPLEX_2_COORDS) THEN
       REAL_ARITH_TAC]);
    ALL_TAC] THEN
  REWRITE_TAC[CHAIN_BOUNDARY_SUB; CHAIN_BOUNDARY_OF_2] THEN
  MAP_EVERY EXPAND_TAC ["s1"; "s2"] THEN
  SIMP_TAC[SINGULAR_FACE_RESTRICTION; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `RESTRICTION (standard_simplex 1)
      ((\x:num->real. (H:real#real->A)(x 2,x 1 + x 2)) o simplicial_face 0) =
    path_simplex (\t. H(t,&1)) /\
    RESTRICTION (standard_simplex 1)
      ((\x:num->real. (H:real#real->A)(x 2,x 1 + x 2)) o simplicial_face 1) =
    path_simplex (\t. H(t,t)) /\
    RESTRICTION (standard_simplex 1)
      ((\x:num->real. (H:real#real->A)(x 2,x 1 + x 2)) o simplicial_face 2) =
    path_simplex (\t. H(&0,t)) /\
    RESTRICTION (standard_simplex 1)
      ((\x:num->real. (H:real#real->A)(x 1 + x 2,x 2)) o simplicial_face 0) =
    path_simplex (\t. H(&1,t)) /\
    RESTRICTION (standard_simplex 1)
      ((\x:num->real. (H:real#real->A)(x 1 + x 2,x 2)) o simplicial_face 1) =
    path_simplex (\t. H(t,t)) /\
    RESTRICTION (standard_simplex 1)
      ((\x:num->real. (H:real#real->A)(x 1 + x 2,x 2)) o simplicial_face 2) =
    path_simplex (\t. H(t,&0))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[path_simplex; RESTRICTION_EXTENSION; o_THM; simplicial_face] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `y:num->real` THEN
    DISCH_THEN(MP_TAC o MATCH_MP STANDARD_SIMPLEX_1_COORD) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    REAL_ARITH_TAC;
    CONV_TAC FRAG_MODULE]);;

let PATH_SIMPLEX_EQ = prove
 (`!g h:real->A.
        (!t. &0 <= t /\ t <= &1 ==> g t = h t) ==> path_simplex g = path_simplex h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[path_simplex; RESTRICTION_EXTENSION] THEN
  X_GEN_TAC `y:num->real` THEN DISCH_THEN(MP_TAC o MATCH_MP STANDARD_SIMPLEX_1_COORD) THEN
  ASM_SIMP_TAC[]);;

let HOMOLOGOUS_REL_HOMOTOPIC_PATHS = prove
 (`!top (g:real->A) h.
      homotopic_with (\k. k(&0) = g(&0) /\ k(&1) = g(&1))
                     (subtopology euclideanreal (real_interval[&0,&1]),top) g h
      ==> homologous_rel (1,top,{})
            (frag_of (RESTRICTION (standard_simplex 1) (\v:num->real. g(v 1))))
            (frag_of (RESTRICTION (standard_simplex 1) (\v:num->real. h(v 1))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(g:real->A)(&0) IN topspace top /\ g(&1) IN topspace top`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC TOPC_PATH_IN_TOPSPACE THEN
    ASM_REWRITE_TAC[path_in; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_with]) THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real#real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `H:real#real->A`] HOMOTOPY_TRIANGLES_LEMMA) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  SUBGOAL_THEN
   `path_simplex (\t. (H:real#real->A)(t,&1)) = path_simplex (\t. g(&1)) /\
    path_simplex (\t. (H:real#real->A)(t,&0)) = path_simplex (\t. g(&0))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC PATH_SIMPLEX_EQ THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "T") THEN REWRITE_TAC[GSYM path_simplex; homologous_rel] THEN
  MP_TAC(ISPECL [`top:A topology`; `(g:real->A)(&0)`] SINGULAR_RELBOUNDARY_CONST_PATH) THEN
  MP_TAC(ISPECL [`top:A topology`; `(g:real->A)(&1)`] SINGULAR_RELBOUNDARY_CONST_PATH) THEN
  ASM_REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SINGULAR_RELBOUNDARY_SUB) THEN
  REMOVE_THEN "T" MP_TAC THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SINGULAR_RELBOUNDARY_SUB) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC FRAG_MODULE);;

let HOMOLOGOUS_REL_HOMOTOPIC_LOOPS = prove
 (`!top (g:real->A) h.
      homotopic_with (\k. k(&0) = k(&1))
                     (subtopology euclideanreal (real_interval[&0,&1]),top) g h
      ==> homologous_rel (1,top,{})
            (frag_of (RESTRICTION (standard_simplex 1) (\v:num->real. g(v 1))))
            (frag_of (RESTRICTION (standard_simplex 1) (\v:num->real. h(v 1))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real#real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `H:real#real->A`] HOMOTOPY_TRIANGLES_LEMMA) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  SUBGOAL_THEN
   `path_simplex (\t. (H:real#real->A)(t,&1)) = path_simplex (\t. H(t,&0))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC PATH_SIMPLEX_EQ THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM path_simplex; homologous_rel] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC FRAG_MODULE);;

(* ========================================================================= *)
(* Hurewicz in degree 1 (G7): every class of H_1 of a                       *)
(* path-connected space is the class of a loop at a given base point.       *)
(* ========================================================================= *)

let simplex_path = new_definition
 `simplex_path (f:(num->real)->A) =
    \s. f(\i. if i = 0 then &1 - s else if i = 1 then s else &0)`;;

let SIMPLEX_PATH_POINT_IN = prove
 (`!s. &0 <= s /\ s <= &1
       ==> (\i. if i = 0 then &1 - s else if i = 1 then s else &0) IN standard_simplex 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `1 < i ==> ~(i = 0) /\ ~(i = 1)`];
    REAL_ARITH_TAC]);;

let PATH_IN_SIMPLEX_PATH = prove
 (`!top f:(num->real)->A.
        singular_simplex (1,top) f ==> path_in top (simplex_path f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[singular_simplex; path_in; simplex_path] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\s. (f:(num->real)->A) (\i. if i = 0 then &1 - s else if i = 1 then s else &0)) =
    f o (\s i. if i = 0 then &1 - s else if i = 1 then s else &0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology (product_topology (:num) (\i. euclideanreal))
                          (standard_simplex 1)` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN X_GEN_TAC `i:num` THEN
    MAP_EVERY ASM_CASES_TAC [`i = 0`; `i = 1`] THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
    TRY(MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB) THEN
    REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN REWRITE_TAC[CONTINUOUS_MAP_ID];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN SIMP_TAC[SIMPLEX_PATH_POINT_IN]]);;

let PATH_SIMPLEX_SIMPLEX_PATH = prove
 (`!top f:(num->real)->A.
        singular_simplex (1,top) f ==> path_simplex (simplex_path f) = f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[singular_simplex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `RESTRICTION (standard_simplex 1) (f:(num->real)->A) = f`
   (fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THENL
   [ASM_REWRITE_TAC[RESTRICTION_FIXPOINT; IN]; ALL_TAC] THEN
  REWRITE_TAC[path_simplex; simplex_path; RESTRICTION_EXTENSION] THEN
  X_GEN_TAC `v:num->real` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[RESTRICTION] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP STANDARD_SIMPLEX_1_COORD) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\i. if i = 0 then &1 - v 1 else if i = 1 then v 1 else &0) = v`
   (fun th -> REWRITE_TAC[th] THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  UNDISCH_TAC `(v:num->real) IN standard_simplex 1` THEN
  REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

let SIMPLEX_PATH_ENDS = prove
 (`!f:(num->real)->A.
        simplex_path f (&0) = f(\i. if i = 0 then &1 else &0) /\
        simplex_path f (&1) = f(\i. if i = 1 then &1 else &0)`,
  GEN_TAC THEN REWRITE_TAC[simplex_path] THEN CONJ_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_ARITH_TAC);;

(* The reverse of a path has the opposite class.                              *)

let HOMOLOGOUS_REL_REVERSEPATH = prove
 (`!top p:real->A.
        path_in top p
        ==> homologous_rel (1,top,{})
              (frag_add (frag_of (path_simplex p))
                        (frag_of (path_simplex (\t. p(&1 - t)))))
              frag_0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p:real->A)(&0) IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_PATH_IN_TOPSPACE THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `tau = RESTRICTION (standard_simplex 2) ((p:real->A) o (\x:num->real. x 1))` THEN
  SUBGOAL_THEN `singular_simplex (2,top) (tau:(num->real)->A)` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN MATCH_MP_TAC SINGULAR_SIMPLEX_REAL_PARAM THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_STANDARD_SIMPLEX_COORD] THEN
    GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP STANDARD_SIMPLEX_2_COORDS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `singular_face 2 0 (tau:(num->real)->A) = path_simplex (\t. p(&1 - t)) /\
    singular_face 2 1 tau = path_simplex (\t. p(&0)) /\
    singular_face 2 2 tau = path_simplex p`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN SIMP_TAC[SINGULAR_FACE_RESTRICTION; ARITH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[path_simplex; RESTRICTION_EXTENSION; o_THM; simplicial_face] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `y:num->real` THEN
    DISCH_THEN(MP_TAC o MATCH_MP STANDARD_SIMPLEX_1_COORD) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[homologous_rel] THEN
  MP_TAC(ISPECL [`top:A topology`; `(p:real->A)(&0)`] SINGULAR_RELBOUNDARY_CONST_PATH) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `singular_relboundary (1,top,{}) (chain_boundary 2 (frag_of (tau:(num->real)->A)))`
  MP_TAC THENL
   [REWRITE_TAC[SINGULAR_BOUNDARY] THEN EXISTS_TAC `frag_of (tau:(num->real)->A)` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[SINGULAR_CHAIN_OF];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[CHAIN_BOUNDARY_OF_2; IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SINGULAR_RELBOUNDARY_ADD) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC FRAG_MODULE);;

let PATH_IN_REVERSE = prove
 (`!top p:real->A. path_in top p ==> path_in top (\t. p(&1 - t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[path_in] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\t. (p:real->A)(&1 - t)) = p o (\t. &1 - t)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN REWRITE_TAC[CONTINUOUS_MAP_ID];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC]);;

(* The loop at a attached to a path q by paths ps, pe from a to its ends.    *)

let HOMOLOGOUS_REL_ATTACHED_LOOP = prove
 (`!top (ps:real->A) q pe.
        path_in top ps /\ path_in top q /\ path_in top pe /\
        ps(&1) = q(&0) /\ pe(&1) = q(&1)
        ==> homologous_rel (1,top,{})
              (frag_of (path_simplex
                 (\t. if t <= &1 / &2
                      then if &2 * t <= &1 / &2 then ps(&2 * (&2 * t))
                           else q(&2 * (&2 * t) - &1)
                      else pe(&1 - (&2 * t - &1)))))
              (frag_sub (frag_add (frag_of (path_simplex ps)) (frag_of (path_simplex q)))
                        (frag_of (path_simplex pe)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `path_in top (\u. if u <= &1 / &2 then (ps:real->A)(&2 * u) else q(&2 * u - &1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_PATH_IN_JOIN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `\u. if u <= &1 / &2 then (ps:real->A)(&2 * u) else q(&2 * u - &1)`;
                 `\s. (pe:real->A)(&1 - s)`] HOMOLOGOUS_REL_JOINPATHS) THEN
  ASM_SIMP_TAC[PATH_IN_REVERSE] THEN ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "1") THEN
  MP_TAC(ISPECL [`top:A topology`; `ps:real->A`; `q:real->A`] HOMOLOGOUS_REL_JOINPATHS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "2") THEN
  MP_TAC(ISPECL [`top:A topology`; `pe:real->A`] HOMOLOGOUS_REL_REVERSEPATH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "3") THEN
  REMOVE_THEN "1" MP_TAC THEN REMOVE_THEN "2" MP_TAC THEN REMOVE_THEN "3" MP_TAC THEN
  REWRITE_TAC[path_simplex; homologous_rel; IMP_IMP] THEN
  DISCH_THEN(fun th -> let ths = CONJUNCTS th in
    MP_TAC(MATCH_MP SINGULAR_RELBOUNDARY_ADD
      (CONJ (MATCH_MP SINGULAR_RELBOUNDARY_ADD (CONJ (el 2 ths) (el 1 ths)))
            (el 0 ths)))) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC FRAG_MODULE);;

(* The loop at a attached to a singular 1-simplex by chosen paths.           *)

let hurewicz_loop = new_definition
 `hurewicz_loop (gam:A->real->A) f =
    \t. if t <= &1 / &2
        then if &2 * t <= &1 / &2 then gam (simplex_path f (&0)) (&2 * (&2 * t))
             else simplex_path f (&2 * (&2 * t) - &1)
        else gam (simplex_path f (&1)) (&1 - (&2 * t - &1))`;;

let HUREWICZ_LOOP = prove
 (`!top a (gam:A->real->A) f.
        (!x. x IN topspace top ==> path_in top (gam x) /\ gam x (&0) = a /\ gam x (&1) = x) /\
        singular_simplex (1,top) f
        ==> path_in top (hurewicz_loop gam f) /\
            hurewicz_loop gam f (&0) = a /\ hurewicz_loop gam f (&1) = a /\
            homologous_rel (1,top,{})
              (frag_of (path_simplex (hurewicz_loop gam f)))
              (frag_sub (frag_add (frag_of (path_simplex (gam (simplex_path f (&0)))))
                                  (frag_of f))
                        (frag_of (path_simplex (gam (simplex_path f (&1))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PATH_IN_SIMPLEX_PATH) THEN
  SUBGOAL_THEN `simplex_path (f:(num->real)->A) (&0) IN topspace top /\
                simplex_path f (&1) IN topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC TOPC_PATH_IN_TOPSPACE THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_in top ((gam:A->real->A) (simplex_path f (&0))) /\
    gam (simplex_path f (&0)) (&0) = a /\
    gam (simplex_path f (&0)) (&1) = simplex_path f (&0) /\
    path_in top ((gam:A->real->A) (simplex_path f (&1))) /\
    gam (simplex_path f (&1)) (&0) = a /\
    gam (simplex_path f (&1)) (&1) = simplex_path f (&1)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[hurewicz_loop] THEN
    SUBGOAL_THEN
     `path_in top (\u. if u <= &1 / &2 then (gam:A->real->A) (simplex_path f (&0)) (&2 * u)
                       else simplex_path f (&2 * u - &1))` ASSUME_TAC THENL
     [MATCH_MP_TAC TOPC_PATH_IN_JOIN THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`;
       `\u. if u <= &1 / &2 then (gam:A->real->A) (simplex_path f (&0)) (&2 * u)
            else simplex_path f (&2 * u - &1)`;
       `\s. (gam:A->real->A) (simplex_path f (&1)) (&1 - s)`] TOPC_PATH_IN_JOIN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[PATH_IN_REVERSE; ETA_AX] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PATH_IN_REVERSE THEN ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[]];
    REWRITE_TAC[hurewicz_loop] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[hurewicz_loop] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `(gam:A->real->A) (simplex_path f (&0))`;
                   `simplex_path (f:(num->real)->A)`;
                   `(gam:A->real->A) (simplex_path f (&1))`]
                  HOMOLOGOUS_REL_ATTACHED_LOOP) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP PATH_SIMPLEX_SIMPLEX_PATH) THEN
    REWRITE_TAC[hurewicz_loop]]);;

(* Points as 0-simplices and the chain-level comparison.                      *)

let POINT_SIMPLEX_BASIS = prove
 (`!x:A. RESTRICTION (standard_simplex 0) (\v. x) (\i. if i = 0 then &1 else &0) = x`,
  GEN_TAC THEN REWRITE_TAC[RESTRICTION] THEN
  REWRITE_TAC[BASIS_IN_STANDARD_SIMPLEX; LE_0]);;

let HUREWICZ_LOOP_CHAIN = prove
 (`!top a (gam:A->real->A) c.
        (!x. x IN topspace top ==> path_in top (gam x) /\ gam x (&0) = a /\ gam x (&1) = x) /\
        singular_chain (1,top) c
        ==> homologous_rel (1,top,{})
              (frag_sub c (frag_extend (\f. frag_of (path_simplex (hurewicz_loop gam f))) c))
              (frag_extend
                 (\pt. frag_of (path_simplex (gam (pt (\i. if i = 0 then &1 else &0)))))
                 (chain_boundary 1 c))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[singular_chain] THEN SPEC_TAC(`c:((num->real)->A)frag`,`c:((num->real)->A)frag`) THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FRAG_EXTEND_0; CHAIN_BOUNDARY_0; HOMOLOGOUS_REL_REFL;
                FRAG_MODULE `frag_sub frag_0 frag_0:((num->real)->A)frag = frag_0`];
    X_GEN_TAC `f:(num->real)->A` THEN REWRITE_TAC[IN] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `a:A`; `gam:A->real->A`; `f:(num->real)->A`]
                  HUREWICZ_LOOP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H")))) THEN
    REWRITE_TAC[FRAG_EXTEND_OF] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
      [GSYM(MATCH_MP PATH_SIMPLEX_SIMPLEX_PATH th)]) THEN
    REWRITE_TAC[CHAIN_BOUNDARY_PATH_SIMPLEX; FRAG_EXTEND_SUB; FRAG_EXTEND_OF] THEN
    REWRITE_TAC[POINT_SIMPLEX_BASIS] THEN
    REMOVE_THEN "H" MP_TAC THEN
    DISCH_THEN(MP_TAC o CONJ (SPECL [`1`; `top:A topology`; `{}:A->bool`;
                                     `frag_of (f:(num->real)->A)`] HOMOLOGOUS_REL_REFL)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMOLOGOUS_REL_SUB) THEN
    MATCH_MP_TAC(MESON[] `x:((num->real)->A)frag = x' /\ y = y'
                          ==> (homologous_rel (1,top:A topology,{}) x y ==>
                               homologous_rel (1,top,{}) x' y')`) THEN
    CONJ_TAC THEN CONV_TAC FRAG_MODULE;
    MAP_EVERY X_GEN_TAC [`c1:((num->real)->A)frag`; `c2:((num->real)->A)frag`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMOLOGOUS_REL_SUB) THEN
    REWRITE_TAC[FRAG_EXTEND_SUB; CHAIN_BOUNDARY_SUB] THEN
    MATCH_MP_TAC(MESON[] `x:((num->real)->A)frag = x'
                          ==> (homologous_rel (1,top:A topology,{}) x y ==>
                               homologous_rel (1,top,{}) x' y)`) THEN
    CONV_TAC FRAG_MODULE]);;

(* Integer combinations of loops at a are homologous to single loops at a.   *)

let HUREWICZ_LOOP_COMBINATION = prove
 (`!top a:A c.
        a IN topspace top /\
        frag_support c SUBSET {path_simplex L | L | path_in top L /\ L(&0) = a /\ L(&1) = a}
        ==> ?L. path_in top L /\ L(&0) = a /\ L(&1) = a /\
                homologous_rel (1,top,{}) c (frag_of (path_simplex L))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SPEC_TAC(`c:((num->real)->A)frag`,`c:((num->real)->A)frag`) THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `\t:real. (a:A)` THEN ASM_REWRITE_TAC[PATH_IN_CONST] THEN
    REWRITE_TAC[homologous_rel;
      FRAG_MODULE `frag_sub frag_0 x:((num->real)->A)frag = frag_neg x`;
      SINGULAR_RELBOUNDARY_NEG] THEN
    ASM_SIMP_TAC[SINGULAR_RELBOUNDARY_CONST_PATH];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `L:real->A` THEN STRIP_TAC THEN
    EXISTS_TAC `L:real->A` THEN ASM_REWRITE_TAC[HOMOLOGOUS_REL_REFL];
    MAP_EVERY X_GEN_TAC [`c1:((num->real)->A)frag`; `c2:((num->real)->A)frag`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `L1:real->A` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `L2:real->A` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `\t. if t <= &1 / &2 then (L1:real->A)(&2 * t) else L2(&1 - (&2 * t - &1))` THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `L1:real->A`; `\s. (L2:real->A)(&1 - s)`]
                    TOPC_PATH_IN_JOIN) THEN
      ASM_SIMP_TAC[PATH_IN_REVERSE; REAL_SUB_RZERO];
      REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `L1:real->A`; `\s. (L2:real->A)(&1 - s)`]
                    HOMOLOGOUS_REL_JOINPATHS) THEN
      ASM_SIMP_TAC[PATH_IN_REVERSE; REAL_SUB_RZERO] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `L2:real->A`] HOMOLOGOUS_REL_REVERSEPATH) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      REPEAT(POP_ASSUM MP_TAC) THEN
      REWRITE_TAC[homologous_rel; path_simplex] THEN
      REPEAT DISCH_TAC THEN
      SUBGOAL_THEN
       `singular_relboundary (1,top,{})
         (frag_sub (frag_sub
           (frag_sub (frag_sub c1 (frag_of (RESTRICTION (standard_simplex 1)
                                              (\v:num->real. (L1:real->A) (v 1)))))
                     (frag_sub c2 (frag_of (RESTRICTION (standard_simplex 1)
                                              (\v. (L2:real->A) (v 1))))))
           (frag_sub (frag_of (RESTRICTION (standard_simplex 1)
                       (\v. if v 1 <= &1 / &2 then L1(&2 * v 1)
                            else L2(&1 - (&2 * v 1 - &1)))))
                     (frag_add (frag_of (RESTRICTION (standard_simplex 1) (\v. L1(v 1))))
                               (frag_of (RESTRICTION (standard_simplex 1)
                                           (\v. L2(&1 - v 1)))))))
           (frag_sub (frag_add (frag_of (RESTRICTION (standard_simplex 1) (\v. L2(v 1))))
                               (frag_of (RESTRICTION (standard_simplex 1)
                                           (\v. L2(&1 - v 1)))))
                     frag_0))`
      MP_TAC THENL
       [MATCH_MP_TAC SINGULAR_RELBOUNDARY_SUB THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
        MATCH_MP_TAC SINGULAR_RELBOUNDARY_SUB THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
        MATCH_MP_TAC SINGULAR_RELBOUNDARY_SUB THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC FRAG_MODULE]]]);;

(* G7: Hurewicz in degree 1, the easy direction.                              *)

let ATOP_HUREWICZ1 = prove
 (`ATOP_HUREWICZ1_STATEMENT (:A)`,
  REWRITE_TAC[ATOP_HUREWICZ1_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `a:A`] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[homology_group; RELATIVE_HOMOLOGY_GROUP; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `c:((num->real)->A)frag` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?gam:A->real->A. !x. x IN topspace top
                           ==> path_in top (gam x) /\ gam x (&0) = a /\ gam x (&1) = x`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `x:A`] o
        GEN_REWRITE_RULE I [path_connected_space]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [SINGULAR_CYCLE]) THEN
    MP_TAC(ISPECL [`top:A topology`; `a:A`; `gam:A->real->A`; `c:((num->real)->A)frag`]
                  HUREWICZ_LOOP_CHAIN) THEN
    ASM_REWRITE_TAC[FRAG_EXTEND_0] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `a:A`;
                   `frag_extend (\f. frag_of (path_simplex (hurewicz_loop (gam:A->real->A) f)))
                                (c:((num->real)->A)frag)`]
                  HUREWICZ_LOOP_COMBINATION) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS {frag_support (frag_of (path_simplex
                           (hurewicz_loop (gam:A->real->A) f))) | f IN frag_support c}` THEN
      REWRITE_TAC[FRAG_SUPPORT_FRAG_EXTEND] THEN
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; FRAG_SUPPORT_OF; SING_SUBSET] THEN
      X_GEN_TAC `f:(num->real)->A` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `hurewicz_loop (gam:A->real->A) f` THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `a:A`; `gam:A->real->A`; `f:(num->real)->A`]
                    HUREWICZ_LOOP) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `singular_chain (1,top) (c:((num->real)->A)frag)` THEN
      REWRITE_TAC[singular_chain; SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `f:(num->real)->A`) THEN
      ASM_REWRITE_TAC[IN];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `L:real->A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM path_simplex; HOMOLOGOUS_REL_EQ] THEN
    MATCH_MP_TAC HOMOLOGOUS_REL_TRANS THEN
    EXISTS_TAC `frag_extend (\f. frag_of (path_simplex (hurewicz_loop (gam:A->real->A) f)))
                            (c:((num->real)->A)frag)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `homologous_rel (1,top,{})
       (frag_sub c (frag_extend (\f. frag_of (path_simplex (hurewicz_loop (gam:A->real->A) f)))
                                (c:((num->real)->A)frag))) frag_0` THEN
    REWRITE_TAC[homologous_rel] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    CONV_TAC FRAG_MODULE;
    X_GEN_TAC `g:real->A` THEN STRIP_TAC THEN
    REWRITE_TAC[homology_group; RELATIVE_HOMOLOGY_GROUP; HOMOLOGOUS_REL_EQ_RELBOUNDARY] THEN
    MP_TAC(ISPECL [`top:A topology`; `g:real->A`; `\t:real. (a:A)`]
                  HOMOLOGOUS_REL_HOMOTOPIC_PATHS) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `a:A`] SINGULAR_RELBOUNDARY_CONST_PATH) THEN
    ASM_REWRITE_TAC[path_simplex; homologous_rel; IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SINGULAR_RELBOUNDARY_ADD) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC FRAG_MODULE]);;

(* ========================================================================= *)
(* The homotopy extension property for the pair                             *)
(* (standard_simplex p, its boundary), with an arbitrary target space, by   *)
(* the radial projection from the point (barycentre, 2) of the prism.        *)
(* ========================================================================= *)

let simplex_min = define
 `(simplex_min 0 (x:num->real) = x 0) /\
  (simplex_min (SUC p) x = min (simplex_min p x) (x (SUC p)))`;;

let SIMPLEX_MIN_LE = prove
 (`!p x i. i <= p ==> simplex_min p x <= x i`,
  INDUCT_TAC THEN REWRITE_TAC[simplex_min; LE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  TRY(MATCH_MP_TAC(REAL_ARITH `a <= c ==> min a b <= c`) THEN
      ASM_SIMP_TAC[] THEN NO_TAC) THEN
  REAL_ARITH_TAC);;

let SIMPLEX_MIN_EXISTS = prove
 (`!p x. ?i. i <= p /\ simplex_min p x = x i`,
  INDUCT_TAC THEN REWRITE_TAC[simplex_min] THENL
   [GEN_TAC THEN EXISTS_TAC `0` THEN REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  X_GEN_TAC `x:num->real` THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o SPEC `x:num->real`) THEN
  ASM_CASES_TAC `simplex_min p x <= (x:num->real) (SUC p)` THENL
   [EXISTS_TAC `i:num` THEN ASM_SIMP_TAC[REAL_ARITH `a <= b ==> min a b = a`] THEN
    ASM_ARITH_TAC;
    EXISTS_TAC `SUC p` THEN REWRITE_TAC[LE_REFL] THEN ASM_REAL_ARITH_TAC]);;

let SIMPLEX_MIN_EQ = prove
 (`!p x y. (!i. i <= p ==> x i = y i) ==> simplex_min p x = simplex_min p y`,
  INDUCT_TAC THEN REWRITE_TAC[simplex_min] THEN REPEAT GEN_TAC THENL
   [DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[LE]) THEN REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `simplex_min p x = simplex_min p (y:num->real) /\
                (x:num->real) (SUC p) = y (SUC p)`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL]]);;

let SIMPLEX_MIN_AFFINE = prove
 (`!p x c s. &0 <= s
             ==> simplex_min p (\i. c + s * (x i - c)) = c + s * (simplex_min p x - c)`,
  INDUCT_TAC THEN REWRITE_TAC[simplex_min] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `simplex_min p x <= (x:num->real) (SUC p)` THENL
   [SUBGOAL_THEN `s * (simplex_min p x - c) <= s * ((x:num->real) (SUC p) - c)`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN `s * ((x:num->real) (SUC p) - c) <= s * (simplex_min p x - c)`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[real_min] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC);;

let CONTINUOUS_MAP_SIMPLEX_MIN = prove
 (`!p top (f:A->num->real).
        (!i. continuous_map (top,euclideanreal) (\z. f z i))
        ==> continuous_map (top,euclideanreal) (\z. simplex_min p (f z))`,
  INDUCT_TAC THEN ASM_SIMP_TAC[simplex_min; CONTINUOUS_MAP_REAL_MIN]);;

let STANDARD_SIMPLEX_MIN = prove
 (`!p x. x IN standard_simplex p
         ==> &0 <= simplex_min p x /\ (&p + &1) * simplex_min p x <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`p:num`; `x:num->real`] SIMPLEX_MIN_EXISTS) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`\i:num. simplex_min p x`; `x:num->real`; `0`; `p:num`]
                  SUM_LE_NUMSEG) THEN
    ASM_SIMP_TAC[SIMPLEX_MIN_LE; SUM_CONST_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `(p + 1) - 0 = p + 1`; GSYM REAL_OF_NUM_ADD]]);;

(* The barycentre, rays from it and the radial gauge.                        *)

let simplex_centre = new_definition
 `simplex_centre p = (\i. if i <= p then inv(&p + &1) else &0)`;;

let simplex_ray = new_definition
 `simplex_ray p (x:num->real) s =
    (\i. simplex_centre p i + s * (x i - simplex_centre p i))`;;

let simplex_gauge = new_definition
 `simplex_gauge p x = &1 - (&p + &1) * simplex_min p x`;;

let SIMPLEX_RAY_1 = prove
 (`!p x. simplex_ray p x (&1) = x`,
  REWRITE_TAC[simplex_ray; FUN_EQ_THM] THEN REAL_ARITH_TAC);;

let SIMPLEX_RAY_MIN = prove
 (`!p x s. &0 <= s
           ==> simplex_min p (simplex_ray p x s) =
               inv(&p + &1) + s * (simplex_min p x - inv(&p + &1))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `simplex_min p (\i. inv(&p + &1) + s * ((x:num->real) i - inv(&p + &1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLEX_MIN_EQ THEN SIMP_TAC[simplex_ray; simplex_centre];
    ASM_SIMP_TAC[SIMPLEX_MIN_AFFINE]]);;

let SIMPLEX_GAUGE_RAY = prove
 (`!p x s. &0 <= s ==> simplex_gauge p (simplex_ray p x s) = s * simplex_gauge p x`,
  SIMP_TAC[simplex_gauge; SIMPLEX_RAY_MIN] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&p + &1) * inv(&p + &1) = &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN REAL_ARITH_TAC; CONV_TAC REAL_RING]);;

let STANDARD_SIMPLEX_GAUGE = prove
 (`!p x. x IN standard_simplex p
         ==> &0 <= simplex_gauge p x /\ simplex_gauge p x <= &1 /\
             (simplex_gauge p x = &1 <=> simplex_min p x = &0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP STANDARD_SIMPLEX_MIN) THEN
  REWRITE_TAC[simplex_gauge] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&p + &1) * simplex_min p x` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 - y = &1 <=> y = &0`; REAL_ENTIRE] THEN
  ASM_REAL_ARITH_TAC);;

let SIMPLEX_RAY_IN = prove
 (`!p x s. x IN standard_simplex p /\ &0 <= s /\ s * simplex_gauge p x <= &1
           ==> simplex_ray p x s IN standard_simplex p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= simplex_min p (simplex_ray p x s)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SIMPLEX_RAY_MIN] THEN
    UNDISCH_TAC `s * simplex_gauge p x <= &1` THEN REWRITE_TAC[simplex_gauge] THEN
    SUBGOAL_THEN `&0 < inv(&p + &1) /\ (&p + &1) * inv(&p + &1) = &1` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_MUL_RINV THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `c = inv(&p + &1)` THEN ABBREV_TAC `m = simplex_min p x` THEN
    STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `c + s * (m - c) = c * (&1 - s * (&1 - (&p + &1) * m))` SUBST1_TAC THENL
     [UNDISCH_TAC `(&p + &1) * c = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(x:num->real) IN standard_simplex p` THEN
  REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sum (0..p) (simplex_ray p x s) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[simplex_ray] THEN
    ASM_SIMP_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_SUB_NUMSEG; ETA_AX] THEN
    SUBGOAL_THEN `sum (0..p) (simplex_centre p) = &1` SUBST1_TAC THENL
     [TRANS_TAC EQ_TRANS `sum (0..p) (\i. inv(&p + &1))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[simplex_centre];
        REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(p + 1) - 0 = p + 1`] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN MATCH_MP_TAC REAL_MUL_RINV THEN
        REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i <= p ==> &0 <= simplex_ray p x s i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `simplex_min p (simplex_ray p x s)` THEN
    ASM_SIMP_TAC[SIMPLEX_MIN_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. p < i ==> simplex_ray p x s i = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[simplex_ray; simplex_centre] THEN
    ASM_SIMP_TAC[ARITH_RULE `(p:num) < i ==> ~(i <= p)`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `(i:num) <= p` THENL
   [ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o
      check (fun th -> is_eq(concl th) && is_comb(lhs(concl th)) &&
                       rand(lhs(concl th)) = `simplex_ray p x s`)) THEN
    MP_TAC(ISPECL [`{i:num}`; `0..p`; `simplex_ray p x s`] SUM_SUBSET_SIMPLE) THEN
    ASM_SIMP_TAC[SUM_SING; FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG; LE_0; IN_DIFF];
    ASM_SIMP_TAC[ARITH_RULE `~((i:num) <= p) ==> p < i`] THEN REAL_ARITH_TAC]);;

(* The prism standard_simplex p x [0,1], the boundary prism, and the         *)
(* extension of a homotopy given on the bottom and the boundary prism.       *)

let simplex_prism = new_definition
 `simplex_prism p =
    prod_topology (subtopology (product_topology (:num) (\i. euclideanreal))
                               (standard_simplex p))
                  (subtopology euclideanreal (real_interval[&0,&1]))`;;

let simplex_bdprism = new_definition
 `simplex_bdprism p =
    subtopology (prod_topology (product_topology (:num) (\i. euclideanreal)) euclideanreal)
                {z:(num->real)#real | FST z IN standard_simplex p /\
                                      simplex_min p (FST z) = &0 /\
                                      &0 <= SND z /\ SND z <= &1}`;;

let hep_extension = new_definition
 `hep_extension p (sig:(num->real)->A) B =
    \z. if &2 * simplex_gauge p (FST z) <= &2 - SND z
        then sig(simplex_ray p (FST z) (&2 / (&2 - SND z)))
        else B(simplex_ray p (FST z) (inv(simplex_gauge p (FST z))),
               &2 - (&2 - SND z) / simplex_gauge p (FST z))`;;

let IN_TOPSPACE_SIMPLEX_PRISM = prove
 (`!p z. z IN topspace(simplex_prism p) <=>
         FST z IN standard_simplex p /\ &0 <= SND z /\ SND z <= &1`,
  REWRITE_TAC[simplex_prism; TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[TOPSPACE_STANDARD_SIMPLEX; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  REWRITE_TAC[IN_REAL_INTERVAL]);;

let IN_TOPSPACE_SIMPLEX_BDPRISM = prove
 (`!p z. z IN topspace(simplex_bdprism p) <=>
         FST z IN standard_simplex p /\ simplex_min p (FST z) = &0 /\
         &0 <= SND z /\ SND z <= &1`,
  REWRITE_TAC[simplex_bdprism; TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY] THEN
  REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; TOPSPACE_EUCLIDEANREAL; IN_INTER] THEN
  REWRITE_TAC[o_DEF; TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV; CROSS_UNIV] THEN
  REWRITE_TAC[IN_UNIV; IN_ELIM_THM]);;

let CONTINUOUS_MAP_SIMPLEX_PRISM_COORDS = prove
 (`!p s i. continuous_map (subtopology (simplex_prism p) s,euclideanreal) (\z. FST z i) /\
           continuous_map (subtopology (simplex_prism p) s,euclideanreal) (\z. SND z) /\
           continuous_map (subtopology (simplex_prism p) s,euclideanreal) SND /\
           continuous_map (subtopology (simplex_prism p) s,euclideanreal)
                          (\z. simplex_gauge p (FST z))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!i. continuous_map (subtopology (simplex_prism p) s,euclideanreal) (\z. FST z i)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    REWRITE_TAC[simplex_prism] THEN
    SUBGOAL_THEN `(\z:(num->real)#real. FST z i) = (\x. x i) o FST` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology (product_topology (:num) (\i. euclideanreal))
                            (standard_simplex p)` THEN
    REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_STANDARD_SIMPLEX_COORD];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC(TAUT `p /\ q ==> p /\ p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN REWRITE_TAC[simplex_prism] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN REWRITE_TAC[CONTINUOUS_MAP_SND];
    REWRITE_TAC[simplex_gauge] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
    MATCH_MP_TAC CONTINUOUS_MAP_SIMPLEX_MIN THEN ASM_REWRITE_TAC[]]);;

let CONTINUOUS_MAP_SIMPLEX_PRISM_COORDS_FULL = prove
 (`!p i. continuous_map (simplex_prism p,euclideanreal) (\z. FST z i) /\
         continuous_map (simplex_prism p,euclideanreal) (\z. SND z) /\
         continuous_map (simplex_prism p,euclideanreal) SND /\
         continuous_map (simplex_prism p,euclideanreal) (\z. simplex_gauge p (FST z))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`p:num`; `topspace(simplex_prism p)`; `i:num`]
               CONTINUOUS_MAP_SIMPLEX_PRISM_COORDS) THEN
  REWRITE_TAC[SUBTOPOLOGY_TOPSPACE]);;

let CONTINUOUS_MAP_SIMPLEX_RAY = prove
 (`!p top (f:A->num->real) g.
        (!i. continuous_map (top,euclideanreal) (\z. f z i)) /\
        continuous_map (top,euclideanreal) g
        ==> continuous_map (top,product_topology (:num) (\i. euclideanreal))
                           (\z. simplex_ray p (f z) (g z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[simplex_ray] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST]);;

let CONTINUOUS_MAP_HEP_EXTENSION = prove
 (`!p top (sig:(num->real)->A) B.
        continuous_map (subtopology (product_topology (:num) (\i. euclideanreal))
                                    (standard_simplex p),top) sig /\
        continuous_map (simplex_bdprism p,top) B /\
        (!x. x IN standard_simplex p /\ simplex_min p x = &0 ==> B(x,&0) = sig x)
        ==> continuous_map (simplex_prism p,top) (hep_extension p sig B)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hep_extension] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_CASES_LE THEN
  MP_TAC(SPECL [`p:num`; `topspace(simplex_prism p)`] CONTINUOUS_MAP_SIMPLEX_PRISM_COORDS) THEN
  REWRITE_TAC[SUBTOPOLOGY_TOPSPACE; FORALL_AND_THM] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
    FIRST_ASSUM(fun th -> ACCEPT_TAC(REWRITE_RULE[ETA_AX] th));
    GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology (product_topology (:num) (\i. euclideanreal))
                            (standard_simplex p)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_SIMPLEX_RAY THEN
      REWRITE_TAC[CONTINUOUS_MAP_SIMPLEX_PRISM_COORDS] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_DIV THEN
      REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
        REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST; CONTINUOUS_MAP_SIMPLEX_PRISM_COORDS];
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM;
                    IN_TOPSPACE_SIMPLEX_PRISM] THEN REAL_ARITH_TAC];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM;
                  IN_TOPSPACE_SIMPLEX_PRISM] THEN
      X_GEN_TAC `z:(num->real)#real` THEN STRIP_TAC THEN
      MATCH_MP_TAC SIMPLEX_RAY_IN THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < &2 - SND(z:(num->real)#real)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `&2 / (&2 - SND(z:(num->real)#real)) * simplex_gauge p (FST z) =
        (&2 * simplex_gauge p (FST z)) / (&2 - SND z)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `simplex_bdprism p` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[simplex_bdprism; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_SIMPLEX_RAY THEN
        REWRITE_TAC[CONTINUOUS_MAP_SIMPLEX_PRISM_COORDS] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_INV THEN
        REWRITE_TAC[CONTINUOUS_MAP_SIMPLEX_PRISM_COORDS];
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_DIV THEN
        REWRITE_TAC[CONTINUOUS_MAP_SIMPLEX_PRISM_COORDS] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
          REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST; CONTINUOUS_MAP_SIMPLEX_PRISM_COORDS];
          ALL_TAC]] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; IN_TOPSPACE_SIMPLEX_PRISM] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM;
                IN_TOPSPACE_SIMPLEX_PRISM] THEN
    X_GEN_TAC `z:(num->real)#real` THEN STRIP_TAC THEN
    ABBREV_TAC `g = simplex_gauge p (FST(z:(num->real)#real))` THEN
    SUBGOAL_THEN `&1 / &2 <= g /\ g <= &1` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`p:num`; `FST(z:(num->real)#real)`] STANDARD_SIMPLEX_GAUGE) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&2 - SND(z:(num->real)#real) <= &2 * g` THEN
      UNDISCH_TAC `SND(z:(num->real)#real) <= &1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `simplex_ray p (FST z) (inv g) IN standard_simplex p /\
                  simplex_gauge p (simplex_ray p (FST(z:(num->real)#real)) (inv g)) = &1`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SIMPLEX_GAUGE_RAY; REAL_LE_INV_EQ;
                   REAL_ARITH `&1 / &2 <= g ==> &0 <= g`] THEN
      SUBGOAL_THEN `inv g * g = &1` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLEX_RAY_IN THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_ARITH `&1 / &2 <= g ==> &0 <= g`; REAL_LE_REFL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`p:num`; `simplex_ray p (FST(z:(num->real)#real)) (inv g)`]
                   STANDARD_SIMPLEX_GAUGE) THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `&0 < g` ASSUME_TAC THENL
       [UNDISCH_TAC `&1 / &2 <= g` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= (&2 - SND(z:(num->real)#real)) / g /\
                    (&2 - SND(z:(num->real)#real)) / g <= &2`
      MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
        UNDISCH_TAC `&2 - SND(z:(num->real)#real) <= &2 * g` THEN
        UNDISCH_TAC `SND(z:(num->real)#real) <= &1` THEN
        UNDISCH_TAC `g <= &1` THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    X_GEN_TAC `z:(num->real)#real` THEN
    REWRITE_TAC[IN_TOPSPACE_SIMPLEX_PRISM] THEN STRIP_TAC THEN
    ABBREV_TAC `g = simplex_gauge p (FST(z:(num->real)#real))` THEN
    SUBGOAL_THEN `&0 < g` ASSUME_TAC THENL
     [UNDISCH_TAC `&2 * g = &2 - SND(z:(num->real)#real)` THEN
      UNDISCH_TAC `SND(z:(num->real)#real) <= &1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 / (&2 - SND(z:(num->real)#real)) = inv g /\
                  (&2 - SND z) / g = &2` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `&0 < g` THEN
      UNDISCH_TAC `&2 * g = &2 - SND(z:(num->real)#real)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV))) THEN
    REWRITE_TAC[REAL_SUB_REFL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `simplex_ray p (FST z) (inv g) IN standard_simplex p /\
                  simplex_gauge p (simplex_ray p (FST(z:(num->real)#real)) (inv g)) = &1`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SIMPLEX_GAUGE_RAY; REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      SUBGOAL_THEN `inv g * g = &1` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLEX_RAY_IN THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_LE_REFL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`p:num`; `simplex_ray p (FST(z:(num->real)#real)) (inv g)`]
                 STANDARD_SIMPLEX_GAUGE) THEN
    ASM_SIMP_TAC[]]);;

let HEP_EXTENSION_BOTTOM = prove
 (`!p (sig:(num->real)->A) B x.
        x IN standard_simplex p ==> hep_extension p sig B (x,&0) = sig x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hep_extension; FST; SND] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP STANDARD_SIMPLEX_GAUGE) THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[SIMPLEX_RAY_1];
    ASM_REAL_ARITH_TAC]);;

let HEP_EXTENSION_SIDE = prove
 (`!p (sig:(num->real)->A) B x l.
        x IN standard_simplex p /\ simplex_min p x = &0 /\ &0 <= l /\ l <= &1 /\
        B(x,&0) = sig x
        ==> hep_extension p sig B (x,l) = B(x,l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hep_extension; FST; SND] THEN
  SUBGOAL_THEN `simplex_gauge p x = &1` SUBST1_TAC THENL
   [ASM_MESON_TAC[STANDARD_SIMPLEX_GAUGE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_1; REAL_DIV_1; SIMPLEX_RAY_1;
              REAL_ARITH `&2 - (&2 - l) = l`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `l = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[SIMPLEX_RAY_1]);;

(* ========================================================================= *)
(* Deleting a vanishing coordinate (inverse of a face                       *)
(* inclusion), the face identities, and the inductive step of the           *)
(* compression: extending a natural family of homotopies of the faces of a  *)
(* singular p-simplex to a homotopy of the simplex.                          *)
(* ========================================================================= *)

let simplex_delete = new_definition
 `simplex_delete k (x:num->real) = (\i. if i < k then x i else x(i + 1))`;;

let SIMPLICIAL_FACE_DELETE = prove
 (`!k x. x k = &0 ==> simplicial_face k (simplex_delete k x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplicial_face; simplex_delete; FUN_EQ_THM] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i:num < k` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(i:num < k) /\ ~(i = k) ==> ~(i - 1 < k)`] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let SIMPLEX_DELETE_FACE = prove
 (`!k y. simplex_delete k (simplicial_face k y) = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_face; simplex_delete; FUN_EQ_THM] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i:num < k` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(i:num < k) ==> ~(i + 1 < k) /\ ~(i + 1 = k)`; ADD_SUB]);;

let SUM_SIMPLICIAL_FACE = prove
 (`!p k y. 1 <= p /\ k <= p ==> sum(0..p) (simplicial_face k y) = sum(0..p-1) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplicial_face] THEN
  ASM_SIMP_TAC[SUM_CASES; FINITE_NUMSEG; IN_NUMSEG; ARITH_RULE
   `(0 <= i /\ i <= p) /\ ~(i < k) <=> k <= i /\ i <= p`] THEN
  REWRITE_TAC[GSYM numseg] THEN
  ASM_SIMP_TAC[SUM_CLAUSES_LEFT; REAL_ADD_LID] THEN
  SUBGOAL_THEN `p = (p - 1) + 1` (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPEC `1` SUM_OFFSET; ADD_SUB] THEN
  SIMP_TAC[ARITH_RULE `k <= i ==> ~(i + 1 = k)`] THEN
  REWRITE_TAC[GSYM IN_NUMSEG] THEN
  W(MP_TAC o PART_MATCH (rand o rand) SUM_UNION o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; FINITE_RESTRICT] THEN ANTS_TAC THENL
   [SIMP_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[IN_UNION; IN_ELIM_THM; IN_NUMSEG] THEN ASM_ARITH_TAC);;

let SIMPLEX_DELETE_IN = prove
 (`!p k x. 1 <= p /\ k <= p /\ x IN standard_simplex p /\ x k = &0
           ==> simplex_delete k x IN standard_simplex (p - 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sum(0..p-1) (simplex_delete k x) = &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`p:num`; `k:num`; `simplex_delete k x`] SUM_SIMPLICIAL_FACE) THEN
    ASM_SIMP_TAC[SIMPLICIAL_FACE_DELETE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(x:num->real) IN standard_simplex p` THEN
    SIMP_TAC[standard_simplex; IN_ELIM_THM];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:num->real) IN standard_simplex p` THEN
  REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simplex_delete] THEN CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(i < k) /\ p < i + 1` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[]]]);;

let SIMPLICIAL_FACE_FACE = prove
 (`!j k t. j < k
           ==> simplicial_face k (simplicial_face j t) =
               simplicial_face j (simplicial_face (k - 1) t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplicial_face; FUN_EQ_THM] THEN
  X_GEN_TAC `i:num` THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY(AP_TERM_TAC THEN ASM_ARITH_TAC) THEN ASM_ARITH_TAC);;

let SIMPLEX_DELETE_DELETE = prove
 (`!j k x. j < k
           ==> simplex_delete (k - 1) (simplex_delete j x) =
               simplex_delete j (simplex_delete k x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplex_delete; FUN_EQ_THM] THEN
  X_GEN_TAC `i:num` THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY(AP_TERM_TAC THEN ASM_ARITH_TAC) THEN ASM_ARITH_TAC);;

let SIMPLEX_DELETE_COORDS = prove
 (`!j k x. j < k ==> simplex_delete j x (k - 1) = x k /\ simplex_delete k x j = x j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplex_delete] THEN
  ASM_SIMP_TAC[ARITH_RULE `j < k ==> ~(k - 1 < j)`] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let SINGULAR_FACE_FACE = prove
 (`!p j k (f:(num->real)->A).
        2 <= p /\ j < k /\ k <= p
        ==> singular_face (p - 1) j (singular_face p k f) =
            singular_face (p - 1) (k - 1) (singular_face p j f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[singular_face; RESTRICTION_EXTENSION] THEN
  X_GEN_TAC `t:num->real` THEN DISCH_TAC THEN REWRITE_TAC[o_THM; RESTRICTION] THEN
  SUBGOAL_THEN `simplicial_face j t IN standard_simplex (p - 1) /\
                simplicial_face (k - 1) t IN standard_simplex (p - 1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SIMPLICIAL_FACE_IN_STANDARD_SIMPLEX THEN
    ASM_REWRITE_TAC[ARITH_RULE `p - 1 - 1 = p - 2`] THEN
    UNDISCH_TAC `(t:num->real) IN standard_simplex (p - 1 - 1)` THEN
    REWRITE_TAC[ARITH_RULE `p - 1 - 1 = p - 2`] THEN SIMP_TAC[] THEN ASM_ARITH_TAC;
    AP_TERM_TAC THEN ASM_SIMP_TAC[SIMPLICIAL_FACE_FACE]]);;

(* The faces of the boundary prism.                                          *)

let SIMPLEX_MIN_ZERO = prove
 (`!p x k. x IN standard_simplex p /\ k <= p /\ x k = &0 ==> simplex_min p x = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= m /\ m <= &0 ==> m = &0`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[STANDARD_SIMPLEX_MIN]; ASM_MESON_TAC[SIMPLEX_MIN_LE]]);;

let CONTINUOUS_MAP_BDPRISM_COORD = prove
 (`!p s i. continuous_map (subtopology (simplex_bdprism p) s,euclideanreal) (\z. FST z i) /\
           continuous_map (subtopology (simplex_bdprism p) s,euclideanreal) SND`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  REWRITE_TAC[simplex_bdprism] THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THENL
   [SUBGOAL_THEN `(\z:(num->real)#real. FST z i) = (\x. x i) o FST` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `product_topology (:num) (\i. euclideanreal)` THEN
    SIMP_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV];
    REWRITE_TAC[CONTINUOUS_MAP_SND]]);;

let BDPRISM_PIECE_CLOSED = prove
 (`!p k. closed_in (simplex_bdprism p)
                   {z | z IN topspace(simplex_bdprism p) /\ FST z k = &0}`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\z:(num->real)#real. FST z k`; `simplex_bdprism p`; `euclideanreal`;
                 `{&0}`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  REWRITE_TAC[IN_SING] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`p:num`; `topspace(simplex_bdprism p)`; `k:num`]
                 CONTINUOUS_MAP_BDPRISM_COORD) THEN
    SIMP_TAC[SUBTOPOLOGY_TOPSPACE];
    MATCH_MP_TAC CLOSED_IN_T1_SING THEN
    REWRITE_TAC[T1_SPACE_EUCLIDEANREAL; TOPSPACE_EUCLIDEANREAL; IN_UNIV]]);;

let CONTINUOUS_MAP_DELETE_PIECE = prove
 (`!p k. 1 <= p /\ k <= p
         ==> continuous_map
              (subtopology (simplex_bdprism p)
                 {z | z IN topspace(simplex_bdprism p) /\ FST z k = &0},
               simplex_prism (p - 1))
              (\z. simplex_delete k (FST z),SND z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplex_prism; CONTINUOUS_MAP_PAIRWISE; o_DEF] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV; simplex_delete] THEN
      X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(i:num) < k` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_BDPRISM_COORD];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM;
                  IN_TOPSPACE_SIMPLEX_BDPRISM] THEN
      X_GEN_TAC `z:(num->real)#real` THEN STRIP_TAC THEN
      MATCH_MP_TAC SIMPLEX_DELETE_IN THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX; CONTINUOUS_MAP_BDPRISM_COORD] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM;
                IN_TOPSPACE_SIMPLEX_BDPRISM; IN_REAL_INTERVAL] THEN
    SIMP_TAC[]]);;

(* The hypotheses on a natural family of homotopies of (p-1)-simplices.     *)

let compression_family = new_definition
 `compression_family (p,top) (K1:((num->real)->A)->(num->real)#real->A) K0 <=>
    !f. singular_simplex (p,top) f
        ==> continuous_map (simplex_prism p,top) (K1 f) /\
            (!x. x IN standard_simplex p ==> K1 f (x,&0) = f x) /\
            (!j y l. j <= p /\ y IN standard_simplex (p - 1) /\ &0 <= l /\ l <= &1
                     ==> K1 f (simplicial_face j y,l) = K0 (singular_face p j f) (y,l))`;;

let COMPRESSION_AGREE = prove
 (`!p top (K1:((num->real)->A)->(num->real)#real->A) K0 sig i j x l.
        2 <= p /\ singular_simplex (p,top) sig /\ compression_family (p - 1,top) K1 K0 /\
        i < j /\ j <= p /\ x IN standard_simplex p /\ x i = &0 /\ x j = &0 /\
        &0 <= l /\ l <= &1
        ==> K1 (singular_face p i sig) (simplex_delete i x,l) =
            K1 (singular_face p j sig) (simplex_delete j x,l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compression_family] THEN STRIP_TAC THEN
  ABBREV_TAC `w = simplex_delete i (simplex_delete j (x:num->real))` THEN
  SUBGOAL_THEN `simplex_delete j (x:num->real) IN standard_simplex (p - 1) /\
                simplex_delete j x i = &0 /\ simplex_delete i x (j - 1) = &0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SIMPLEX_DELETE_COORDS] THEN MATCH_MP_TAC SIMPLEX_DELETE_IN THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:num->real) IN standard_simplex (p - 2)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[ARITH_RULE `p - 2 = p - 1 - 1`] THEN
    MATCH_MP_TAC SIMPLEX_DELETE_IN THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `simplex_delete j (x:num->real) = simplicial_face i w /\
                simplex_delete i x = simplicial_face (j - 1) w`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [EXPAND_TAC "w" THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SIMPLICIAL_FACE_DELETE THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM(MATCH_MP SIMPLEX_DELETE_DELETE (ASSUME `(i:num) < j`))] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SIMPLICIAL_FACE_DELETE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `singular_simplex (p - 1,top) (singular_face p i (sig:(num->real)->A)) /\
                singular_simplex (p - 1,top) (singular_face p j sig)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SINGULAR_SIMPLEX_SINGULAR_FACE THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `singular_face p i (sig:(num->real)->A)` th) THEN
    MP_TAC(SPEC `singular_face p j (sig:(num->real)->A)` th)) THEN
  ASM_REWRITE_TAC[ARITH_RULE `p - 1 - 1 = p - 2`] THEN
  DISCH_THEN(MP_TAC o SPECL [`i:num`; `w:num->real`; `l:real`] o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`j - 1`; `w:num->real`; `l:real`] o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SINGULAR_FACE_FACE THEN ASM_REWRITE_TAC[]);;

(* The inductive step: a natural extension to the p-simplices.               *)

let COMPRESSION_STEP = prove
 (`!p top (K1:((num->real)->A)->(num->real)#real->A) K0 sig.
        2 <= p /\ singular_simplex (p,top) sig /\ compression_family (p - 1,top) K1 K0
        ==> ?K. continuous_map (simplex_prism p,top) K /\
                (!x. x IN standard_simplex p ==> K(x,&0) = sig x) /\
                (!k y l. k <= p /\ y IN standard_simplex (p - 1) /\ &0 <= l /\ l <= &1
                         ==> K(simplicial_face k y,l) = K1 (singular_face p k sig) (y,l))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. k <= p ==> singular_simplex (p - 1,top:A topology)
                                  (singular_face p k (sig:(num->real)->A))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SINGULAR_SIMPLEX_SINGULAR_FACE THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`simplex_bdprism p`; `top:A topology`;
    `\k z. (K1:((num->real)->A)->(num->real)#real->A) (singular_face p k sig)
                (simplex_delete k (FST z),SND z)`;
    `\k. {z | z IN topspace(simplex_bdprism p) /\ FST z k = &0}`;
    `0..p`] PASTING_LEMMA_EXISTS_CLOSED) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
      X_GEN_TAC `z:(num->real)#real` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`p:num`; `FST(z:(num->real)#real)`] SIMPLEX_MIN_EXISTS) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
      UNDISCH_TAC `(z:(num->real)#real) IN topspace (simplex_bdprism p)` THEN
      REWRITE_TAC[IN_TOPSPACE_SIMPLEX_BDPRISM] THEN SIMP_TAC[];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[BDPRISM_PIECE_CLOSED] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `simplex_prism (p - 1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_DELETE_PIECE THEN ASM_ARITH_TAC;
        UNDISCH_TAC `compression_family (p - 1,top) (K1:((num->real)->A)->(num->real)#real->A) K0` THEN
        REWRITE_TAC[compression_family] THEN
        DISCH_THEN(MP_TAC o SPEC `singular_face p k (sig:(num->real)->A)`) THEN
        ASM_SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `z:(num->real)#real`] THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_TOPSPACE_SIMPLEX_BDPRISM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `i:num = j \/ i < j \/ j < i` STRIP_ASSUME_TAC THENL
       [ARITH_TAC;
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC COMPRESSION_AGREE THEN
        MAP_EVERY EXISTS_TAC
         [`top:A topology`; `K0:((num->real)->A)->(num->real)#real->A`] THEN
        ASM_REWRITE_TAC[];
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC COMPRESSION_AGREE THEN
        MAP_EVERY EXISTS_TAC
         [`top:A topology`; `K0:((num->real)->A)->(num->real)#real->A`] THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:(num->real)#real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN standard_simplex p /\ simplex_min p x = &0
                    ==> (B:(num->real)#real->A)(x,&0) = sig x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:num->real` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:num`; `x:num->real`] SIMPLEX_MIN_EXISTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(x:num->real,&0)`; `k:num`]) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_TOPSPACE_SIMPLEX_BDPRISM; REAL_POS] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `simplex_delete k (x:num->real) IN standard_simplex (p - 1)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SIMPLEX_DELETE_IN THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `compression_family (p - 1,top) (K1:((num->real)->A)->(num->real)#real->A) K0` THEN
    REWRITE_TAC[compression_family] THEN
    DISCH_THEN(MP_TAC o SPEC `singular_face p k (sig:(num->real)->A)`) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_REWRITE_TAC[singular_face; RESTRICTION; o_THM] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SIMPLICIAL_FACE_DELETE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `hep_extension p (sig:(num->real)->A) B` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_HEP_EXTENSION THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[singular_simplex]) THEN ASM_REWRITE_TAC[];
    SIMP_TAC[HEP_EXTENSION_BOTTOM];
    MAP_EVERY X_GEN_TAC [`k:num`; `y:num->real`; `l:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `simplicial_face k (y:num->real) IN standard_simplex p /\
                  simplicial_face k y k = &0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SIMPLICIAL_FACE_IN_STANDARD_SIMPLEX THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC;
        REWRITE_TAC[simplicial_face; LT_REFL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `simplex_min p (simplicial_face k (y:num->real)) = &0` ASSUME_TAC THENL
     [MATCH_MP_TAC SIMPLEX_MIN_ZERO THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) HEP_EXTENSION_SIDE o lhand o snd) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(simplicial_face k (y:num->real),(l:real))`; `k:num`] o
      check (fun th -> is_forall(concl th) && free_in `B:(num->real)#real->A` (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_TOPSPACE_SIMPLEX_BDPRISM; SIMPLEX_DELETE_FACE]]);;

(* ========================================================================= *)
(* Compression in a simply connected space.  Level 1:                       *)
(* each singular 1-simplex is deformed to the constant at the base point,    *)
(* with its vertices moving along chosen paths to the base point.            *)
(* ========================================================================= *)

let STANDARD_SIMPLEX_1_POINT = prove
 (`!x. x IN standard_simplex 1
       ==> (\i. if i = 0 then &1 - x 1 else if i = 1 then x 1 else &0) = x`,
  X_GEN_TAC `v:num->real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP STANDARD_SIMPLEX_1_COORD) THEN STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  UNDISCH_TAC `(v:num->real) IN standard_simplex 1` THEN
  REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

let STANDARD_SIMPLEX_1_VERTICES = prove
 (`!x. x IN standard_simplex 1
       ==> (x 0 = &0 ==> x = (\i. if i = 1 then &1 else &0)) /\
           (x 1 = &0 ==> x = (\i. if i = 0 then &1 else &0))`,
  X_GEN_TAC `x:num->real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP STANDARD_SIMPLEX_1_COORD) THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. 1 < i ==> (x:num->real) i = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:num->real) IN standard_simplex 1` THEN
    SIMP_TAC[standard_simplex; IN_ELIM_THM];
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  (SUBGOAL_THEN `i = 0 \/ i = 1 \/ 1 < i` STRIP_ASSUME_TAC THENL
    [ARITH_TAC; ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
     ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
     ASM_SIMP_TAC[ARITH_RULE `1 < i ==> ~(i = 0) /\ ~(i = 1)`]]));;

let SIMPLICIAL_FACES_0 = prove
 (`simplicial_face 0 (\j. if j = 0 then &1 else &0) = (\i. if i = 1 then &1 else &0) /\
   simplicial_face 1 (\j. if j = 0 then &1 else &0) = (\i. if i = 0 then &1 else &0)`,
  REWRITE_TAC[simplicial_face; FUN_EQ_THM] THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let LEVEL1_HEP = prove
 (`!top a (gam:A->real->A) e.
        (!x. x IN topspace top ==> path_in top (gam x) /\ gam x (&0) = x /\ gam x (&1) = a) /\
        singular_simplex (1,top) e
        ==> ?K. continuous_map (simplex_prism 1,top) K /\
                (!x. x IN standard_simplex 1 ==> K(x,&0) = e x) /\
                (!x l. x IN standard_simplex 1 /\ (x 0 = &0 \/ x 1 = &0) /\
                       &0 <= l /\ l <= &1
                       ==> K(x,l) = gam (e x) l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN standard_simplex 1 ==> (e:(num->real)->A) x IN topspace top`
  ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[singular_simplex; continuous_map;
                                TOPSPACE_STANDARD_SIMPLEX]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\i. if i = 1 then &1 else &0) IN standard_simplex 1 /\
                (\i. if i = 0 then &1 else &0) IN standard_simplex 1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BASIS_IN_STANDARD_SIMPLEX] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`simplex_bdprism 1`; `top:A topology`;
    `\k (z:(num->real)#real). (gam:A->real->A)
             ((e:(num->real)->A)
              (if k = 0 then (\i. if i = 1 then &1 else &0)
               else (\i. if i = 0 then &1 else &0))) (SND z)`;
    `\k. {z | z IN topspace(simplex_bdprism 1) /\ FST z k = &0}`;
    `0..1`] PASTING_LEMMA_EXISTS_CLOSED) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
      X_GEN_TAC `z:(num->real)#real` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`1`; `FST(z:(num->real)#real)`] SIMPLEX_MIN_EXISTS) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:(num->real)#real) IN topspace (simplex_bdprism 1)` THEN
      REWRITE_TAC[IN_TOPSPACE_SIMPLEX_BDPRISM] THEN
      UNDISCH_TAC `simplex_min 1 (FST(z:(num->real)#real)) = FST z k` THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[BDPRISM_PIECE_CLOSED] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN CONJ_TAC THENL
       [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_BDPRISM_COORD] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER;
                    IN_TOPSPACE_SIMPLEX_BDPRISM; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
        SIMP_TAC[];
        REWRITE_TAC[GSYM path_in] THEN
        SUBGOAL_THEN `(e:(num->real)->A)
                        (if k = 0 then (\i. if i = 1 then &1 else &0)
                         else (\i. if i = 0 then &1 else &0)) IN topspace top`
        MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[]]];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `z:(num->real)#real`] THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_TOPSPACE_SIMPLEX_BDPRISM] THEN STRIP_TAC THEN
      ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `FST (z:(num->real)#real) 0 = &0 /\ FST z 1 = &0` MP_TAC THENL
       [UNDISCH_TAC `FST (z:(num->real)#real) i = &0` THEN
        UNDISCH_TAC `FST (z:(num->real)#real) j = &0` THEN
        SUBGOAL_THEN `(i = 0 /\ j = 1) \/ (i = 1 /\ j = 0)` MP_TAC THENL
         [ASM_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP STANDARD_SIMPLEX_1_COORD) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:(num->real)#real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!z. z IN topspace(simplex_bdprism 1)
        ==> (B:(num->real)#real->A) z = gam ((e:(num->real)->A) (FST z)) (SND z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:(num->real)#real` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`1`; `FST(z:(num->real)#real)`] SIMPLEX_MIN_EXISTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:(num->real)#real`; `k:num`]) THEN
    UNDISCH_TAC `(z:(num->real)#real) IN topspace (simplex_bdprism 1)` THEN
    REWRITE_TAC[IN_TOPSPACE_SIMPLEX_BDPRISM; IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `FST (z:(num->real)#real) k = &0` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `k = 0 \/ k = 1` MP_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(SPEC `FST(z:(num->real)#real)` STANDARD_SIMPLEX_1_VERTICES) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `hep_extension 1 (e:(num->real)->A) B` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_HEP_EXTENSION THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[singular_simplex]) THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:num->real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(x:num->real,&0)`) THEN
      ASM_REWRITE_TAC[IN_TOPSPACE_SIMPLEX_BDPRISM; REAL_POS] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]];
    SIMP_TAC[HEP_EXTENSION_BOTTOM];
    MAP_EVERY X_GEN_TAC [`x:num->real`; `l:real`] THEN STRIP_TAC THEN
    (SUBGOAL_THEN `simplex_min 1 x = &0` ASSUME_TAC THENL
      [MATCH_MP_TAC SIMPLEX_MIN_ZERO THEN ASM_MESON_TAC[ARITH_RULE `0 <= 1 /\ 1 <= 1`];
       ALL_TAC] THEN
     W(MP_TAC o PART_MATCH (lhand o rand) HEP_EXTENSION_SIDE o lhand o snd) THEN
     ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `(x:num->real,&0)`) THEN
       ASM_REWRITE_TAC[IN_TOPSPACE_SIMPLEX_BDPRISM; REAL_POS] THEN
       DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
       DISCH_THEN SUBST1_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `(x:num->real,l:real)`) THEN
     ASM_REWRITE_TAC[IN_TOPSPACE_SIMPLEX_BDPRISM])]);;

let LEVEL1_EXISTS = prove
 (`!top a (gam:A->real->A) e.
        simply_connected_space top /\ a IN topspace top /\
        (!x. x IN topspace top ==> path_in top (gam x) /\ gam x (&0) = x /\ gam x (&1) = a) /\
        singular_simplex (1,top) e
        ==> ?K. continuous_map (simplex_prism 1,top) K /\
                (!x. x IN standard_simplex 1 ==> K(x,&0) = e x /\ K(x,&1) = a) /\
                (!x l. x IN standard_simplex 1 /\ (x 0 = &0 \/ x 1 = &0) /\
                       &0 <= l /\ l <= &1
                       ==> K(x,l) = if l <= &1 / &2 then gam (e x) (&2 * l) else a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`; `gam:A->real->A`; `e:(num->real)->A`]
                LEVEL1_HEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:(num->real)#real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN standard_simplex 1 ==> (e:(num->real)->A) x IN topspace top`
  ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[singular_simplex; continuous_map;
                                TOPSPACE_STANDARD_SIMPLEX]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\i. if i = 1 then &1 else &0) IN standard_simplex 1 /\
                (\i. if i = 0 then &1 else &0) IN standard_simplex 1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BASIS_IN_STANDARD_SIMPLEX] THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = RESTRICTION (standard_simplex 1) (\x. (K:(num->real)#real->A) (x,&1))` THEN
  SUBGOAL_THEN `singular_simplex (1,top) (r:(num->real)->A)` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[singular_simplex] THEN
    REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
    SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; TOPSPACE_STANDARD_SIMPLEX; SUBSET_REFL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `simplex_prism 1` THEN
    ASM_REWRITE_TAC[simplex_prism; CONTINUOUS_MAP_PAIRWISE; o_DEF; CONTINUOUS_MAP_ID] THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_CONST] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; IN_UNIV; SUBSET; FORALL_IN_IMAGE;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_in top (simplex_path (r:(num->real)->A)) /\
                simplex_path r (&0) = a /\ simplex_path r (&1) = a`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_IN_SIMPLEX_PATH; SIMPLEX_PATH_ENDS] THEN
    EXPAND_TAC "r" THEN ASM_REWRITE_TAC[RESTRICTION] THEN
    CONJ_TAC THEN FIRST_X_ASSUM(fun th ->
      W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `simplex_path (r:(num->real)->A)`; `\t:real. (a:A)`]
                TOPC_SIMPLY_CONNECTED_HOMOTOPIC_PATHS) THEN
  ASM_REWRITE_TAC[PATH_IN_CONST; homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real#real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z:(num->real)#real.
     if SND z <= &1 / &2 then (K:(num->real)#real->A) (FST z,&2 * SND z)
     else (N:real#real->A) (&2 * SND z - &1,FST z 1)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_CASES_LE THEN
    REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST; CONTINUOUS_MAP_SIMPLEX_PRISM_COORDS_FULL] THEN
    REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `simplex_prism 1` THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o RAND_CONV) [simplex_prism] THEN
      REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
        REWRITE_TAC[simplex_prism] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
        EXISTS_TAC `standard_simplex 1` THEN REWRITE_TAC[CONTINUOUS_MAP_FST];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER;
                    IN_TOPSPACE_SIMPLEX_PRISM] THEN SIMP_TAC[];
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
        REWRITE_TAC[CONTINUOUS_MAP_SIMPLEX_PRISM_COORDS];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM;
                    IN_TOPSPACE_SIMPLEX_PRISM; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                    IN_REAL_INTERVAL] THEN REAL_ARITH_TAC];
      GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                (subtopology euclideanreal (real_interval[&0,&1]))` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
        REWRITE_TAC[CONTINUOUS_MAP_SIMPLEX_PRISM_COORDS];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM;
                    IN_TOPSPACE_SIMPLEX_PRISM; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                    IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
        REWRITE_TAC[CONTINUOUS_MAP_SIMPLEX_PRISM_COORDS];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM;
                    IN_TOPSPACE_SIMPLEX_PRISM; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                    IN_REAL_INTERVAL] THEN
        X_GEN_TAC `z:(num->real)#real` THEN STRIP_TAC THEN
        MP_TAC(SPEC `FST(z:(num->real)#real)` STANDARD_SIMPLEX_1_COORD) THEN
        ASM_SIMP_TAC[]];
      X_GEN_TAC `z:(num->real)#real` THEN REWRITE_TAC[IN_TOPSPACE_SIMPLEX_PRISM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `simplex_path (r:(num->real)->A) (FST(z:(num->real)#real) 1) =
                    K(FST z,&1)` (fun th -> REWRITE_TAC[th]) THEN
      EXPAND_TAC "r" THEN REWRITE_TAC[simplex_path; RESTRICTION] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP STANDARD_SIMPLEX_1_POINT th]) THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:num->real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`x:num->real`; `l:real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o MATCH_MP STANDARD_SIMPLEX_1_COORD) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(x:num->real) 1 = &0 \/ x 1 = &1` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `&2 * l - &1` o
        check (fun th -> is_forall(concl th) && free_in `N:real#real->A` (concl th) &&
                         is_imp(snd(dest_forall(concl th))))) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN
      (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      ASM_SIMP_TAC[]]]);;

(* ========================================================================= *)
(* The natural families of homotopies at levels 0..3                        *)
(* and the compressions of 2- and 3-simplices to edge-constant ones.         *)
(* ========================================================================= *)

let hur_paths = new_definition
 `hur_paths (top,a) (gam:A->real->A) <=>
    (!x. x IN topspace top ==> path_in top (gam x) /\ gam x (&0) = x /\ gam x (&1) = a) /\
    gam a = (\t. a)`;;

let HUR_PATHS_EXIST = prove
 (`!top a:A. path_connected_space top /\ a IN topspace top ==> ?gam. hur_paths (top,a) gam`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?g:A->real->A. !x. x IN topspace top
                                ==> path_in top (g x) /\ g x (&0) = x /\ g x (&1) = a`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `a:A`] o GEN_REWRITE_RULE I [path_connected_space]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\x:A. if x = a then (\t:real. a) else (g:A->real->A) x` THEN
  REWRITE_TAC[hur_paths] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[PATH_IN_CONST]);;

let hur_K0 = new_definition
 `hur_K0 (a:A) (gam:A->real->A) =
    \v:(num->real)->A. \z:(num->real)#real.
       if SND z <= &1 / &2 then gam (v (\i. if i = 0 then &1 else &0)) (&2 * SND z) else a`;;

let hur_K1 = new_definition
 `hur_K1 (top,a) (gam:A->real->A) =
    \e:(num->real)->A.
      if e = RESTRICTION (standard_simplex 1) (\x. a) then (\z:(num->real)#real. a)
      else @K. continuous_map (simplex_prism 1,top) K /\
               (!x. x IN standard_simplex 1 ==> K(x,&0) = e x /\ K(x,&1) = a) /\
               (!x l. x IN standard_simplex 1 /\ (x 0 = &0 \/ x 1 = &0) /\
                      &0 <= l /\ l <= &1
                      ==> K(x,l) = if l <= &1 / &2 then gam (e x) (&2 * l) else a)`;;

let HUR_K1 = prove
 (`!top a (gam:A->real->A) e.
        simply_connected_space top /\ a IN topspace top /\ hur_paths (top,a) gam /\
        singular_simplex (1,top) e
        ==> continuous_map (simplex_prism 1,top) (hur_K1 (top,a) gam e) /\
            (!x. x IN standard_simplex 1
                 ==> hur_K1 (top,a) gam e (x,&0) = e x /\
                     hur_K1 (top,a) gam e (x,&1) = a) /\
            (!x l. x IN standard_simplex 1 /\ (x 0 = &0 \/ x 1 = &0) /\
                   &0 <= l /\ l <= &1
                   ==> hur_K1 (top,a) gam e (x,l) =
                       if l <= &1 / &2 then gam (e x) (&2 * l) else a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hur_paths] THEN STRIP_TAC THEN
  REWRITE_TAC[hur_K1] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUS_MAP_CONST; RESTRICTION] THEN
    SIMP_TAC[] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    CONV_TAC SELECT_CONV THEN MATCH_MP_TAC LEVEL1_EXISTS THEN ASM_REWRITE_TAC[]]);;

let HUR_K1_FAMILY = prove
 (`!top a (gam:A->real->A).
        simply_connected_space top /\ a IN topspace top /\ hur_paths (top,a) gam
        ==> compression_family (1,top) (hur_K1 (top,a) gam) (hur_K0 a gam)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[compression_family] THEN
  X_GEN_TAC `e:(num->real)->A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`; `gam:A->real->A`; `e:(num->real)->A`] HUR_K1) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `y:num->real`; `l:real`] THEN
  REWRITE_TAC[ARITH_RULE `1 - 1 = 0`; STANDARD_SIMPLEX_0; IN_SING] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `j = 0 \/ j = 1` MP_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[SIMPLICIAL_FACES_0] THEN
  (W(MP_TAC o PART_MATCH (lhand o rand) (ASSUME
     `!x l. x IN standard_simplex 1 /\ (x 0 = &0 \/ x 1 = &0) /\ &0 <= l /\ l <= &1
            ==> hur_K1 (top,a) (gam:A->real->A) e (x,l) =
                (if l <= &1 / &2 then gam (e x) (&2 * l) else a)`) o lhand o snd) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[BASIS_IN_STANDARD_SIMPLEX] THEN CONV_TAC NUM_REDUCE_CONV;
     DISCH_THEN SUBST1_TAC]) THEN
  REWRITE_TAC[hur_K0; singular_face; RESTRICTION; o_THM] THEN
  REWRITE_TAC[ARITH_RULE `1 - 1 = 0`; BASIS_IN_STANDARD_SIMPLEX; LE_0] THEN
  REWRITE_TAC[SIMPLICIAL_FACES_0]);;

let hur_K2 = new_definition
 `hur_K2 (top,a) (gam:A->real->A) =
    \sig:(num->real)->A.
      if edgeconst_simplex (2,top) a sig then (\z:(num->real)#real. sig(FST z))
      else @K. continuous_map (simplex_prism 2,top) K /\
               (!x. x IN standard_simplex 2 ==> K(x,&0) = sig x) /\
               (!k y l. k <= 2 /\ y IN standard_simplex 1 /\ &0 <= l /\ l <= &1
                        ==> K(simplicial_face k y,l) =
                            hur_K1 (top,a) gam (singular_face 2 k sig) (y,l))`;;

let EDGECONST_SIMPLEX_2_FACE = prove
 (`!top a (sig:(num->real)->A) k.
        edgeconst_simplex (2,top) a sig /\ k <= 2
        ==> singular_face 2 k sig = RESTRICTION (standard_simplex 1) (\x. a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EDGECONST_SIMPLEX_2] THEN STRIP_TAC THEN
  REWRITE_TAC[singular_face; ARITH_RULE `2 - 1 = 1`; RESTRICTION_EXTENSION; o_THM] THEN
  X_GEN_TAC `y:num->real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLICIAL_FACE_IN_STANDARD_SIMPLEX THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 - 1 = 1`] THEN ARITH_TAC;
    SUBGOAL_THEN `k = 0 \/ k = 1 \/ k = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[simplicial_face] THEN CONV_TAC NUM_REDUCE_CONV]);;

let HUR_K2_FAMILY = prove
 (`!top a (gam:A->real->A).
        simply_connected_space top /\ a IN topspace top /\ hur_paths (top,a) gam
        ==> compression_family (2,top) (hur_K2 (top,a) gam) (hur_K1 (top,a) gam)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[compression_family; ARITH_RULE `2 - 1 = 1`] THEN
  X_GEN_TAC `sig:(num->real)->A` THEN DISCH_TAC THEN REWRITE_TAC[hur_K2] THEN
  COND_CASES_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology (product_topology (:num) (\i. euclideanreal))
                              (standard_simplex 2)` THEN
      REWRITE_TAC[simplex_prism; CONTINUOUS_MAP_FST] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[singular_simplex]) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`k:num`; `y:num->real`; `l:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `singular_face 2 k (sig:(num->real)->A) =
                    RESTRICTION (standard_simplex 1) (\x. a)` SUBST1_TAC THENL
       [MATCH_MP_TAC EDGECONST_SIMPLEX_2_FACE THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[hur_K1] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EDGECONST_SIMPLEX_2]) THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC SIMPLICIAL_FACE_IN_STANDARD_SIMPLEX THEN
        ASM_REWRITE_TAC[ARITH_RULE `2 - 1 = 1`] THEN ASM_ARITH_TAC;
        SUBGOAL_THEN `k = 0 \/ k = 1 \/ k = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[simplicial_face] THEN CONV_TAC NUM_REDUCE_CONV]];
    CONV_TAC SELECT_CONV THEN
    MP_TAC(ISPECL [`2`; `top:A topology`; `hur_K1 (top,a) (gam:A->real->A)`;
                   `hur_K0 (a:A) (gam:A->real->A)`; `sig:(num->real)->A`]
                  COMPRESSION_STEP) THEN
    ASM_SIMP_TAC[HUR_K1_FAMILY; ARITH_RULE `2 - 1 = 1`; LE_REFL]]);;

let hur_K3 = new_definition
 `hur_K3 (top,a) (gam:A->real->A) =
    \tau:(num->real)->A.
      @K. continuous_map (simplex_prism 3,top) K /\
          (!x. x IN standard_simplex 3 ==> K(x,&0) = tau x) /\
          (!k y l. k <= 3 /\ y IN standard_simplex 2 /\ &0 <= l /\ l <= &1
                   ==> K(simplicial_face k y,l) =
                       hur_K2 (top,a) gam (singular_face 3 k tau) (y,l))`;;

let HUR_K3 = prove
 (`!top a (gam:A->real->A) tau.
        simply_connected_space top /\ a IN topspace top /\ hur_paths (top,a) gam /\
        singular_simplex (3,top) tau
        ==> continuous_map (simplex_prism 3,top) (hur_K3 (top,a) gam tau) /\
            (!x. x IN standard_simplex 3 ==> hur_K3 (top,a) gam tau (x,&0) = tau x) /\
            (!k y l. k <= 3 /\ y IN standard_simplex 2 /\ &0 <= l /\ l <= &1
                     ==> hur_K3 (top,a) gam tau (simplicial_face k y,l) =
                         hur_K2 (top,a) gam (singular_face 3 k tau) (y,l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[hur_K3] THEN CONV_TAC SELECT_CONV THEN
  MP_TAC(ISPECL [`3`; `top:A topology`; `hur_K2 (top,a) (gam:A->real->A)`;
                 `hur_K1 (top,a) (gam:A->real->A)`; `tau:(num->real)->A`]
                COMPRESSION_STEP) THEN
  ASM_SIMP_TAC[HUR_K2_FAMILY; ARITH_RULE `3 - 1 = 2`] THEN
  ANTS_TAC THENL [ARITH_TAC; SIMP_TAC[]]);;

let SINGULAR_SIMPLEX_PRISM_TOP = prove
 (`!p top (K:(num->real)#real->A).
        continuous_map (simplex_prism p,top) K
        ==> singular_simplex (p,top) (RESTRICTION (standard_simplex p) (\x. K(x,&1)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[singular_simplex] THEN
  REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
  SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; TOPSPACE_STANDARD_SIMPLEX; SUBSET_REFL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `simplex_prism p` THEN
  ASM_REWRITE_TAC[simplex_prism; CONTINUOUS_MAP_PAIRWISE; o_DEF; CONTINUOUS_MAP_ID] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_CONST] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; IN_UNIV; SUBSET; FORALL_IN_IMAGE;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

let hur_rho2 = new_definition
 `hur_rho2 (top,a) (gam:A->real->A) sig =
    RESTRICTION (standard_simplex 2) (\x. hur_K2 (top,a) gam sig (x,&1))`;;

let hur_rho3 = new_definition
 `hur_rho3 (top,a) (gam:A->real->A) tau =
    RESTRICTION (standard_simplex 3) (\x. hur_K3 (top,a) gam tau (x,&1))`;;

let HUR_K2_TOP = prove
 (`!top a (gam:A->real->A) sig x k.
        simply_connected_space top /\ a IN topspace top /\ hur_paths (top,a) gam /\
        singular_simplex (2,top) sig /\ x IN standard_simplex 2 /\ k <= 2 /\ x k = &0
        ==> hur_K2 (top,a) gam sig (x,&1) = a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`; `gam:A->real->A`] HUR_K2_FAMILY) THEN
  ASM_REWRITE_TAC[compression_family; ARITH_RULE `2 - 1 = 1`] THEN
  DISCH_THEN(MP_TAC o SPEC `sig:(num->real)->A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`k:num`; `simplex_delete k (x:num->real)`; `&1`] o
             CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `simplex_delete k (x:num->real) IN standard_simplex 1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`2`; `k:num`; `x:num->real`] SIMPLEX_DELETE_IN) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 - 1 = 1`] THEN DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SIMPLICIAL_FACE_DELETE; REAL_POS; REAL_LE_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`; `gam:A->real->A`;
                 `singular_face 2 k (sig:(num->real)->A)`] HUR_K1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`2`; `top:A topology`; `k:num`; `sig:(num->real)->A`]
                  SINGULAR_SIMPLEX_SINGULAR_FACE) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 - 1 = 1`] THEN DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
    ASM_SIMP_TAC[]]);;

let HUR_RHO2 = prove
 (`!top a (gam:A->real->A) sig.
        simply_connected_space top /\ a IN topspace top /\ hur_paths (top,a) gam /\
        singular_simplex (2,top) sig
        ==> edgeconst_simplex (2,top) a (hur_rho2 (top,a) gam sig) /\
            (edgeconst_simplex (2,top) a sig ==> hur_rho2 (top,a) gam sig = sig)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[EDGECONST_SIMPLEX_2; hur_rho2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SINGULAR_SIMPLEX_PRISM_TOP THEN REWRITE_TAC[ETA_AX] THEN
      MP_TAC(ISPECL [`top:A topology`; `a:A`; `gam:A->real->A`] HUR_K2_FAMILY) THEN
      ASM_REWRITE_TAC[compression_family] THEN
      DISCH_THEN(MP_TAC o SPEC `sig:(num->real)->A`) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `x:num->real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[RESTRICTION] THEN
      MATCH_MP_TAC HUR_K2_TOP THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ARITH_RULE
        `0 <= 2 /\ 1 <= 2 /\ 2 <= 2`]];
    DISCH_TAC THEN ASM_REWRITE_TAC[hur_rho2; hur_K2; ETA_AX] THEN
    REWRITE_TAC[RESTRICTION_FIXPOINT] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[singular_simplex]) THEN ASM_REWRITE_TAC[IN]]);;

let PIGEONHOLE_4_2 = prove
 (`!i j:num. ?k k'. k <= 3 /\ k' <= 3 /\ ~(k = k') /\ ~(k = i) /\ ~(k = j) /\
                    ~(k' = i) /\ ~(k' = j)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(~(0 = i) /\ ~(0 = j) /\ ~(1 = i) /\ ~(1 = j)) \/
    (~(0 = i) /\ ~(0 = j) /\ ~(2 = i) /\ ~(2 = j)) \/
    (~(0 = i) /\ ~(0 = j) /\ ~(3 = i) /\ ~(3 = j)) \/
    (~(1 = i) /\ ~(1 = j) /\ ~(2 = i) /\ ~(2 = j)) \/
    (~(1 = i) /\ ~(1 = j) /\ ~(3 = i) /\ ~(3 = j)) \/
    (~(2 = i) /\ ~(2 = j) /\ ~(3 = i) /\ ~(3 = j))`
  MP_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_MESON_TAC[ARITH_RULE
   `0 <= 3 /\ 1 <= 3 /\ 2 <= 3 /\ 3 <= 3 /\ ~(0 = 1) /\ ~(0 = 2) /\ ~(0 = 3) /\
    ~(1 = 2) /\ ~(1 = 3) /\ ~(2 = 3)`]);;

let HUR_RHO3 = prove
 (`!top a (gam:A->real->A) tau.
        simply_connected_space top /\ a IN topspace top /\ hur_paths (top,a) gam /\
        singular_simplex (3,top) tau
        ==> edgeconst_simplex (3,top) a (hur_rho3 (top,a) gam tau) /\
            (!k. k <= 3
                 ==> singular_face 3 k (hur_rho3 (top,a) gam tau) =
                     hur_rho2 (top,a) gam (singular_face 3 k tau))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`; `gam:A->real->A`; `tau:(num->real)->A`]
                HUR_K3) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[edgeconst_simplex; hur_rho3] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SINGULAR_SIMPLEX_PRISM_TOP THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:num->real`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[RESTRICTION] THEN
    MP_TAC(SPECL [`i:num`; `j:num`] PIGEONHOLE_4_2) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `k':num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:num->real) k = &0 /\ x k' = &0` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `simplex_delete k (x:num->real) IN standard_simplex 2` ASSUME_TAC THENL
     [MP_TAC(SPECL [`3`; `k:num`; `x:num->real`] SIMPLEX_DELETE_IN) THEN
      ASM_REWRITE_TAC[ARITH_RULE `3 - 1 = 2`] THEN DISCH_THEN MATCH_MP_TAC THEN
      ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
      [SYM(MATCH_MP SIMPLICIAL_FACE_DELETE th)]) o
      check (fun th -> concl th = `(x:num->real) k = &0`)) THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th
      (CONJ (ASSUME `k <= 3`) (CONJ (ASSUME `simplex_delete k (x:num->real) IN standard_simplex 2`)
         (CONJ (REAL_ARITH `&0 <= &1`) (SPEC `&1` REAL_LE_REFL))))]) o
      check (fun th -> is_forall(concl th) &&
                       free_in `hur_K2 (top,a) (gam:A->real->A)` (concl th))) THEN
    MATCH_MP_TAC HUR_K2_TOP THEN
    EXISTS_TAC `if k' < k then k' else k' - 1` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`3`; `top:A topology`; `k:num`; `tau:(num->real)->A`]
                    SINGULAR_SIMPLEX_SINGULAR_FACE) THEN
      ASM_REWRITE_TAC[ARITH_RULE `3 - 1 = 2`] THEN DISCH_THEN MATCH_MP_TAC THEN
      ARITH_TAC;
      ASM_ARITH_TAC;
      REWRITE_TAC[simplex_delete] THEN ASM_CASES_TAC `k':num < k` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(k' - 1 < k) /\ k' - 1 + 1 = k'` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [singular_face] THEN
    REWRITE_TAC[hur_rho3; hur_rho2; ARITH_RULE `3 - 1 = 2`] THEN
    REWRITE_TAC[RESTRICTION_EXTENSION; o_THM] THEN X_GEN_TAC `y:num->real` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `simplicial_face k (y:num->real) IN standard_simplex 3` ASSUME_TAC THENL
     [MATCH_MP_TAC SIMPLICIAL_FACE_IN_STANDARD_SIMPLEX THEN
      ASM_REWRITE_TAC[ARITH_RULE `3 - 1 = 2`] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[RESTRICTION] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Compression of singular 3-chains, and triviality of                      *)
(* the pi_2 class of an edge-constant 2-simplex whose difference with the   *)
(* constant 2-simplex is a boundary.                                         *)
(* ========================================================================= *)

let HUR_RHO3_CHAIN = prove
 (`!top a (gam:A->real->A) w.
        simply_connected_space top /\ a IN topspace top /\ hur_paths (top,a) gam /\
        singular_chain (3,top) w
        ==> frag_support (frag_extend (frag_of o hur_rho3 (top,a) gam) w) SUBSET
              edgeconst_simplex (3,top) a /\
            chain_boundary 3 (frag_extend (frag_of o hur_rho3 (top,a) gam) w) =
            frag_extend (frag_of o hur_rho2 (top,a) gam) (chain_boundary 3 w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[singular_chain] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SPEC_TAC(`w:((num->real)->A)frag`,`w:((num->real)->A)frag`) THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN CONJ_TAC THENL
   [REWRITE_TAC[FRAG_EXTEND_0; FRAG_SUPPORT_0; EMPTY_SUBSET; CHAIN_BOUNDARY_0];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `tau:(num->real)->A` THEN REWRITE_TAC[IN] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `a:A`; `gam:A->real->A`; `tau:(num->real)->A`]
                  HUR_RHO3) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[FRAG_EXTEND_OF; o_THM; FRAG_SUPPORT_OF; SING_SUBSET] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[IN]; ALL_TAC] THEN
    REWRITE_TAC[PI2_CHAIN_BOUNDARY_3; FRAG_EXTEND_ADD; FRAG_EXTEND_NEG;
                FRAG_EXTEND_OF; o_THM] THEN
    ASM_SIMP_TAC[ARITH_RULE `0 <= 3 /\ 1 <= 3 /\ 2 <= 3 /\ 3 <= 3`];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c1:((num->real)->A)frag`; `c2:((num->real)->A)frag`] THEN
  STRIP_TAC THEN REWRITE_TAC[FRAG_EXTEND_SUB; CHAIN_BOUNDARY_SUB] THEN
  ASM_REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH lhand FRAG_SUPPORT_SUB o lhand o snd) THEN
  ASM SET_TAC[]);;

let HUR_PI2_CLASS_TRIVIAL = prove
 (`!top a (sig:(num->real)->A) w.
        simply_connected_space top /\ a IN topspace top /\
        edgeconst_simplex (2,top) a sig /\ singular_chain (3,top) w /\
        chain_boundary 3 w =
        frag_sub (frag_of sig) (frag_of (RESTRICTION (standard_simplex 2) (\x. a)))
        ==> pi2_class top a (sig o pi2_tri) = group_id(pi2_group(top,a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`] HUR_PATHS_EXIST) THEN
  ASM_SIMP_TAC[TOPC_SIMPLY_CONNECTED_IMP_PATH_CONNECTED] THEN
  DISCH_THEN(X_CHOOSE_TAC `gam:A->real->A`) THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`] PI2_HUREWICZ_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:((num->real)->A)frag->(real#real->A)->bool`
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`; `gam:A->real->A`; `w:((num->real)->A)frag`]
                HUR_RHO3_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `edgeconst_simplex (2,top) (a:A) (RESTRICTION (standard_simplex 2) (\x. a))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[EDGECONST_SIMPLEX_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. edgeconst_simplex (2,top) (a:A) s ==> hur_rho2 (top,a) (gam:A->real->A) s = s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `a:A`; `gam:A->real->A`; `s:(num->real)->A`]
                  HUR_RHO2) THEN
    ASM_MESON_TAC[EDGECONST_SIMPLEX_IMP_SINGULAR];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `frag_extend (frag_of o hur_rho3 (top,a) (gam:A->real->A)) w`) THEN
  ASM_REWRITE_TAC[FRAG_EXTEND_SUB; FRAG_EXTEND_OF; o_THM] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `frag_sub (frag_of sig) (frag_of (RESTRICTION (standard_simplex 2) (\x. a))) =
    group_mul (free_abelian_group (edgeconst_simplex (2,top) (a:A))) (frag_of sig)
      (group_inv (free_abelian_group (edgeconst_simplex (2,top) a))
         (frag_of (RESTRICTION (standard_simplex 2) (\x. a))))`
  SUBST1_TAC THENL [REWRITE_TAC[FREE_ABELIAN_GROUP] THEN CONV_TAC FRAG_MODULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `sig IN edgeconst_simplex (2,top) (a:A) /\
    RESTRICTION (standard_simplex 2) (\x. a) IN edgeconst_simplex (2,top) (a:A)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[IN]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP GROUP_HOMOMORPHISM_MUL th;
                                     MATCH_MP GROUP_HOMOMORPHISM_INV th;
                                     GROUP_INV; FRAG_OF_IN_FREE_ABELIAN_GROUP]) THEN
  ASM_SIMP_TAC[PI2_CLASS_EDGECONST_CONST; GROUP_INV_ID] THEN
  SUBGOAL_THEN `pi2_class top a ((sig:(num->real)->A) o pi2_tri) IN
                group_carrier(pi2_group(top,a))` ASSUME_TAC THENL
   [MATCH_MP_TAC PI2_CLASS_IN_CARRIER THEN MATCH_MP_TAC EDGECONST_SIMPLEX_PI2_MAP THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[GROUP_MUL_RID]]);;

(* ========================================================================= *)
(* A map from the square onto the 2-sphere collapsing                       *)
(* the boundary to the north pole.  With u, v the coordinates centred at    *)
(* (1/2,1/2) and d = 1 - 2 max(|u|,|v|), the point (u,v)/d of the plane is   *)
(* sent to the sphere by inverse stereographic projection; the result,       *)
(* (2du, 2dv, u^2 + v^2 - d^2) / (u^2 + v^2 + d^2), is continuous on the    *)
(* whole square, constant on the boundary and injective on the interior.    *)
(* ========================================================================= *)

let HUR_MAX_RMUL = prove
 (`!a b c. &0 <= c ==> max a b * c = max (a * c) (b * c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_max] THEN ASM_CASES_TAC `a:real <= b` THENL
   [SUBGOAL_THEN `a * c <= b * c` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `b * c <= a * c` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    ASM_REAL_ARITH_TAC]);;

let HUR_ABS_MUL_POS = prove
 (`!u d. &0 < d ==> abs u * d = abs(u * d)`,
  SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < d ==> abs d = d`]);;

let HUR_SQSPHERE_INJ_ARITH = prove
 (`!u1 v1 d1 u2 v2 d2.
        &2 * max (abs u1) (abs v1) = &1 - d1 /\ &0 < d1 /\
        &2 * max (abs u2) (abs v2) = &1 - d2 /\ &0 < d2 /\
        &2 * d1 * u1 / (u1 pow 2 + v1 pow 2 + d1 pow 2) =
        &2 * d2 * u2 / (u2 pow 2 + v2 pow 2 + d2 pow 2) /\
        &2 * d1 * v1 / (u1 pow 2 + v1 pow 2 + d1 pow 2) =
        &2 * d2 * v2 / (u2 pow 2 + v2 pow 2 + d2 pow 2) /\
        (u1 pow 2 + v1 pow 2 - d1 pow 2) / (u1 pow 2 + v1 pow 2 + d1 pow 2) =
        (u2 pow 2 + v2 pow 2 - d2 pow 2) / (u2 pow 2 + v2 pow 2 + d2 pow 2)
        ==> u1 = u2 /\ v1 = v2`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ABBREV_TAC [`r1 = u1 pow 2 + v1 pow 2 + d1 pow 2`;
                        `r2 = u2 pow 2 + v2 pow 2 + d2 pow 2`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r1 /\ &0 < r2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r1"; "r2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 < c ==> &0 < a + b + c`) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `d1 pow 2 * r2 = d2 pow 2 * r1` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(u1 pow 2 + v1 pow 2 - d1 pow 2) / r1 = (u2 pow 2 + v2 pow 2 - d2 pow 2) / r2`;
      `u1 pow 2 + v1 pow 2 + d1 pow 2 = r1`; `u2 pow 2 + v2 pow 2 + d2 pow 2 = r2`;
      `&0 < r1`; `&0 < r2`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `u1 * d2 = u2 * d1 /\ v1 * d2 = v2 * d1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`&2 * d1 * u1 / r1 = &2 * d2 * u2 / r2`; `&2 * d1 * v1 / r1 = &2 * d2 * v2 / r2`;
      `d1 pow 2 * r2 = d2 pow 2 * r1`; `&0 < r1`; `&0 < r2`; `&0 < d1`; `&0 < d2`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs u1 * d2 = abs u2 * d1 /\ abs v1 * d2 = abs v2 * d1`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[HUR_ABS_MUL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `max (abs u1) (abs v1) * d2 = max (abs u2) (abs v2) * d1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[HUR_MAX_RMUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `d1:real = d2` SUBST_ALL_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`max (abs u1) (abs v1) * d2 = max (abs u2) (abs v2) * d1`;
      `&2 * max (abs u1) (abs v1) = &1 - d1`; `&2 * max (abs u2) (abs v2) = &1 - d2`] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  UNDISCH_TAC `u1 * d2 = u2 * d2` THEN UNDISCH_TAC `v1 * d2 = v2 * d2` THEN
  ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL; REAL_LT_IMP_NZ]);;

let HUR_SQSPHERE_SURJ_ARITH = prove
 (`!w1 w2 w3. w1 pow 2 + w2 pow 2 + w3 pow 2 = &1 /\ ~(w3 = &1)
       ==> ?u v d. &2 * max (abs u) (abs v) = &1 - d /\ &0 < d /\
                   abs u < &1 / &2 /\ abs v < &1 / &2 /\
                   &2 * d * u / (u pow 2 + v pow 2 + d pow 2) = w1 /\
                   &2 * d * v / (u pow 2 + v pow 2 + d pow 2) = w2 /\
                   (u pow 2 + v pow 2 - d pow 2) / (u pow 2 + v pow 2 + d pow 2) = w3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - w3` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs w3 <= abs(&1)` MP_TAC THENL
     [REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MP_TAC(SPEC `w1:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `w2:real` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `~(w3 = &1)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `t1 = w1 / (&1 - w3)` THEN ABBREV_TAC `t2 = w2 / (&1 - w3)` THEN
  ABBREV_TAC `m = &1 + &2 * max (abs t1) (abs t2)` THEN
  SUBGOAL_THEN `abs(t1:real) <= max (abs t1) (abs t2) /\
                abs(t2:real) <= max (abs t1) (abs t2) /\
                &2 * max (abs t1) (abs t2) = m - &1 /\ &0 < m`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv m` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t1 * inv m`; `t2 * inv m`; `inv m`] THEN
  SUBGOAL_THEN `abs(t1 * inv m) = abs t1 * inv m /\ abs(t2 * inv m) = abs t2 * inv m`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < m ==> abs m = m`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM HUR_MAX_RMUL; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `max (abs t1) (abs t2) * inv m = &1 / &2 - inv m / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `&2 * max (abs t1) (abs t2) = m - &1` THEN
    UNDISCH_TAC `&0 < m` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs t1 * inv m <= max (abs t1) (abs t2) * inv m /\
                abs t2 * inv m <= max (abs t1) (abs t2) * inv m`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXPAND_TAC ["t1"; "t2"] THEN
  MAP_EVERY UNDISCH_TAC
   [`w1 pow 2 + w2 pow 2 + w3 pow 2 = &1`; `&0 < &1 - w3`; `&0 < m`] THEN
  CONV_TAC REAL_FIELD);;

let HUR_SQSPHERE_NORM_ARITH = prove
 (`!u v d r. r = u pow 2 + v pow 2 + d pow 2 /\ &0 < r
       ==> (&2 * d * u / r) * (&2 * d * u / r) + (&2 * d * v / r) * (&2 * d * v / r) +
           ((u pow 2 + v pow 2 - d pow 2) / r) * ((u pow 2 + v pow 2 - d pow 2) / r) = &1`,
  CONV_TAC REAL_FIELD);;

let hur_sqd = new_definition
 `hur_sqd (x:real#real) =
    &1 - &2 * max (abs(FST x - &1 / &2)) (abs(SND x - &1 / &2))`;;

let hur_sqr = new_definition
 `hur_sqr (x:real#real) =
    (FST x - &1 / &2) pow 2 + (SND x - &1 / &2) pow 2 + hur_sqd x pow 2`;;

let hur_sqsphere = new_definition
 `hur_sqsphere (x:real#real) =
    vector [&2 * hur_sqd x * (FST x - &1 / &2) / hur_sqr x;
            &2 * hur_sqd x * (SND x - &1 / &2) / hur_sqr x;
            ((FST x - &1 / &2) pow 2 + (SND x - &1 / &2) pow 2 - hur_sqd x pow 2) /
            hur_sqr x]:real^3`;;

let HUR_SQR_POS = prove
 (`!x. &0 < hur_sqr x`,
  GEN_TAC THEN REWRITE_TAC[hur_sqr; hur_sqd] THEN
  SPEC_TAC(`FST(x:real#real) - &1 / &2`,`u:real`) THEN
  SPEC_TAC(`SND(x:real#real) - &1 / &2`,`v:real`) THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `u = &0 /\ v = &0` THENL
   [ASM_REWRITE_TAC[REAL_ABS_0; real_max; REAL_LE_REFL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= c /\ (&0 < a /\ &0 <= b \/ &0 <= a /\ &0 < b) ==> &0 < a + b + c`) THEN
    REWRITE_TAC[REAL_LE_POW_2; REAL_LT_POW_2] THEN ASM_MESON_TAC[]]);;

let HUR_SQSPHERE_IN_SPHERE = prove
 (`!x. hur_sqsphere x IN sphere(vec 0:real^3,&1)`,
  GEN_TAC THEN REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; DOT_3; hur_sqsphere; VECTOR_3] THEN
  MATCH_MP_TAC HUR_SQSPHERE_NORM_ARITH THEN REWRITE_TAC[HUR_SQR_POS] THEN
  REWRITE_TAC[hur_sqr]);;

let CONTINUOUS_MAP_HUR_SQD = prove
 (`continuous_map (sqtop,euclideanreal) (\x. hur_sqd x)`,
  REWRITE_TAC[hur_sqd] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
  REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST; CONTINUOUS_MAP_SQTOP_FST_SND;
              CONTINUOUS_MAP_SQTOP_FST]);;

let CONTINUOUS_MAP_HUR_SQR = prove
 (`continuous_map (sqtop,euclideanreal) (\x. hur_sqr x)`,
  REWRITE_TAC[hur_sqr] THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN CONJ_TAC) THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_POW THEN
  REWRITE_TAC[CONTINUOUS_MAP_HUR_SQD; REWRITE_RULE[ETA_AX] CONTINUOUS_MAP_HUR_SQD] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
  REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST; CONTINUOUS_MAP_SQTOP_FST_SND;
              CONTINUOUS_MAP_SQTOP_FST]);;

(* Continuity of real functions on the square built from the coordinates,  *)
(* constants, hur_sqd and hur_sqr by sums, differences, products, powers  *)
(* and division by hur_sqr.                                                 *)

let HUR_RCONT_TAC =
  let base = [CONTINUOUS_MAP_REAL_CONST; CONTINUOUS_MAP_HUR_SQD; CONTINUOUS_MAP_HUR_SQR;
              REWRITE_RULE[ETA_AX] CONTINUOUS_MAP_HUR_SQD;
              REWRITE_RULE[ETA_AX] CONTINUOUS_MAP_HUR_SQR] @
             CONJUNCTS CONTINUOUS_MAP_SQTOP_FST_SND @ CONJUNCTS CONTINUOUS_MAP_SQTOP_FST in
  let rec tac g =
    (FIRST (map MATCH_ACCEPT_TAC base) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN CONJ_TAC THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_POW THEN tac) ORELSE
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_DIV THEN
      CONJ_TAC THENL [tac; CONJ_TAC THENL
        [tac; MESON_TAC[HUR_SQR_POS; REAL_LT_IMP_NZ]]])) g in
  tac;;

let CONTINUOUS_MAP_HUR_SQSPHERE = prove
 (`continuous_map (sqtop,subtopology euclidean (sphere(vec 0:real^3,&1))) hur_sqsphere`,
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE;
              HUR_SQSPHERE_IN_SPHERE] THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_REAL; DIMINDEX_3; FORALL_3] THEN
  REWRITE_TAC[hur_sqsphere; VECTOR_3] THEN REPEAT CONJ_TAC THEN HUR_RCONT_TAC);;

let HUR_SQD_ZERO = prove
 (`!x. x IN topspace sqtop ==> &0 <= hur_sqd x /\ (hur_sqd x = &0 <=> sqbd x)`,
  GEN_TAC THEN REWRITE_TAC[IN_TOPSPACE_SQTOP; hur_sqd; sqbd] THEN REAL_ARITH_TAC);;

let HUR_SQSPHERE_NORTH = prove
 (`!x. x IN topspace sqtop ==> (hur_sqsphere x = vector[&0;&0;&1] <=> sqbd x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HUR_SQD_ZERO) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[hur_sqsphere; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  MP_TAC(SPEC `x:real#real` HUR_SQR_POS) THEN REWRITE_TAC[hur_sqr] THEN
  SPEC_TAC(`hur_sqd x`,`d:real`) THEN
  SPEC_TAC(`FST(x:real#real) - &1 / &2`,`u:real`) THEN
  SPEC_TAC(`SND(x:real#real) - &1 / &2`,`v:real`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    UNDISCH_TAC `(u pow 2 + v pow 2 - d pow 2) / (u pow 2 + v pow 2 + d pow 2) = &1` THEN
    UNDISCH_TAC `&0 < u pow 2 + v pow 2 + d pow 2` THEN CONV_TAC REAL_FIELD;
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `&0 < u pow 2 + v pow 2 + &0 pow 2` THEN CONV_TAC REAL_FIELD]);;

let HUR_SQSPHERE_INJ = prove
 (`!x y. x IN topspace sqtop /\ y IN topspace sqtop /\ ~sqbd x /\ ~sqbd y /\
         hur_sqsphere x = hur_sqsphere y
         ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real#real` HUR_SQD_ZERO) THEN MP_TAC(SPEC `y:real#real` HUR_SQD_ZERO) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `hur_sqsphere x = hur_sqsphere y` THEN
  REWRITE_TAC[hur_sqsphere; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; hur_sqr] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`FST(x:real#real) - &1 / &2`; `SND(x:real#real) - &1 / &2`; `hur_sqd x`;
                `FST(y:real#real) - &1 / &2`; `SND(y:real#real) - &1 / &2`; `hur_sqd y`]
               HUR_SQSPHERE_INJ_ARITH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[hur_sqd] THEN REAL_ARITH_TAC) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `a - &1 / &2 = b - &1 / &2 <=> a = b`] THEN
    REWRITE_TAC[GSYM PAIR_EQ; PAIR]]);;

let HUR_SQSPHERE_SURJ = prove
 (`IMAGE hur_sqsphere (topspace sqtop) = sphere(vec 0:real^3,&1)`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE; HUR_SQSPHERE_IN_SPHERE] THEN
  X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; DOT_3; IN_IMAGE] THEN
  DISCH_TAC THEN ASM_CASES_TAC `(w:real^3)$3 = &1` THENL
   [EXISTS_TAC `(&0,&0)` THEN
    REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC(SPEC `(&0,&0)` HUR_SQSPHERE_NORTH) THEN
    REWRITE_TAC[IN_TOPSPACE_SQTOP; sqbd] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(w:real^3)$1 * w$1 = &0 /\ w$2 * w$2 = &0` MP_TAC THENL
     [MP_TAC(SPEC `(w:real^3)$1` REAL_LE_SQUARE) THEN
      MP_TAC(SPEC `(w:real^3)$2` REAL_LE_SQUARE) THEN
      UNDISCH_TAC `(w:real^3)$1 * w$1 + w$2 * w$2 + w$3 * w$3 = &1` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ENTIRE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`(w:real^3)$1`; `(w:real^3)$2`; `(w:real^3)$3`] HUR_SQSPHERE_SURJ_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `v:real`; `d:real`] THEN STRIP_TAC THEN
  EXISTS_TAC `(u + &1 / &2,v + &1 / &2)` THEN
  REWRITE_TAC[IN_TOPSPACE_SQTOP] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[hur_sqsphere; hur_sqr; hur_sqd; REAL_ARITH `(u + &1 / &2) - &1 / &2 = u`] THEN
  SUBGOAL_THEN `&1 - &2 * max (abs u) (abs v) = d` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3]);;

(* ========================================================================= *)
(* Descending a null-homotopy of f o hur_sqsphere rel                        *)
(* the boundary to a null-homotopy of f, and Hurewicz injectivity in degree *)
(* 2 for maps of the 2-sphere into simply connected spaces (G4).            *)
(* ========================================================================= *)

let COMPACT_SPACE_SQTOP = prove
 (`compact_space sqtop`,
  REWRITE_TAC[sqtop; COMPACT_SPACE_PROD_TOPOLOGY] THEN DISJ2_TAC THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
  REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL]);;

let HUR_IMAGE_SND_CROSS = prove
 (`!(f:B->C) (s:A->bool) t.
        IMAGE (\z. FST z,f(SND z)) (s CROSS t) = s CROSS IMAGE f t`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; FORALL_PAIR_THM; IN_CROSS;
              PAIR_EQ] THEN
  MESON_TAC[]);;

let HUR_SQSPHERE_DESCENT = prove
 (`!top (g:real^3->A) a.
        continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),top) g /\
        pi2_homotopic top a (g o hur_sqsphere) (\x. a)
        ==> homotopic_with (\h. T) (subtopology euclidean (sphere(vec 0:real^3,&1)),top)
                           g (\x. a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[pi2_homotopic] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[homotopic_with; o_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real#(real#real)->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`prod_topology (subtopology euclideanreal (real_interval[&0,&1])) sqtop`;
    `prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                   (subtopology euclidean (sphere(vec 0:real^3,&1)))`;
    `top:A topology`;
    `\z:real#(real#real). (FST z,hur_sqsphere(SND z))`;
    `H:real#(real#real)->A`] QUOTIENT_MAP_LIFT_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_QUOTIENT_MAP THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[COMPACT_SPACE_PROD_TOPOLOGY; COMPACT_SPACE_SQTOP] THEN DISJ2_TAC THEN
        MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
        REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL];
        REWRITE_TAC[HAUSDORFF_SPACE_PROD_TOPOLOGY] THEN DISJ2_TAC THEN
        CONJ_TAC THEN MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
        REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEANREAL; HAUSDORFF_SPACE_EUCLIDEAN];
        REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX; CONTINUOUS_MAP_FST] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `sqtop` THEN
        REWRITE_TAC[CONTINUOUS_MAP_SND; CONTINUOUS_MAP_HUR_SQSPHERE];
        REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; HUR_IMAGE_SND_CROSS; HUR_SQSPHERE_SURJ;
                    TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]];
      REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_CROSS; FST; SND] THEN
      X_GEN_TAC `t1:real` THEN DISCH_TAC THEN X_GEN_TAC `x1:real#real` THEN DISCH_TAC THEN
      X_GEN_TAC `t2:real` THEN DISCH_TAC THEN X_GEN_TAC `x2:real#real` THEN DISCH_TAC THEN
      REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
      ASM_CASES_TAC `sqbd x1` THENL
       [SUBGOAL_THEN `sqbd x2` ASSUME_TAC THENL
         [ASM_MESON_TAC[HUR_SQSPHERE_NORTH]; ALL_TAC] THEN
        ASM_MESON_TAC[];
        SUBGOAL_THEN `~sqbd x2` ASSUME_TAC THENL
         [ASM_MESON_TAC[HUR_SQSPHERE_NORTH]; ALL_TAC] THEN
        SUBGOAL_THEN `x1:real#real = x2` (fun th -> REWRITE_TAC[th]) THEN
        MATCH_MP_TAC HUR_SQSPHERE_INJ THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real#real^3->A` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  MAP_EVERY EXISTS_TAC [`\y:real^3. (G:real#real^3->A)(&0,y)`;
                        `\y:real^3. (G:real#real^3->A)(&1,y)`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[homotopic_with] THEN EXISTS_TAC `G:real#real^3->A` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; GSYM HUR_SQSPHERE_SURJ] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real#real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM((fun th ->
      MP_TAC(SPEC `(&0,x):real#(real#real)` th) THEN
      MP_TAC(SPEC `(&1,x):real#(real#real)` th)) o
      check (fun th -> free_in `G:real#real^3->A` (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; IN_CROSS; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                    IN_REAL_INTERVAL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
    REWRITE_TAC[]]);;

let EDGECONST_SIMPLEX_SIMPLEX_MAP = prove
 (`!p top top' a (f:A->B) sig.
        edgeconst_simplex (p,top) a sig /\ continuous_map (top,top') f
        ==> edgeconst_simplex (p,top') (f a) (simplex_map p f sig)`,
  REWRITE_TAC[edgeconst_simplex] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[SINGULAR_SIMPLEX_SIMPLEX_MAP];
    ASM_REWRITE_TAC[simplex_map; RESTRICTION; o_THM] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let HUR_EDGECONST_CYCLE = prove
 (`!top a (sig:(num->real)->A).
        a IN topspace top /\ edgeconst_simplex (2,top) a sig
        ==> singular_relcycle (2,top,{})
              (frag_sub (frag_of sig) (frag_of (RESTRICTION (standard_simplex 2) (\x. a))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `edgeconst_simplex (2,top) (a:A) (RESTRICTION (standard_simplex 2) (\x. a))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[EDGECONST_SIMPLEX_CONST]; ALL_TAC] THEN
  REWRITE_TAC[SINGULAR_CYCLE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SINGULAR_CHAIN_SUB THEN REWRITE_TAC[SINGULAR_CHAIN_OF] THEN
    ASM_MESON_TAC[EDGECONST_SIMPLEX_IMP_SINGULAR];
    ALL_TAC] THEN
  REWRITE_TAC[CHAIN_BOUNDARY_SUB; CHAIN_BOUNDARY_OF; ARITH_EQ] THEN
  MATCH_MP_TAC(FRAG_MODULE `x:((num->real)->A)frag = y ==> frag_sub x y = frag_0`) THEN
  MATCH_MP_TAC(MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
  REWRITE_TAC[IN_NUMSEG] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `RESTRICTION (standard_simplex 1) (\x. a:A)` THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC SYM_CONV] THEN
  MATCH_MP_TAC EDGECONST_SIMPLEX_2_FACE THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

let ATOP_HUREWICZ2 = prove
 (`ATOP_HUREWICZ2_STATEMENT (:A)`,
  REWRITE_TAC[ATOP_HUREWICZ2_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `f:real^3->A`] THEN STRIP_TAC THEN
  EXISTS_TAC `(f:real^3->A)(vector[&0;&0;&1])` THEN
  MATCH_MP_TAC HUR_SQSPHERE_DESCENT THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a = (f:real^3->A)(vector[&0;&0;&1])` THEN
  SUBGOAL_THEN `(vector[&0;&0;&1]:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; DOT_3; VECTOR_3] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
                MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pi2_map (subtopology euclidean (sphere(vec 0:real^3,&1))) (vector[&0;&0;&1])
            hur_sqsphere`
  ASSUME_TAC THENL
   [REWRITE_TAC[pi2_map; CONTINUOUS_MAP_HUR_SQSPHERE] THEN
    MESON_TAC[HUR_SQSPHERE_NORTH];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PI2_MAP_TRI_FACTOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `sp:(num->real)->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^3,&1))`;
                 `vector[&0;&0;&1]:real^3`; `sp:(num->real)->real^3`]
                HUR_EDGECONST_CYCLE) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `homologous_rel (2,subtopology euclidean (sphere(vec 0:real^3,&1)),{})
      (frag_sub (frag_of sp)
         (frag_of (RESTRICTION (standard_simplex 2) (\x. vector[&0;&0;&1]:real^3))))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[homology_group; RELATIVE_HOMOLOGY_GROUP; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HOM_INDUCED_CHAIN_MAP; IMAGE_CLAUSES; EMPTY_SUBSET] THEN
  REWRITE_TAC[homology_group; RELATIVE_HOMOLOGY_GROUP; HOMOLOGOUS_REL_EQ_RELBOUNDARY] THEN
  REWRITE_TAC[SINGULAR_BOUNDARY; ARITH_RULE `2 + 1 = 3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:((num->real)->A)frag` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `simplex_map 2 (f:real^3->A)
      (RESTRICTION (standard_simplex 2) (\x. vector[&0;&0;&1]:real^3)) =
    RESTRICTION (standard_simplex 2) (\x. a)`
  ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[simplex_map; RESTRICTION_EXTENSION; o_THM] THEN
    SIMP_TAC[RESTRICTION];
    ALL_TAC] THEN
  SUBGOAL_THEN `edgeconst_simplex (2,top) (a:A) (simplex_map 2 (f:real^3->A) sp)`
  ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC EDGECONST_SIMPLEX_SIMPLEX_MAP THEN
    EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^3,&1))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `a:A`; `simplex_map 2 (f:real^3->A) sp`;
                 `w:((num->real)->A)frag`] HUR_PI2_CLASS_TRIVIAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `chain_boundary 3 w =
      chain_map 2 (f:real^3->A)
       (frag_sub (frag_of sp)
          (frag_of (RESTRICTION (standard_simplex 2) (\x. vector[&0;&0;&1]:real^3))))` THEN
    ASM_REWRITE_TAC[CHAIN_MAP_SUB; CHAIN_MAP_OF];
    ALL_TAC] THEN
  SUBGOAL_THEN `pi2_map top (a:A) ((f:real^3->A) o hur_sqsphere)` ASSUME_TAC THENL
   [REWRITE_TAC[pi2_map] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^3,&1))` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_HUR_SQSPHERE];
      EXPAND_TAC "a" THEN REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
      AP_TERM_TAC THEN ASM_MESON_TAC[HUR_SQSPHERE_NORTH]];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP PI2_CLASS_EQ th)]) THEN
  SUBGOAL_THEN
   `pi2_class top (a:A) ((f:real^3->A) o hur_sqsphere) =
    pi2_class top a (simplex_map 2 f sp o pi2_tri)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC PI2_CLASS_EQ_ON THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real#real` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[o_THM; simplex_map; RESTRICTION; PI2_TRI_IN_STANDARD_SIMPLEX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PI2_GROUP]);;


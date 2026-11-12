(* ========================================================================= *)
(* pc_moi_lt_nsys: resimplicialization and the first normal system of the    *)
(* loop theorem (Moise pp.187-188 (1)-(4)).  Main theorems (statements of    *)
(* pc_moi_loop_stmt.ml):                                                     *)
(*   RESIMPLICIAL = MOI_LT_RESIMPLICIAL                                       *)
(*   NSYS         = MOI_LT_NSYS                                               *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_fnd_rn.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Every triangle of a combinatorial 3-manifold with boundary lies          *)
(* in one or two tetrahedra, in exactly one iff it is a boundary triangle.  *)
(* ========================================================================= *)

let MOI_LNS_TRIANGLE_TETS = prove
 (`!(c:(real^N->bool)->bool) t.
     combinatorial_manifold_with_boundary 3 c /\ t IN c /\ aff_dim t = &2
     ==> FINITE {r | r IN c /\ aff_dim r = &3 /\ t SUBSET r} /\
         (CARD {r | r IN c /\ aff_dim r = &3 /\ t SUBSET r} = 1 \/
          CARD {r | r IN c /\ aff_dim r = &3 /\ t SUBSET r} = 2) /\
         (CARD {r | r IN c /\ aff_dim r = &3 /\ t SUBSET r} = 1 <=>
          t IN boundary_complex c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN
    ASM_MESON_TAC[INT_ARITH `~(--(&1):int = &2)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {r | r IN c /\ aff_dim r = &3 /\ (t:real^N->bool) SUBSET r}`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{s | s IN c /\ (x:real^N) IN s}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_STAR_FINITE THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `1 <= CARD {r | r IN c /\ aff_dim r = &3 /\ (t:real^N->bool) SUBSET r} /\
    CARD {r | r IN c /\ aff_dim r = &3 /\ t SUBSET r} <= 2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
      MOI_FM3_LF_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
      MOI_FM3_LINK_OPP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
      MOI_FM3_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `t = convex hull ((v:real^N) INSERT e)` THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `aff_dim (e:real^N->bool) = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `aff_dim (convex hull ((v:real^N) INSERT e)) = aff_dim e + &1` THEN
      UNDISCH_TAC `aff_dim (convex hull ((v:real^N) INSERT e)) = &2` THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `pl_sphere 2 (UNIONS (simplicial_link c (v:real^N))) \/
      pl_ball 2 (UNIONS (simplicial_link c v))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`;
                   `&2:int`; `&3:int`] MOI_FM3_LINK_CARD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
      MOI_FRN_LINK_EDGE_COFACES) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `1 <= CARD {r | r IN c /\ aff_dim r = &3 /\ (t:real^N->bool) SUBSET r}` THEN
    UNDISCH_TAC `CARD {r | r IN c /\ aff_dim r = &3 /\ (t:real^N->bool) SUBSET r} <= 2` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[boundary_complex; IN_ELIM_THM; complex_boundary] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!(t:real^N->bool) u. t IN u ==> t SUBSET UNIONS u`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[boundary_complex; IN_ELIM_THM; complex_boundary] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(relative_interior (t:real^N->bool) = {})` MP_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  SUBGOAL_THEN
   `(x:real^N) IN UNIONS {s | s IN c /\ aff_dim s = &2 /\
                              CARD {r | r IN c /\ aff_dim r = &3 /\ s SUBSET r} = 1}`
  MP_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t:real^N->bool = s` SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Maps that are affine on a set: images of affine combinations,            *)
(* preimages of faces are faces, images of relative interiors.              *)
(* ========================================================================= *)

let MOI_LNS_AFFINE_COMBO = prove
 (`!(f:real^M->real^N) l y s a b u.
     linear l /\ (!x. x IN s ==> f x = l x + y) /\
     a IN s /\ b IN s /\ (&1 - u) % a + u % b IN s
     ==> f((&1 - u) % a + u % b) = (&1 - u) % f a + u % f b`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th;
                                    MATCH_MP LINEAR_CMUL th]) THEN
  VECTOR_ARITH_TAC);;

let MOI_LNS_FACE_PREIMAGE = prove
 (`!(f:real^M->real^N) l y s t.
     linear l /\ (!x. x IN s ==> f x = l x + y) /\ convex s /\
     t face_of IMAGE f s
     ==> {x | x IN s /\ f x IN t} face_of s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FACE_OF_IMP_CONVEX) THEN
  REWRITE_TAC[face_of] THEN REPEAT CONJ_TAC THENL
   [SET_TAC[];
    REWRITE_TAC[CONVEX_ALT; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `u:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(&1 - u) % a + u % b IN (s:real^M->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONVEX_ALT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `l:real^M->real^N`; `y:real^N`;
                   `s:real^M->bool`; `a:real^M`; `b:real^M`; `u:real`]
      MOI_LNS_AFFINE_COMBO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_MESON_TAC[CONVEX_ALT];
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `x:real^M`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^M) IN segment(a,b)` THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)))) THEN
    SUBGOAL_THEN
     `(f:real^M->real^N)((&1 - u) % a + u % b) = (&1 - u) % f a + u % f b`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_LNS_AFFINE_COMBO THEN
      MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`; `s:real^M->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(f:real^M->real^N) a = f b` THENL
     [SUBGOAL_THEN `(f:real^M->real^N)((&1 - u) % a + u % b) = f b` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(t:real^N->bool) face_of IMAGE (f:real^M->real^N) s` THEN
    REWRITE_TAC[face_of] THEN
    DISCH_THEN(MP_TAC o SPECL [`(f:real^M->real^N) a`; `(f:real^M->real^N) b`;
                               `(f:real^M->real^N)((&1 - u) % a + u % b)`] o
               CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[FUN_IN_IMAGE];
        ASM_MESON_TAC[FUN_IN_IMAGE];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `u:real` THEN
        ASM_REWRITE_TAC[]];
      SIMP_TAC[]]]);;

let MOI_LNS_AFFINE_IMAGE_EQ = prove
 (`!(f:real^M->real^N) l y s u.
     (!x. x IN s ==> f x = l x + y) /\ u SUBSET s
     ==> IMAGE f u = IMAGE (\x. y + x) (IMAGE l u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  MATCH_MP_TAC IMAGE_EQ THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
  ASM_MESON_TAC[SUBSET]);;

let MOI_LNS_AFFINE_RELINT = prove
 (`!(f:real^M->real^N) l y s.
     linear l /\ (!x. x IN s ==> f x = l x + y) /\ convex s
     ==> relative_interior (IMAGE f s) = IMAGE f (relative_interior s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `l:real^M->real^N`; `y:real^N`;
                 `s:real^M->bool`; `s:real^M->bool`] MOI_LNS_AFFINE_IMAGE_EQ) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `l:real^M->real^N`; `y:real^N`;
                 `s:real^M->bool`; `relative_interior s:real^M->bool`]
    MOI_LNS_AFFINE_IMAGE_EQ) THEN
  ASM_REWRITE_TAC[SUBSET_REFL; RELATIVE_INTERIOR_SUBSET] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[RELATIVE_INTERIOR_TRANSLATION] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RELATIVE_INTERIOR_LINEAR_IMAGE_CONVEX THEN ASM_REWRITE_TAC[]);;

let MOI_LNS_AFFINE_HULL_IMAGE = prove
 (`!(h:real^M->real^N) l y t.
     linear l /\ (!x. x IN convex hull t ==> h x = l x + y)
     ==> IMAGE h (convex hull t) = convex hull (IMAGE h t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^M->real^N`; `l:real^M->real^N`; `y:real^N`;
                 `convex hull t:real^M->bool`; `convex hull t:real^M->bool`]
    MOI_LNS_AFFINE_IMAGE_EQ) THEN
  MP_TAC(ISPECL [`h:real^M->real^N`; `l:real^M->real^N`; `y:real^N`;
                 `convex hull t:real^M->bool`; `t:real^M->bool`]
    MOI_LNS_AFFINE_IMAGE_EQ) THEN
  ASM_REWRITE_TAC[SUBSET_REFL; HULL_SUBSET] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
  MP_TAC(ISPECL [`l:real^M->real^N`; `y:real^N`; `t:real^M->bool`]
    MOI_REAL_AFFINE_IMAGE_CONVEX_HULL) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The barycentric vertex map b(s) -> b(f s) of a simplicial map,           *)
(* extended simplexwise over the barycentric subdivision; images of chains; *)
(* lifting chains of faces of f(s) to chains of faces of s.                 *)
(* ========================================================================= *)

let MOI_LNS_VERTEX_MAP = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f.
     simplicial_complex k /\ lf_simplicial_complex c /\ simplicial_map_on k c f
     ==> ?h. !q. moi_bar_chain k q /\ ~(q = {})
                 ==> (?l y. linear l /\
                            !x. x IN convex hull (IMAGE simplex_barycentre q)
                                ==> h x = l x + y) /\
                     (!s. s IN q ==> h (simplex_barycentre s) =
                                     simplex_barycentre (IMAGE f s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (k:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_SIMPLICIAL_COMPLEX]; ALL_TAC] THEN
  ABBREV_TAC
   `g = \v:real^M. simplex_barycentre (IMAGE (f:real^M->real^N)
          (@s. s IN k /\ ~(s = {}) /\ simplex_barycentre s = v))` THEN
  SUBGOAL_THEN
   `!s:real^M->bool. s IN k /\ ~(s = {})
        ==> (g:real^M->real^N) (simplex_barycentre s) =
            simplex_barycentre (IMAGE (f:real^M->real^N) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "g" THEN BETA_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC `s':real^M->bool` THEN BETA_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_BARYCENTRE_INJ THEN
      EXISTS_TAC `k:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^M. x`; `g:real^M->real^N`;
                 `moi_real_vertex_sets
                    (barycentric_subdivision (k:(real^M->bool)->bool))`]
    MOI_REAL_SIMPLEXWISE_AFFINE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MOI_REAL_VERTEX_SETS_REALIZES THEN
    ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_ID] THEN
  DISCH_THEN(X_CHOOSE_TAC `h:real^M->real^N`) THEN
  EXISTS_TAC `h:real^M->real^N` THEN
  X_GEN_TAC `q:(real^M->bool)->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE simplex_barycentre (q:(real^M->bool)->bool)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
      MATCH_MP_TAC MOI_BAR_CHAIN_AFFINE_INDEPENDENT THEN
      EXISTS_TAC `k:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `q:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `q:(real^M->bool)->bool`;
                 `s:real^M->bool`] MOI_BAR_CHAIN_ELEMENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplex_barycentre (s:real^M->bool) IN
                IMAGE simplex_barycentre (q:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (s:real^M->bool) IN
                convex hull (IMAGE simplex_barycentre (q:(real^M->bool)->bool))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[HULL_INC]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `(l:real^M->real^N) (simplex_barycentre (s:real^M->bool)) + y` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `(g:real^M->real^N) (simplex_barycentre (s:real^M->bool))` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ASM_SIMP_TAC[]]);;

let MOI_LNS_IMAGE_CHAIN = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f q.
     simplicial_map_on k c f /\ moi_bar_chain k q
     ==> moi_bar_chain c (IMAGE (IMAGE f) q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_map_on; moi_bar_chain] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `s:real^M->bool` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(s:real^M->bool) IN k` (fun th -> ASM_MESON_TAC[th]) THEN
    UNDISCH_TAC `(s:real^M->bool) IN q` THEN
    UNDISCH_TAC `(q:(real^M->bool)->bool) SUBSET k` THEN SET_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `{}:real^N->bool = IMAGE (f:real^M->real^N) s` THEN
    DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~({}:real^M->bool IN q)` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^M->bool`; `t:real^M->bool`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[IMAGE_SUBSET]]);;

let MOI_LNS_CHAIN_IMAGE = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f (h:real^M->real^N) q.
     simplicial_map_on k c f /\ moi_bar_chain k q /\ ~(q = {}) /\
     (?l y. linear l /\
            !x. x IN convex hull (IMAGE simplex_barycentre q) ==> h x = l x + y) /\
     (!s. s IN q ==> h (simplex_barycentre s) = simplex_barycentre (IMAGE f s))
     ==> moi_bar_chain c (IMAGE (IMAGE f) q) /\
         IMAGE h (convex hull (IMAGE simplex_barycentre q)) =
         convex hull (IMAGE simplex_barycentre (IMAGE (IMAGE f) q))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
         STRIP_ASSUME_TAC)) ASSUME_TAC)))) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LNS_IMAGE_CHAIN THEN EXISTS_TAC `k:(real^M->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^M->real^N`; `l:real^M->real^N`; `y:real^N`;
                 `IMAGE simplex_barycentre (q:(real^M->bool)->bool)`]
    MOI_LNS_AFFINE_HULL_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  MATCH_MP_TAC IMAGE_EQ THEN
  ASM_SIMP_TAC[]);;

let MOI_LNS_LIFT_CHAIN = prove
 (`!(k:(real^M->bool)->bool) (f:real^M->real^N) s g.
     simplicial_complex k /\ s IN k /\
     (?l y. linear l /\ !x. x IN s ==> f x = l x + y) /\
     moi_bar_chain {t | t face_of IMAGE f s} g
     ==> ?q. moi_bar_chain k q /\ IMAGE (IMAGE f) q = g /\
             !r. r IN q ==> r SUBSET s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
       STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
  SUBGOAL_THEN `convex (s:real^M->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_SC_LF; MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
  UNDISCH_TAC `moi_bar_chain {t | t face_of IMAGE (f:real^M->real^N) s} g` THEN
  GEN_REWRITE_TAC LAND_CONV [moi_bar_chain] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[SUBSET; IN_ELIM_THM])
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN g ==> t SUBSET IMAGE (f:real^M->real^N) s`
  ASSUME_TAC THENL [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\t:real^N->bool. {x:real^M | x IN s /\ f x IN t}) g` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_bar_chain] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `t:real^N->bool` THEN
      DISCH_TAC THEN
      UNDISCH_TAC `simplicial_complex (k:(real^M->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_LNS_FACE_PREIMAGE THEN
      MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[FINITE_IMAGE];
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~({}:real^N->bool IN g)` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `t SUBSET IMAGE (f:real^M->real^N) s` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(t:real^N->bool = {})` THEN
      UNDISCH_TAC `{}:real^M->bool = {x | x IN s /\ (f:real^M->real^N) x IN t}` THEN
      SET_TAC[];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
      X_GEN_TAC `t':real^N->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`t:real^N->bool`; `t':real^N->bool`]) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM IMAGE_ID] THEN
    MATCH_MP_TAC IMAGE_EQ THEN
    X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `t SUBSET IMAGE (f:real^M->real^N) s` MP_TAC THENL
     [ASM_SIMP_TAC[]; SET_TAC[]];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN SET_TAC[]]);;

(* ========================================================================= *)
(* A simplicial map of a finite complex into a locally finite one induces a  *)
(* simplicial map between the barycentric subdivisions (vertex map b(s) ->   *)
(* b(f s)) with the same image and the same open carriers; the theorem       *)
(* RESIMPLICIAL.                                                             *)
(* ========================================================================= *)

let MOI_LNS_CHAIN_SING = prove
 (`!(k:(real^M->bool)->bool) s.
     s IN k /\ ~(s = {}) ==> moi_bar_chain k {s}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_bar_chain; FINITE_SING; SING_SUBSET; IN_SING] THEN
  ASM_MESON_TAC[SUBSET_REFL]);;

let MOI_LNS_SD_MAP = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f.
     simplicial_complex k /\ lf_simplicial_complex c /\ simplicial_map_on k c f
     ==> ?h. simplicial_map_on (barycentric_subdivision k)
                               (barycentric_subdivision c) h /\
             (!s. s IN k /\ ~(s = {})
                  ==> h (simplex_barycentre s) = simplex_barycentre (IMAGE f s)) /\
             (!q. moi_bar_chain k q /\ ~(q = {})
                  ==> moi_bar_chain c (IMAGE (IMAGE f) q) /\
                      IMAGE h (convex hull (IMAGE simplex_barycentre q)) =
                      convex hull (IMAGE simplex_barycentre (IMAGE (IMAGE f) q))) /\
             IMAGE h (UNIONS k) = IMAGE f (UNIONS k) /\
             !x. x IN UNIONS k
                 ==> ?s. s IN c /\ f x IN relative_interior s /\
                         h x IN relative_interior s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`;
                 `f:real^M->real^N`] MOI_LNS_VERTEX_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N` (LABEL_TAC "h")) THEN
  EXISTS_TAC `h:real^M->real^N` THEN
  SUBGOAL_THEN
   `moi_bar_complex (k:(real^M->bool)->bool) /\ lf_simplicial_complex k /\
    moi_bar_complex (c:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_SIMPLICIAL_COMPLEX; MOI_FMB_SC_LF; MOI_FRN_LF_BAR_COMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q. moi_bar_chain k q /\ ~(q = {})
        ==> moi_bar_chain c (IMAGE (IMAGE (f:real^M->real^N)) q) /\
            IMAGE (h:real^M->real^N) (convex hull (IMAGE simplex_barycentre q)) =
            convex hull (IMAGE simplex_barycentre (IMAGE (IMAGE f) q))`
  (LABEL_TAC "img") THENL
   [X_GEN_TAC `q:(real^M->bool)->bool` THEN STRIP_TAC THEN
    USE_THEN "h" (MP_TAC o SPEC `q:(real^M->bool)->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^M->real^N`
      (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`;
                   `f:real^M->real^N`; `h:real^M->real^N`;
                   `q:(real^M->bool)->bool`] MOI_LNS_CHAIN_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* simplicial *)
    REWRITE_TAC[simplicial_map_on; MOI_BAR_IN_SUBDIVISION] THEN
    X_GEN_TAC `sg:real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `q:(real^M->bool)->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    ASM_CASES_TAC `q:(real^M->bool)->bool = {}` THENL
     [CONJ_TAC THENL
       [EXISTS_TAC `{}:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[moi_bar_chain; IMAGE_CLAUSES; CONVEX_HULL_EMPTY;
                        EMPTY_SUBSET; FINITE_EMPTY; NOT_IN_EMPTY];
        MAP_EVERY EXISTS_TAC [`\x:real^M. vec 0:real^N`; `vec 0:real^N`] THEN
        ASM_REWRITE_TAC[LINEAR_ZERO; IMAGE_CLAUSES; CONVEX_HULL_EMPTY;
                        NOT_IN_EMPTY]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `IMAGE (IMAGE (f:real^M->real^N)) q` THEN
      USE_THEN "img" (MP_TAC o SPEC `q:(real^M->bool)->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      USE_THEN "h" (MP_TAC o SPEC `q:(real^M->bool)->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)]];
    (* vertices *)
    X_GEN_TAC `s:real^M->bool` THEN STRIP_TAC THEN
    USE_THEN "h" (MP_TAC o SPEC `{s:real^M->bool}`) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MOI_LNS_CHAIN_SING; NOT_INSERT_EMPTY]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^M->bool` o CONJUNCT2) THEN
    REWRITE_TAC[IN_SING];
    (* chains *)
    X_GEN_TAC `q:(real^M->bool)->bool` THEN DISCH_TAC THEN
    USE_THEN "img" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* images *)
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^M` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^M) IN UNIONS (barycentric_subdivision k)` MP_TAC THENL
       [ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS; MOI_BAR_IN_SUBDIVISION] THEN
      DISCH_THEN(X_CHOOSE_THEN `sg:real^M->bool`
        (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
      DISCH_THEN(X_CHOOSE_THEN `q:(real^M->bool)->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
      SUBGOAL_THEN `~(q:(real^M->bool)->bool = {})` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `(x:real^M) IN convex hull (IMAGE simplex_barycentre {})` THEN
        REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
        ALL_TAC] THEN
      USE_THEN "img" (MP_TAC o SPEC `q:(real^M->bool)->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `(h:real^M->real^N) x IN
        convex hull (IMAGE simplex_barycentre (IMAGE (IMAGE (f:real^M->real^N)) q))`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `convex hull (IMAGE simplex_barycentre (IMAGE (IMAGE (f:real^M->real^N)) q))
        SUBSET UNIONS (IMAGE (IMAGE f) q)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_BAR_CHAIN_HULL_SUBSET_MAX THEN
        EXISTS_TAC `c:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `UNIONS (IMAGE (IMAGE (f:real^M->real^N)) q) SUBSET IMAGE f (UNIONS k)`
      ASSUME_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_UNIONS] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        MATCH_MP_TAC SUBSET_UNIONS THEN
        UNDISCH_TAC `moi_bar_chain k (q:(real^M->bool)->bool)` THEN
        SIMP_TAC[moi_bar_chain];
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE
       `!(a:real^N->bool) b d z. z IN a /\ a SUBSET b /\ b SUBSET d ==> z IN d`) THEN
      MAP_EVERY EXISTS_TAC
       [`convex hull (IMAGE simplex_barycentre
                       (IMAGE (IMAGE (f:real^M->real^N)) q))`;
        `UNIONS (IMAGE (IMAGE (f:real^M->real^N)) q)`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIONS] THEN
    X_GEN_TAC `x:real^M` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `IMAGE (f:real^M->real^N) s IN c /\
      ?l y. linear l /\ !x. x IN s ==> f x = l x + y`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_map_on k c (f:real^M->real^N)` THEN
      REWRITE_TAC[simplicial_map_on] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^M->bool`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`aff_dim(IMAGE (f:real^M->real^N) s)`;
                   `IMAGE (f:real^M->real^N) s`; `(f:real^M->real^N) x`]
      MOI_BAR_SIMPLEX_COVERED) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FM3_LF_SIMPLEX THEN
        EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[FUN_IN_IMAGE]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `f:real^M->real^N`; `s:real^M->bool`;
                   `g:(real^N->bool)->bool`] MOI_LNS_LIFT_CHAIN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(q:(real^M->bool)->bool = {})` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `IMAGE (IMAGE (f:real^M->real^N)) {} = g` THEN
      REWRITE_TAC[IMAGE_CLAUSES] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      UNDISCH_TAC `(f:real^M->real^N) x IN
                   convex hull (IMAGE simplex_barycentre {})` THEN
      REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      ALL_TAC] THEN
    USE_THEN "img" (MP_TAC o SPEC `q:(real^M->bool)->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(f:real^M->real^N) x IN
      IMAGE (h:real^M->real^N) (convex hull (IMAGE simplex_barycentre q))`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^M` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^M` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `convex hull (IMAGE simplex_barycentre q) SUBSET UNIONS (q:(real^M->bool)->bool)`
    MP_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_HULL_SUBSET_MAX THEN
      EXISTS_TAC `k:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `!r:real^M->bool. r IN q ==> r SUBSET s` THEN
    UNDISCH_TAC `(z:real^M) IN convex hull (IMAGE simplex_barycentre q)` THEN
    UNDISCH_TAC `(s:real^M->bool) IN k` THEN UNDISCH_TAC `(x:real^M) IN s` THEN
    SET_TAC[];
    (* carriers *)
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^M) IN UNIONS (barycentric_subdivision k)` MP_TAC THENL
     [ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; MOI_BAR_IN_SUBDIVISION] THEN
    DISCH_THEN(X_CHOOSE_THEN `sg:real^M->bool`
      (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `q0:(real^M->bool)->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `q0:(real^M->bool)->bool`; `x:real^M`]
      MOI_BAR_CHAIN_HULL_RI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_bar_chain k (q:(real^M->bool)->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
      EXISTS_TAC `q0:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(q:(real^M->bool)->bool = {})` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(x:real^M) IN
                   relative_interior (convex hull (IMAGE simplex_barycentre {}))` THEN
      REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; RELATIVE_INTERIOR_EMPTY;
                  NOT_IN_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `UNIONS (q:(real^M->bool)->bool) IN k` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `q:(real^M->bool)->bool`]
        MOI_BAR_CHAIN_MAX) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `moi_bar_chain k (q:(real^M->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^M) IN relative_interior (UNIONS q)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_RI_MAX THEN
      EXISTS_TAC `k:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `IMAGE (f:real^M->real^N) (UNIONS q)` THEN
    SUBGOAL_THEN
     `IMAGE (f:real^M->real^N) (UNIONS q) IN c /\
      ?l y. linear l /\ !x. x IN UNIONS q ==> f x = l x + y`
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `l1:real^M->real^N`
       (X_CHOOSE_THEN `y1:real^N` STRIP_ASSUME_TAC))) THENL
     [UNDISCH_TAC `simplicial_map_on k c (f:real^M->real^N)` THEN
      REWRITE_TAC[simplicial_map_on] THEN
      DISCH_THEN(MP_TAC o SPEC `UNIONS (q:(real^M->bool)->bool)`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`f:real^M->real^N`; `l1:real^M->real^N`; `y1:real^N`;
                     `UNIONS (q:(real^M->bool)->bool)`] MOI_LNS_AFFINE_RELINT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      ALL_TAC] THEN
    USE_THEN "h" (MP_TAC o SPEC `q:(real^M->bool)->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `l2:real^M->real^N`
      (X_CHOOSE_THEN `y2:real^N` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    USE_THEN "img" (MP_TAC o SPEC `q:(real^M->bool)->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`h:real^M->real^N`; `l2:real^M->real^N`; `y2:real^N`;
                   `convex hull (IMAGE simplex_barycentre (q:(real^M->bool)->bool))`]
      MOI_LNS_AFFINE_RELINT) THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(h:real^M->real^N) x IN
      relative_interior
        (convex hull (IMAGE simplex_barycentre
                       (IMAGE (IMAGE (f:real^M->real^N)) q)))`
    MP_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th] THEN
                              ASSUME_TAC th) THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[IMAGE_UNIONS] THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_RI_MAX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

let RESIMPLICIAL = prove
 (MOI_LT_RESIMPLICIAL,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LNS_SD_MAP) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h:real^M->real^N` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The image complex of a simplicial map; two resimplicial-                *)
(* izations composed (second barycentric subdivisions, the same open       *)
(* carriers); membership in the boundary depends only on the open carrier.  *)
(* ========================================================================= *)

let MOI_LNS_IMAGE_COMPLEX = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f.
     simplicial_complex k /\ lf_simplicial_complex c /\ simplicial_map_on k c f
     ==> simplicial_subcomplex (IMAGE (IMAGE f) k) c /\
         FINITE (IMAGE (IMAGE f) k) /\
         UNIONS (IMAGE (IMAGE f) k) = IMAGE f (UNIONS k)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      UNDISCH_TAC `simplicial_map_on k c (f:real^M->real^N)` THEN
      SIMP_TAC[simplicial_map_on];
      ALL_TAC] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?l y. linear l /\ !x. x IN s ==> (f:real^M->real^N) x = l x + y`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_map_on k c (f:real^M->real^N)` THEN
      REWRITE_TAC[simplicial_map_on] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^M->bool`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex (s:real^M->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FMB_SC_LF; MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `{x:real^M | x IN s /\ (f:real^M->real^N) x IN t}` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `t SUBSET IMAGE (f:real^M->real^N) s` MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; SET_TAC[]];
      UNDISCH_TAC `simplicial_complex (k:(real^M->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_LNS_FACE_PREIMAGE THEN
      MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC FINITE_IMAGE THEN ASM_MESON_TAC[simplicial_complex];
    REWRITE_TAC[IMAGE_UNIONS]]);;

let MOI_LNS_SD_RELINT = prove
 (`!(c:(real^N->bool)->bool) s' x.
     moi_bar_complex c /\ s' IN barycentric_subdivision c /\
     x IN relative_interior s'
     ==> ?t. t IN c /\ relative_interior s' SUBSET relative_interior t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
     SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `~(q:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(x:real^N) IN
                 relative_interior (convex hull (IMAGE simplex_barycentre {}))` THEN
    REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; RELATIVE_INTERIOR_EMPTY;
                NOT_IN_EMPTY];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS (q:(real^N->bool)->bool)` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `q:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_MAX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `moi_bar_chain c (q:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_RI_MAX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_LNS_RELINT_EQ = prove
 (`!(c:(real^N->bool)->bool) s t x.
     moi_bar_complex c /\ s IN c /\ t IN c /\
     x IN relative_interior s /\ x IN relative_interior t
     ==> s = t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC MOI_FRN_RELINT_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN
  ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]);;

let MOI_LNS_TWO_STEP = prove
 (`!(k:(real^M->bool)->bool) (c:(real^N->bool)->bool) f.
     simplicial_complex k /\ lf_simplicial_complex c /\ simplicial_map_on k c f
     ==> ?f1. simplicial_map_on
                (barycentric_subdivision (barycentric_subdivision k))
                (barycentric_subdivision (barycentric_subdivision c)) f1 /\
              IMAGE f1 (UNIONS k) = IMAGE f (UNIONS k) /\
              !x. x IN UNIONS k
                  ==> ?s. s IN c /\ f x IN relative_interior s /\
                          f1 x IN relative_interior s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `c:(real^N->bool)->bool`;
                 `f:real^M->real^N`] RESIMPLICIAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`barycentric_subdivision (k:(real^M->bool)->bool)`;
                 `barycentric_subdivision (c:(real^N->bool)->bool)`;
                 `f':real^M->real^N`] RESIMPLICIAL) THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX;
               BARYCENTRIC_SUBDIVISION_LF] THEN
  SUBGOAL_THEN `UNIONS (barycentric_subdivision k) = UNIONS (k:(real^M->bool)->bool)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION; MOI_FMB_SC_LF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^M->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f1:real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s':real^N->bool`;
                 `(f':real^M->real^N) x`] MOI_LNS_SD_RELINT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t:real^N->bool = s` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOI_LNS_RELINT_EQ THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `(f':real^M->real^N) x`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_LNS_CARRIER_BOUNDARY = prove
 (`!(c:(real^N->bool)->bool) s y.
     lf_simplicial_complex c /\ s IN c /\ y IN relative_interior s /\
     y IN complex_boundary c
     ==> s SUBSET complex_boundary c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FM3_BC_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN complex_boundary c` THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t:real^N->bool) IN c /\ t SUBSET complex_boundary c`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real^N->bool) IN boundary_complex c` THEN
    REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `y:real^N`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Segments between points with a common open carrier stay in a            *)
(* boundary component; boundary simplices of the derived neighbourhood     *)
(* that meet the subcomplex lie in the boundary of the ambient manifold.   *)
(* ========================================================================= *)

let MOI_LNS_SEGMENT_IN_COMPONENT = prove
 (`!(c:(real^N->bool)->bool) b s p p'.
     lf_simplicial_complex c /\ b IN components (complex_boundary c) /\
     s IN c /\ p IN relative_interior s /\ p' IN relative_interior s /\ p IN b
     ==> segment[p,p'] SUBSET b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET complex_boundary c` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LNS_CARRIER_BOUNDARY THEN EXISTS_TAC `p:real^N` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p:real^N,p'] SUBSET s` ASSUME_TAC THENL
   [SUBGOAL_THEN `convex (s:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
  EXISTS_TAC `complex_boundary (c:(real^N->bool)->bool)` THEN
  ASM_REWRITE_TAC[CONNECTED_SEGMENT] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `p:real^N` THEN
    ASM_REWRITE_TAC[IN_INTER; ENDS_IN_SEGMENT]]);;

let MOI_LNS_BOUNDARY_SD2 = prove
 (`!c0:(real^N->bool)->bool.
     combinatorial_manifold_with_boundary 3 c0
     ==> combinatorial_manifold_with_boundary 3
           (barycentric_subdivision (barycentric_subdivision c0)) /\
         complex_boundary (barycentric_subdivision (barycentric_subdivision c0)) =
         complex_boundary c0 /\
         lf_simplicial_complex
           (barycentric_subdivision (barycentric_subdivision c0)) /\
         (orientable_complex c0
          ==> orientable_complex
                (barycentric_subdivision (barycentric_subdivision c0)))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `c0:(real^N->bool)->bool` COMBINATORIAL_WB_BARYCENTRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `barycentric_subdivision (c0:(real^N->bool)->bool)`
    COMBINATORIAL_WB_BARYCENTRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    ASM_MESON_TAC[]]);;

let MOI_LNS_BUFFER_SIMPLEX = prove
 (`!(c0:(real^N->bool)->bool) l s.
     combinatorial_manifold_with_boundary 3 c0 /\
     simplicial_subcomplex l c0 /\ FINITE l /\
     s IN derived_nbhd_complex c0 l /\
     s SUBSET complex_boundary (derived_nbhd_complex c0 l) /\
     ~(s INTER UNIONS l = {})
     ==> s SUBSET complex_boundary c0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c0:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c0:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c0:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_COMBINATORIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c0:(real^N->bool)->bool` MOI_LNS_BOUNDARY_SD2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `derived_nbhd_complex c0 l SUBSET
    barycentric_subdivision (barycentric_subdivision (c0:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN boundary_complex (derived_nbhd_complex c0 l)`
  ASSUME_TAC THENL
   [REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~({}:real^N->bool INTER UNIONS l = {})` THEN
    REWRITE_TAC[INTER_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPEC `derived_nbhd_complex (c0:(real^N->bool)->bool) l`
    BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`boundary_complex (derived_nbhd_complex (c0:(real^N->bool)->bool) l)`;
                 `s:real^N->bool`] MOI_FRN_CM_PURE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `derived_nbhd_complex (c0:(real^N->bool)->bool) l` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[boundary_complex] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(d:real^N->bool) IN derived_nbhd_complex c0 l` ASSUME_TAC THENL
   [UNDISCH_TAC `(d:real^N->bool) IN boundary_complex (derived_nbhd_complex c0 l)` THEN
    REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {r | r IN derived_nbhd_complex c0 l /\ aff_dim r = &3 /\
              (d:real^N->bool) SUBSET r} = 1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`derived_nbhd_complex (c0:(real^N->bool)->bool) l`;
                   `d:real^N->bool`] MOI_LNS_TRIANGLE_TETS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{r | r IN derived_nbhd_complex c0 l /\ aff_dim r = &3 /\ d SUBSET r} =
    {r | r IN barycentric_subdivision (barycentric_subdivision c0) /\
         aff_dim r = &3 /\ (d:real^N->bool) SUBSET r}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `r:real^N->bool` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE
       `!(x:real^N->bool) s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `derived_nbhd_complex (c0:(real^N->bool)->bool) l` THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
      EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `~((s:real^N->bool) INTER UNIONS l = {})` THEN
        UNDISCH_TAC `(s:real^N->bool) SUBSET d` THEN
        UNDISCH_TAC `(d:real^N->bool) SUBSET r` THEN SET_TAC[];
        MATCH_MP_TAC FACE_OF_REFL THEN MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
        EXISTS_TAC `barycentric_subdivision
                      (barycentric_subdivision (c0:(real^N->bool)->bool))` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {r | r IN barycentric_subdivision (barycentric_subdivision c0) /\
              aff_dim r = &3 /\ (d:real^N->bool) SUBSET r} = 1`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^N->bool) SUBSET complex_boundary c0` MP_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
                                rand (concl th) = `complex_boundary (c0:(real^N->bool)->bool)`
                             then SUBST1_TAC (SYM th) else failwith "no") THEN
    REWRITE_TAC[complex_boundary] THEN
    MATCH_MP_TAC(SET_RULE `!(t:real^N->bool) u. t IN u ==> t SUBSET UNIONS u`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
     `!(x:real^N->bool) s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `derived_nbhd_complex (c0:(real^N->bool)->bool) l` THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `(s:real^N->bool) SUBSET d` THEN SET_TAC[]]);;

(* ========================================================================= *)
(* The first normal system (Moise pp.187-188 (1)-(4)): the map lands in the  *)
(* derived neighbourhood complex, stays proper, its boundary loop is         *)
(* homotopic to the old one in each boundary component, and the boundary     *)
(* simplices through the loop stay in that component; the theorem NSYS.      *)
(* ========================================================================= *)

let MOI_LNS_INTO_NBHD = prove
 (`!(c0:(real^N->bool)->bool) lk (k1:(real^M->bool)->bool) f1.
     lf_simplicial_complex c0 /\
     simplicial_map_on k1 (barycentric_subdivision (barycentric_subdivision c0)) f1 /\
     IMAGE f1 (UNIONS k1) SUBSET UNIONS lk /\ ~(UNIONS k1 = {})
     ==> simplicial_map_on k1 (derived_nbhd_complex c0 lk) f1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lf_simplicial_complex
      (barycentric_subdivision (barycentric_subdivision (c0:(real^N->bool)->bool)))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  UNDISCH_TAC `simplicial_map_on k1
                 (barycentric_subdivision (barycentric_subdivision c0))
                 (f1:real^M->real^N)` THEN
  REWRITE_TAC[simplicial_map_on] THEN DISCH_THEN(LABEL_TAC "f1s") THEN
  SUBGOAL_THEN `({}:real^N->bool) IN derived_nbhd_complex c0 lk` ASSUME_TAC THENL
   [UNDISCH_TAC `~(UNIONS k1:real^M->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:real^M` (X_CHOOSE_THEN `sg0:real^M->bool`
      STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
    EXISTS_TAC `IMAGE (f1:real^M->real^N) sg0` THEN REWRITE_TAC[EMPTY_FACE_OF] THEN
    CONJ_TAC THENL
     [USE_THEN "f1s" (MP_TAC o SPEC `sg0:real^M->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `(f1:real^M->real^N) x0` THEN REWRITE_TAC[IN_INTER] THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[FUN_IN_IMAGE];
        UNDISCH_TAC `IMAGE (f1:real^M->real^N) (UNIONS k1) SUBSET UNIONS lk` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIONS] THEN
        DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `sg0:real^M->bool` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[simplicial_map_on] THEN X_GEN_TAC `sg:real^M->bool` THEN DISCH_TAC THEN
  USE_THEN "f1s" (MP_TAC o SPEC `sg:real^M->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> REWRITE_TAC[th])) THEN
  ASM_CASES_TAC `sg:real^M->bool = {}` THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
  REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
  EXISTS_TAC `IMAGE (f1:real^M->real^N) sg` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `~(sg:real^M->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^M`) THEN
    EXISTS_TAC `(f1:real^M->real^N) x` THEN REWRITE_TAC[IN_INTER] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE];
      UNDISCH_TAC `IMAGE (f1:real^M->real^N) (UNIONS k1) SUBSET UNIONS lk` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIONS] THEN
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `sg:real^M->bool` THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC FACE_OF_REFL THEN MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
    EXISTS_TAC `barycentric_subdivision
                  (barycentric_subdivision (c0:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LNS_PROPER = prove
 (`!(c0:(real^N->bool)->bool) lk (f:real^M->real^N) f1 d e.
     combinatorial_manifold_with_boundary 3 c0 /\ simplicial_subcomplex lk c0 /\
     IMAGE f1 d SUBSET UNIONS lk /\
     (!x. x IN d ==> ?s. s IN c0 /\ f x IN relative_interior s /\
                         f1 x IN relative_interior s) /\
     {x | x IN d /\ f x IN complex_boundary c0} = e
     ==> {x | x IN d /\ f1 x IN complex_boundary (derived_nbhd_complex c0 lk)} = e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c0:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c0:(real^N->bool)->bool`; `lk:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c0:(real^N->bool)->bool`; `lk:(real^N->bool)->bool`]
    DERIVED_NBHD_COMBINATORIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `{x | x IN d /\ (f:real^M->real^N) x IN complex_boundary c0} = e` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^M` THEN
  ASM_CASES_TAC `(x:real^M) IN d` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `!x. x IN d ==> ?s. s IN c0 /\ (f:real^M->real^N) x IN relative_interior s /\
                                  (f1:real^M->real^N) x IN relative_interior s` THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f1:real^M->real^N) x IN UNIONS lk` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f1:real^M->real^N) d SUBSET UNIONS lk` THEN
    UNDISCH_TAC `(x:real^M) IN d` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(f1:real^M->real^N) x IN derived_nbhd c0 lk /\
    ~((f1:real^M->real^N) x IN derived_frontier c0 lk)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[derived_frontier; frontier_of; IN_DIFF] THEN
    MP_TAC(ISPECL [`subtopology euclidean (UNIONS (c0:(real^N->bool)->bool))`;
                   `derived_nbhd (c0:(real^N->bool)->bool) lk`] INTERIOR_OF_SUBSET) THEN
    UNDISCH_TAC `UNIONS lk SUBSET
                 (subtopology euclidean (UNIONS (c0:(real^N->bool)->bool)))
                 interior_of (derived_nbhd c0 lk)` THEN
    UNDISCH_TAC `(f1:real^M->real^N) x IN UNIONS lk` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNION; IN_INTER] THEN EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`c0:(real^N->bool)->bool`; `s:real^N->bool`;
                   `(f1:real^M->real^N) x`] MOI_LNS_CARRIER_BOUNDARY) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    MP_TAC(ISPECL [`c0:(real^N->bool)->bool`; `s:real^N->bool`;
                   `(f:real^M->real^N) x`] MOI_LNS_CARRIER_BOUNDARY) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]]);;

let MOI_LNS_BOUNDARY_PART = prove
 (`!(c0:(real^N->bool)->bool) lk (f:real^2->real^N) f1 b.
     combinatorial_manifold_with_boundary 3 c0 /\ simplicial_subcomplex lk c0 /\
     FINITE lk /\ f continuous_on std_triangle /\ f1 continuous_on std_triangle /\
     IMAGE f1 std_triangle SUBSET UNIONS lk /\
     (!x. x IN std_triangle
          ==> ?s. s IN c0 /\ f x IN relative_interior s /\
                  f1 x IN relative_interior s) /\
     b IN components (complex_boundary c0) /\
     IMAGE f (relative_frontier std_triangle) SUBSET b
     ==> homotopic_loops b (f o std_triangle_loop) (f1 o std_triangle_loop) /\
         UNIONS {s | s IN derived_nbhd_complex c0 lk /\
                     s SUBSET complex_boundary (derived_nbhd_complex c0 lk) /\
                     ~(s INTER IMAGE f1 (relative_frontier std_triangle) = {})}
         SUBSET b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c0:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c0:(real^N->bool)->bool`; `lk:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN relative_frontier std_triangle
        ==> segment[(f:real^2->real^N) x,(f1:real^2->real^N) x] SUBSET b`
  (LABEL_TAC "seg") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN std_triangle` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE; SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC
     `!x. x IN std_triangle
          ==> ?s. s IN c0 /\ (f:real^2->real^N) x IN relative_interior s /\
                  (f1:real^2->real^N) x IN relative_interior s` THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_LNS_SEGMENT_IN_COMPONENT THEN
    MAP_EVERY EXISTS_TAC [`c0:(real^N->bool)->bool`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^N) (relative_frontier std_triangle) SUBSET b` THEN
    UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; MOI_LTD_STD_TRIANGLE_LOOP] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[MOI_LTD_STD_TRIANGLE_LOOP] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE];
      MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[MOI_LTD_STD_TRIANGLE_LOOP] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE];
      REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      USE_THEN "seg" MATCH_MP_TAC THEN
      REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_LTD_STD_TRIANGLE_LOOP)))] THEN
      REWRITE_TAC[path_image] THEN ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (f1:real^2->real^N) (relative_frontier std_triangle) SUBSET UNIONS lk`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^2->real^N) std_triangle` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET complex_boundary c0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LNS_BUFFER_SIMPLEX THEN
    EXISTS_TAC `lk:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(s INTER IMAGE (f1:real^2->real^N)
                             (relative_frontier std_triangle) = {})` THEN
    UNDISCH_TAC `IMAGE (f1:real^2->real^N) (relative_frontier std_triangle)
                 SUBSET UNIONS lk` THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(s INTER IMAGE (f1:real^2->real^N)
                           (relative_frontier std_triangle) = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
  EXISTS_TAC `complex_boundary (c0:(real^N->bool)->bool)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
    EXISTS_TAC `derived_nbhd_complex (c0:(real^N->bool)->bool) lk` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^N` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    USE_THEN "seg" (MP_TAC o SPEC `x:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[ENDS_IN_SEGMENT; SUBSET]]]);;

let NSYS = prove
 (MOI_LT_NSYS,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c0:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  ABBREV_TAC `lk = IMAGE (IMAGE (f:real^2->real^N)) k` THEN
  MP_TAC(ISPECL [`k:(real^2->bool)->bool`; `c0:(real^N->bool)->bool`;
                 `f:real^2->real^N`] MOI_LNS_IMAGE_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^2->bool)->bool`; `c0:(real^N->bool)->bool`;
                 `f:real^2->real^N`] MOI_LNS_TWO_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^2->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c0:(real^N->bool)->bool`; `lk:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c0:(real^N->bool)->bool`; `lk:(real^N->bool)->bool`]
    DERIVED_NBHD_COMBINATORIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c0:(real^N->bool)->bool`; `lk:(real^N->bool)->bool`]
    DERIVED_NBHD_DEFORMATION_RETRACT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c0:(real^N->bool)->bool` MOI_LNS_BOUNDARY_SD2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `simplicial_complex
      (barycentric_subdivision (barycentric_subdivision (k:(real^2->bool)->bool))) /\
    UNIONS (barycentric_subdivision (barycentric_subdivision k)) = std_triangle`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX;
                 UNIONS_BARYCENTRIC_SUBDIVISION; BARYCENTRIC_SUBDIVISION_LF;
                 MOI_FMB_SC_LF];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^2->real^N) std_triangle SUBSET UNIONS lk`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(f:real^2->real^N) continuous_on std_triangle /\
    (f1:real^2->real^N) continuous_on std_triangle`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:(real^2->bool)->bool`; `c0:(real^N->bool)->bool`;
                     `f:real^2->real^N`] MOI_LTD_SAN_SIMPLICIAL_CELLWISE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP MOI_LTD_CELLWISE_BASIC) THEN SIMP_TAC[];
      MP_TAC(ISPECL
        [`barycentric_subdivision (barycentric_subdivision (k:(real^2->bool)->bool))`;
         `barycentric_subdivision (barycentric_subdivision (c0:(real^N->bool)->bool))`;
         `f1:real^2->real^N`] MOI_LTD_SAN_SIMPLICIAL_CELLWISE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP MOI_LTD_CELLWISE_BASIC) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `simplicial_map_on
      (barycentric_subdivision (barycentric_subdivision (k:(real^2->bool)->bool)))
      (derived_nbhd_complex c0 lk) (f1:real^2->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LNS_INTO_NBHD THEN ASM_REWRITE_TAC[] THEN
    MP_TAC MOI_LTD_FRONTIER_SUBSET_TRIANGLE THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`derived_nbhd_complex (c0:(real^N->bool)->bool) lk`;
    `barycentric_subdivision (barycentric_subdivision (k:(real^2->bool)->bool))`;
    `f1:real^2->real^N`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC MOI_FD_ORIENTABLE_SUBSET THEN
    EXISTS_TAC `barycentric_subdivision
                  (barycentric_subdivision (c0:(real^N->bool)->bool))` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `orientable_complex (c0:(real^N->bool)->bool)
                   ==> orientable_complex
                         (barycentric_subdivision (barycentric_subdivision c0))` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `simplicial_subcomplex (derived_nbhd_complex c0 lk)
                     (barycentric_subdivision
                        (barycentric_subdivision (c0:(real^N->bool)->bool)))` THEN
      SIMP_TAC[simplicial_subcomplex]];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_LNS_PROPER THEN EXISTS_TAC `f:real^2->real^N` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    X_GEN_TAC `b:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_LNS_BOUNDARY_PART THEN ASM_REWRITE_TAC[]]);;


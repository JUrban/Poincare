(* ========================================================================= *)
(* pc_top_lochom: local homology for HOL Light singular homology            *)
(* (homology.ml).                                                            *)
(*   G3 (ATOP_DEGREE_ONE_LOCAL_STATEMENT): excision at a point of a T1       *)
(*   space and the local isomorphism of a map that is a homeomorphism from   *)
(*   an open set onto an open set.                                           *)
(*   G2 (ATOP_EUCLIDEAN_LOCAL_HOMOLOGY_STATEMENT): H_p(R^N, R^N - x) is      *)
(*   trivial for p <> N and infinite cyclic for p = N, and for compact       *)
(*   convex K containing x the restriction H_p(R^N, R^N - K) ->              *)
(*   H_p(R^N, R^N - x) is an isomorphism.                                    *)
(*   M2 (ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT): the same at points of a    *)
(*   topological manifold, with compact chart balls.                          *)
(* Depends on the library and pc_top_iface (statement constants).          *)
(* ========================================================================= *)

needs "src/pc_top_iface.ml";;

prioritize_real();;
type_invention_error := true;;

let ATOP_DEGREE_ONE_IMAGE_SUBSET = prove
 (`!top top' (p:A->B) w x.
        continuous_map (top,top') p /\
        homeomorphic_map (subtopology top w,subtopology top' (IMAGE p w)) p /\
        (!y. y IN topspace top /\ p y IN IMAGE p w ==> y IN w) /\
        x IN w /\ w SUBSET topspace top
        ==> IMAGE p (topspace top DELETE x) SUBSET topspace top' DELETE p x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_INJECTIVE_MAP) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE] THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE; SUBSET; IN_IMAGE];
    DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN w` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `x:A`]) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[]]);;


let ATOP_EXCISION_POINT = prove
 (`!p top (w:A->bool) x.
        t1_space top /\ open_in top w /\ x IN w
        ==> group_isomorphism
              (relative_homology_group(p,subtopology top w,w DELETE x),
               relative_homology_group(p,top,topspace top DELETE x))
              (hom_induced p (subtopology top w,w DELETE x)
                             (top,topspace top DELETE x) (\x. x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(w:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:int`; `top:A topology`; `topspace top:A->bool`;
                 `topspace top DELETE (x:A)`; `topspace top DIFF w:A->bool`]
                HOMOLOGY_EXCISION_AXIOM) THEN
  REWRITE_TAC[SUBTOPOLOGY_TOPSPACE] THEN
  SUBGOAL_THEN `topspace top DIFF (topspace top DIFF w) = w:A->bool /\
                (topspace top DELETE x) DIFF (topspace top DIFF w) = w DELETE (x:A)`
  (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[DELETE_SUBSET] THEN
  SUBGOAL_THEN `top closure_of (topspace top DIFF w) = topspace top DIFF (w:A->bool) /\
                top interior_of (topspace top DELETE x) = topspace top DELETE (x:A)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[CLOSURE_OF_EQ] THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
      ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE];
      REWRITE_TAC[INTERIOR_OF_EQ] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [T1_SPACE_OPEN_IN_DELETE_ALT]) THEN
      SIMP_TAC[OPEN_IN_TOPSPACE]];
    ASM SET_TAC[]]);;

let ATOP_DEGREE_ONE_LOCAL = prove
 (`ATOP_DEGREE_ONE_LOCAL_STATEMENT (:A) (:B)`,
  REWRITE_TAC[ATOP_DEGREE_ONE_LOCAL_STATEMENT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(w:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:A->B) w SUBSET topspace top'` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_INJECTIVE_MAP) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `topspace top INTER w:A->bool = w` SUBST1_TAC THENL
   [ASM SET_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`p:int`; `top:A topology`; `w:A->bool`; `x:A`] ATOP_EXCISION_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `e1':(((num->real)->A)frag->bool)->(((num->real)->A)frag->bool)` o
    GEN_REWRITE_RULE I [group_isomorphism]) THEN
  MP_TAC(ISPECL [`p:int`; `top':B topology`; `IMAGE (f:A->B) w`; `(f:A->B) x`]
    ATOP_EXCISION_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`p:int`; `subtopology top (w:A->bool)`;
                 `subtopology top' (IMAGE (f:A->B) w)`; `w DELETE (x:A)`;
                 `IMAGE (f:A->B) w DELETE f x`; `f:A->B`]
    HOMEOMORPHIC_MAP_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:A->B) (topspace top DELETE x) SUBSET topspace top' DELETE f x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ATOP_DEGREE_ONE_IMAGE_SUBSET THEN EXISTS_TAC `w:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hom_induced p (top,topspace top DELETE x) (top',topspace top' DELETE (f:A->B) x) f o
    hom_induced p (subtopology top w,w DELETE x) (top,topspace top DELETE x) (\x:A. x) =
    hom_induced p (subtopology top' (IMAGE f w),IMAGE f w DELETE f x)
                  (top',topspace top' DELETE f x) (\x:B. x) o
    hom_induced p (subtopology top w,w DELETE x)
                  (subtopology top' (IMAGE f w),IMAGE f w DELETE f x) f`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:int`; `subtopology top (w:A->bool)`; `w DELETE (x:A)`;
                   `top:A topology`; `topspace top DELETE (x:A)`; `top':B topology`;
                   `topspace top' DELETE (f:A->B) x`; `\x:A. x`; `f:A->B`]
                  HOM_INDUCED_COMPOSE) THEN
    MP_TAC(ISPECL [`p:int`; `subtopology top (w:A->bool)`; `w DELETE (x:A)`;
                   `subtopology top' (IMAGE (f:A->B) w)`; `IMAGE (f:A->B) w DELETE f x`;
                   `top':B topology`; `topspace top' DELETE (f:A->B) x`; `f:A->B`; `\x:B. x`]
                  HOM_INDUCED_COMPOSE) THEN
    SUBGOAL_THEN `(\x:B. x) o (f:A->B) = f /\ f o (\x:A. x) = f`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_ID] THEN
    SUBGOAL_THEN
     `continuous_map (subtopology top (w:A->bool),top) (\x. x) /\
      continuous_map (subtopology top' (IMAGE (f:A->B) w),top') (\x. x) /\
      continuous_map (subtopology top w,subtopology top' (IMAGE f w)) f /\
      continuous_map (top,top') f`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
      ASM_MESON_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP];
      ASM_REWRITE_TAC[]] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    REFL_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC GROUP_ISOMORPHISM_EQ THEN
  EXISTS_TAC
   `hom_induced p (subtopology top' (IMAGE (f:A->B) w),IMAGE f w DELETE f x)
                  (top',topspace top' DELETE f x) (\x:B. x) o
    hom_induced p (subtopology top w,w DELETE x)
                  (subtopology top' (IMAGE f w),IMAGE f w DELETE f x) f o
    (e1':(((num->real)->A)frag->bool)->(((num->real)->A)frag->bool))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GROUP_ISOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_homology_group (p,subtopology top' (IMAGE (f:A->B) w),
                                         IMAGE f w DELETE f x)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GROUP_ISOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_homology_group (p,subtopology top (w:A->bool),w DELETE x)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[group_isomorphism] THEN
    EXISTS_TAC `hom_induced p (subtopology top w,w DELETE x)
                              (top,topspace top DELETE x) (\x:A. x)` THEN
    ONCE_REWRITE_TAC[GROUP_ISOMORPHISMS_SYM] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `u:((num->real)->A)frag->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [group_isomorphisms] o
      check (fun th -> is_comb(concl th) &&
                       (try fst(dest_const(fst(strip_comb(concl th)))) = "group_isomorphisms"
                        with Failure _ -> false))) THEN
    SUBGOAL_THEN
     `u = hom_induced p (subtopology top w,w DELETE x) (top,topspace top DELETE x) (\x:A. x)
            ((e1':(((num->real)->A)frag->bool)->(((num->real)->A)frag->bool)) u)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C AP_THM
      `(e1':(((num->real)->A)frag->bool)->(((num->real)->A)frag->bool)) u` o
      check (fun th -> is_eq(concl th) && is_comb(lhs(concl th)) &&
                       (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "o"
                        with Failure _ -> false))) THEN
    REWRITE_TAC[o_THM]]);;


(* ========================================================================= *)
(* Reduced homology of the spheres sphere(a,r) of real^N                     *)
(* (the library has it for nsphere).                                          *)
(* ========================================================================= *)

let HOMEOMORPHIC_SPACE_NSPHERE_SPHERE = prove
 (`!a:real^N r.
        &0 < r
        ==> nsphere(dimindex(:N) - 1) homeomorphic_space
            subtopology euclidean (sphere(a,r))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`nsphere(dimindex(:N) - 1)`;
                       `subtopology euclidean (sphere(vec 0:real^N,&1))`;
                       `subtopology euclidean (sphere(a:real^N,r))`]
                      HOMEOMORPHIC_SPACE_TRANS) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphic_space] THEN
    MP_TAC(ISPEC `dimindex(:N)` HOMEOMORPHIC_MAPS_NSPHERE_EUCLIDEAN_SPHERE) THEN
    REWRITE_TAC[DIMINDEX_GE_1; LE_REFL] THEN
    SUBGOAL_THEN `span(IMAGE basis (1..dimindex(:N))) = (:real^N)` SUBST1_TAC THENL
     [MP_TAC SPAN_STDBASIS THEN REWRITE_TAC[GSYM IN_NUMSEG; SIMPLE_IMAGE];
      REWRITE_TAC[INTER_UNIV] THEN MESON_TAC[]];
    REWRITE_TAC[HOMEOMORPHIC_SPACE_EUCLIDEAN; HOMEOMORPHIC_SPHERES_EQ] THEN
    ASM_REWRITE_TAC[REAL_LT_01]]);;

let REDUCED_HOMOLOGY_GROUP_SPHERE = prove
 (`(!a:real^N r.
        &0 < r
        ==> reduced_homology_group(&(dimindex(:N) - 1),
                                   subtopology euclidean (sphere(a,r)))
            isomorphic_group integer_group) /\
   (!a:real^N r p.
        &0 < r /\ ~(p = &(dimindex(:N) - 1))
        ==> trivial_group(reduced_homology_group(p,subtopology euclidean (sphere(a,r)))))`,
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC(ISPECL
     [`reduced_homology_group(&(dimindex(:N) - 1),subtopology euclidean (sphere(a:real^N,r)))`;
      `reduced_homology_group(&(dimindex(:N) - 1),nsphere(dimindex(:N) - 1))`;
      `integer_group`] ISOMORPHIC_GROUP_TRANS) THEN
    REWRITE_TAC[REDUCED_HOMOLOGY_GROUP_NSPHERE] THEN
    ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    MATCH_MP_TAC HOMEOMORPHIC_SPACE_IMP_ISOMORPHIC_REDUCED_HOMOLOGY_GROUPS THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_SPACE_NSPHERE_SPHERE];
    MP_TAC(ISPECL [`a:real^N`; `r:real`] HOMEOMORPHIC_SPACE_NSPHERE_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `p:int` o
      MATCH_MP HOMEOMORPHIC_SPACE_IMP_ISOMORPHIC_REDUCED_HOMOLOGY_GROUPS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP ISOMORPHIC_GROUP_TRIVIALITY th)]) THEN
    MATCH_MP_TAC(CONJUNCT2 REDUCED_HOMOLOGY_GROUP_NSPHERE) THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The radial deformation of the complement of a convex                     *)
(* set onto a sphere around one of its points, with a base point on the      *)
(* sphere held fixed.                                                         *)
(* ========================================================================= *)

let RADIAL_SEGMENT_COMPLEMENT_CONVEX = prove
 (`!k a:real^N r x.
        convex k /\ a IN k /\ k SUBSET ball(a,r) /\ ~(x IN k)
        ==> segment[a + (r / norm(x - a)) % (x - a),x] SUBSET (:real^N) DIFF k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(x:real^N = a)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^N->bool) SUBSET ball(a,r)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `s = norm(x - a:real^N)` THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_SEGMENT] THEN
  X_GEN_TAC `z:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  ABBREV_TAC `m = (&1 - t) * r + t * s` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ (a = &0 ==> &0 < b) ==> &0 < a + b`) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ENTIRE] THEN STRIP_TAC THENL
       [SUBGOAL_THEN `t = &1` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `z:real^N = a + (m / s) % (x - a)` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ARITH `z:real^N = a + y <=> z - a = y`] THEN
    REWRITE_TAC[VECTOR_ARITH
     `((&1 - t) % (a + c % (x - a)) + t % x) - a:real^N = ((&1 - t) * c + t) % (x - a)`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "m" THEN
    UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `s <= m \/ m < s`) THENL
   [UNDISCH_TAC `~(x:real^N IN k)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `x:real^N = (&1 - s / m) % a + (s / m) % (a + (m / s) % (x - a))`
    SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH
       `(&1 - c) % a + c % (a + d % (x - a)):real^N = a + (c * d) % (x - a)`] THEN
      SUBGOAL_THEN `s / m * m / s = &1` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`&0 < s`; `&0 < m`] THEN CONV_TAC REAL_FIELD;
        VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CONVEX_ALT] o
      check (fun th -> concl th = `convex (k:real^N->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `r <= m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    SUBGOAL_THEN `(&1 - t) * r + t * s - r = t * (s - r)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `r < s` ASSUME_TAC THENL
     [UNDISCH_TAC `m < s` THEN EXPAND_TAC "m" THEN
      SUBGOAL_THEN `(&1 - t) * r + t * s < s <=> (&1 - t) * r < (&1 - t) * s`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `t = &1` THENL
       [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        SUBGOAL_THEN `&0 < &1 - t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LT_LMUL_EQ]];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= t * (s - r) ==> r <= (&1 - t) * r + t * s`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a + (r / s) % (x - a) IN (k:real^N->bool)` MP_TAC THENL
   [SUBGOAL_THEN
     `a + (r / s) % (x - a) =
      (&1 - r / m) % a + (r / m) % (a + (m / s) % (x - a)):real^N`
    SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH
       `(&1 - c) % a + c % (a + d % (x - a)):real^N = a + (c * d) % (x - a)`] THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MAP_EVERY UNDISCH_TAC [`&0 < s`; `&0 < m`] THEN CONV_TAC REAL_FIELD;
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CONVEX_ALT] o
        check (fun th -> concl th = `convex (k:real^N->bool)`)) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID]];
    UNDISCH_TAC `(k:real^N->bool) SUBSET ball(a,r)` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `a - (a + x):real^N = --x`; NORM_NEG;
                NORM_MUL] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs(r / s) * s = r` (fun th -> REWRITE_TAC[th; REAL_LT_REFL]) THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_DIV_RMUL;
                 REAL_LT_IMP_NZ]]);;

let HOMOTOPIC_WITH_LINEAR_IMAGE_SUBSET = prove
 (`!f g:real^N->real^N s t u.
        f continuous_on s /\ g continuous_on s /\
        (!x. x IN s ==> segment[f x,g x] SUBSET t) /\
        (!x. x IN u ==> f x = g x /\ f x IN u)
        ==> homotopic_with (\h. IMAGE h u SUBSET u)
             (subtopology euclidean s,subtopology euclidean t) f g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMOTOPIC_WITH_EUCLIDEAN] THEN
  EXISTS_TAC
    `\y. ((&1 - drop(fstcart y)) % (f:real^N->real^N)(sndcart y) +
         drop(fstcart y) % g(sndcart y):real^N)` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_SUB_RZERO] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
  REWRITE_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; LIFT_SUB] THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON;
             LINEAR_FSTCART; ETA_AX] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    SIMP_TAC[SNDCART_PASTECART; FORALL_IN_PCROSS];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`z:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o
      check (fun th -> is_forall(concl th) && free_in `t:real^N->bool` (concl th))) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `drop z` THEN
    ASM_MESON_TAC[IN_INTERVAL_1; DROP_VEC];
    X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o
      check (fun th -> is_forall(concl th) && free_in `u:real^N->bool` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_MESON_TAC[VECTOR_ARITH `(&1 - t) % a + t % a:real^N = a`]]);;

let CONTINUOUS_ON_RADIAL_PROJECTION = prove
 (`!a:real^N r s.
        ~(a IN s) ==> (\x. a + (r / norm(x - a)) % (x - a)) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
  REWRITE_TAC[real_div; o_DEF; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
  SIMP_TAC[CONTINUOUS_ON_LIFT_NORM_COMPOSE; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
           CONTINUOUS_ON_ID] THEN
  REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]);;

let GROUP_ISOMORPHISM_HOM_INDUCED_SPHERE_COMPLEMENT_CONVEX = prove
 (`!p k a:real^N r y.
        convex k /\ a IN k /\ k SUBSET ball(a,r) /\ y IN sphere(a,r)
        ==> group_isomorphism
              (relative_homology_group(p,subtopology euclidean (sphere(a,r)),{y}),
               relative_homology_group(p,subtopology euclidean ((:real^N) DIFF k),{y}))
              (hom_induced p (subtopology euclidean (sphere(a,r)),{y})
                             (subtopology euclidean ((:real^N) DIFF k),{y}) (\x. x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^N->bool) SUBSET ball(a,r)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(a:real^N,r) SUBSET (:real^N) DIFF k` ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^N->bool) SUBSET ball(a,r)` THEN
    REWRITE_TAC[SUBSET; IN_SPHERE; IN_BALL; IN_DIFF; IN_UNIV] THEN
    MESON_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN sphere(a,r) ==> a + (r / norm(x - a)) % (x - a) = x`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE; dist] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `norm(x - a:real^N) = r` SUBST1_TAC THENL
     [ASM_MESON_TAC[NORM_SUB]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a:real^N IN (:real^N) DIFF k)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DIFF; IN_UNIV]; ALL_TAC] THEN
  MATCH_MP_TAC DEFORMATION_RETRACT_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISM_ID THEN
  EXISTS_TAC `\x:real^N. a + (r / norm(x - a)) % (x - a)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[retraction_maps; CONTINUOUS_MAP_EUCLIDEAN2; I_THM] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_RADIAL_PROJECTION; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    REWRITE_TAC[IMAGE_I; I_DEF; CONTINUOUS_ON_ID] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[dist; VECTOR_ARITH `a - (a + x):real^N = --x`; NORM_NEG; NORM_MUL] THEN
    SUBGOAL_THEN `~(x:real^N = a)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(x - a:real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_DIV_RMUL;
                 REAL_LT_IMP_NZ];
    REWRITE_TAC[SUBSET_REFL];
    ASM_SIMP_TAC[IMAGE_CLAUSES; SUBSET_REFL];
    REWRITE_TAC[I_DEF] THEN MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR_IMAGE_SUBSET THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_RADIAL_PROJECTION; CONTINUOUS_ON_ID; IN_SING] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN DISCH_TAC THEN
    MATCH_MP_TAC RADIAL_SEGMENT_COMPLEMENT_CONVEX THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Relative homology of R^N modulo the complement of a                       *)
(* bounded convex set (that of a sphere, one degree lower), and the          *)
(* restriction maps between such pairs for nested convex sets.               *)
(* ========================================================================= *)

let GROUP_ISOMORPHISM_SQUARE = prove
 (`!A B C D (f:A->B) (g:C->D) (h:B->D) (k:A->C).
        group_homomorphism (A,B) f /\ group_isomorphism (B,D) h /\
        group_isomorphism (A,C) k /\ group_isomorphism (C,D) g /\
        (!x. x IN group_carrier A ==> h(f x) = g(k x))
        ==> group_isomorphism (A,B) f`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `h':D->B` o REWRITE_RULE[group_isomorphism] o
    check (fun th -> concl th = `group_isomorphism (B,D) (h:B->D)`)) THEN
  MATCH_MP_TAC GROUP_ISOMORPHISM_EQ THEN
  EXISTS_TAC `(h':D->B) o (g:C->D) o (k:A->C)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC GROUP_ISOMORPHISM_COMPOSE THEN EXISTS_TAC `D:D group` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GROUP_ISOMORPHISM_COMPOSE THEN EXISTS_TAC `C:C group` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC GROUP_ISOMORPHISMS_IMP_ISOMORPHISM THEN EXISTS_TAC `h:B->D` THEN
      ONCE_REWRITE_TAC[GROUP_ISOMORPHISMS_SYM] THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(g:C->D)((k:A->C) x) = (h:B->D)((f:A->B) x)` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:A->B) x IN group_carrier B` ASSUME_TAC THENL
     [ASM_MESON_TAC[group_homomorphism; SUBSET; FUN_IN_IMAGE]; ALL_TAC] THEN
    ASM_MESON_TAC[group_isomorphisms]]);;

let ISOMORPHIC_RELATIVE_HOMOLOGY_COMPLEMENT_CONVEX_SPHERE = prove
 (`!p k a:real^N r y.
        convex k /\ a IN k /\ k SUBSET ball(a,r) /\ y IN sphere(a,r)
        ==> relative_homology_group(p,euclidean,(:real^N) DIFF k) isomorphic_group
            relative_homology_group(p - &1,subtopology euclidean (sphere(a,r)),{y})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN (:real^N) DIFF k` ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^N->bool) SUBSET ball(a,r)` THEN
    UNDISCH_TAC `(y:real^N) IN sphere(a,r)` THEN
    REWRITE_TAC[SUBSET; IN_SPHERE; IN_BALL; IN_DIFF; IN_UNIV] THEN
    MESON_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`relative_homology_group(p,euclidean,(:real^N) DIFF k)`;
    `relative_homology_group(p - &1,subtopology euclidean ((:real^N) DIFF k),{y:real^N})`;
    `relative_homology_group(p - &1,subtopology euclidean (sphere(a:real^N,r)),{y})`]
   ISOMORPHIC_GROUP_TRANS) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GROUP_ISOMORPHISM_IMP_ISOMORPHIC THEN
    EXISTS_TAC `hom_relboundary p (euclidean,(:real^N) DIFF k,{y:real^N})` THEN
    MATCH_MP_TAC GROUP_ISOMORPHISM_HOM_RELBOUNDARY_CONTRACTIBLE THEN
    REWRITE_TAC[CONTRACTIBLE_SPACE_SUBTOPOLOGY_SING;
                REWRITE_RULE[SUBTOPOLOGY_UNIV; CONTRACTIBLE_UNIV]
                  (ISPEC `(:real^N)` CONTRACTIBLE_SPACE_EUCLIDEAN)] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN] THEN ASM SET_TAC[];
    ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    MATCH_MP_TAC GROUP_ISOMORPHISM_IMP_ISOMORPHIC THEN
    EXISTS_TAC `hom_induced (p - &1) (subtopology euclidean (sphere(a:real^N,r)),{y})
                  (subtopology euclidean ((:real^N) DIFF k),{y}) (\x. x)` THEN
    MATCH_MP_TAC GROUP_ISOMORPHISM_HOM_INDUCED_SPHERE_COMPLEMENT_CONVEX THEN
    ASM_REWRITE_TAC[]]);;

let ISOMORPHIC_RELATIVE_HOMOLOGY_COMPLEMENT_CONVEX = prove
 (`!p k:real^N->bool.
        bounded k /\ convex k /\ ~(k = {})
        ==> ?a:real^N r. &0 < r /\
                  relative_homology_group(p,euclidean,(:real^N) DIFF k) isomorphic_group
                  reduced_homology_group(p - &1,subtopology euclidean (sphere(a,r)))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `a:real^N`] BOUNDED_SUBSET_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a + r % basis 1 IN sphere(a:real^N,r)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE; dist; VECTOR_ARITH `a - (a + x):real^N = --x`; NORM_NEG;
                NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`relative_homology_group(p,euclidean,(:real^N) DIFF k)`;
    `relative_homology_group(p - &1,subtopology euclidean (sphere(a:real^N,r)),
                             {a + r % basis 1})`;
    `reduced_homology_group(p - &1,subtopology euclidean (sphere(a:real^N,r)))`]
   ISOMORPHIC_GROUP_TRANS) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ISOMORPHIC_RELATIVE_HOMOLOGY_COMPLEMENT_CONVEX_SPHERE THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC ISOMORPHIC_GROUP_RELATIVE_HOMOLOGY_BY_SING THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]]);;

let RELATIVE_HOMOLOGY_GROUP_COMPLEMENT_CONVEX = prove
 (`(!p k:real^N->bool.
        bounded k /\ convex k /\ ~(k = {}) /\ ~(p = &(dimindex(:N)))
        ==> trivial_group(relative_homology_group(p,euclidean,(:real^N) DIFF k))) /\
   (!k:real^N->bool.
        bounded k /\ convex k /\ ~(k = {})
        ==> relative_homology_group(&(dimindex(:N)),euclidean,(:real^N) DIFF k)
            isomorphic_group integer_group)`,
  SUBGOAL_THEN `&(dimindex(:N) - 1):int = &(dimindex(:N)) - &1` ASSUME_TAC THENL
   [SIMP_TAC[GSYM INT_OF_NUM_SUB; DIMINDEX_GE_1]; ALL_TAC] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`p:int`; `k:real^N->bool`]
                  ISOMORPHIC_RELATIVE_HOMOLOGY_COMPLEMENT_CONVEX) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `r:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ISOMORPHIC_GROUP_TRIVIALITY th]) THEN
    MATCH_MP_TAC(CONJUNCT2 REDUCED_HOMOLOGY_GROUP_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
    MP_TAC(ISPECL [`&(dimindex(:N)):int`; `k:real^N->bool`]
                  ISOMORPHIC_RELATIVE_HOMOLOGY_COMPLEMENT_CONVEX) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `r:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL
     [`relative_homology_group(&(dimindex(:N)),euclidean,(:real^N) DIFF k)`;
      `reduced_homology_group(&(dimindex(:N)) - &1,subtopology euclidean (sphere(a:real^N,r)))`;
      `integer_group`] ISOMORPHIC_GROUP_TRANS) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      type_of(lhs(concl th)) = `:int`)) THEN
    MATCH_MP_TAC(CONJUNCT1 REDUCED_HOMOLOGY_GROUP_SPHERE) THEN ASM_REWRITE_TAC[]]);;

let GROUP_ISOMORPHISM_HOM_INDUCED_COMPLEMENT_CONVEX = prove
 (`!p k l:real^N->bool.
        bounded k /\ convex k /\ convex l /\ ~(l = {}) /\ l SUBSET k
        ==> group_isomorphism
              (relative_homology_group(p,euclidean,(:real^N) DIFF k),
               relative_homology_group(p,euclidean,(:real^N) DIFF l))
              (hom_induced p (euclidean,(:real^N) DIFF k)
                             (euclidean,(:real^N) DIFF l) (\x. x))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `a:real^N`] BOUNDED_SUBSET_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `y:real^N = a + r % basis 1` THEN
  SUBGOAL_THEN `(y:real^N) IN sphere(a,r)` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN
    REWRITE_TAC[IN_SPHERE; dist; VECTOR_ARITH `a - (a + x):real^N = --x`; NORM_NEG;
                NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN k /\ l SUBSET ball(a,r)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^N) IN k)` ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^N->bool) SUBSET ball(a,r)` THEN
    UNDISCH_TAC `(y:real^N) IN sphere(a,r)` THEN
    REWRITE_TAC[SUBSET; IN_SPHERE; IN_BALL] THEN MESON_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^N) IN l)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sphere(a:real^N,r) SUBSET (:real^N) DIFF k` ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^N->bool) SUBSET ball(a,r)` THEN
    REWRITE_TAC[SUBSET; IN_SPHERE; IN_BALL; IN_DIFF; IN_UNIV] THEN
    MESON_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `contractible_space(euclidean:(real^N)topology)` ASSUME_TAC THENL
   [REWRITE_TAC[REWRITE_RULE[SUBTOPOLOGY_UNIV; CONTRACTIBLE_UNIV]
                  (ISPEC `(:real^N)` CONTRACTIBLE_SPACE_EUCLIDEAN)];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`relative_homology_group(p,euclidean,(:real^N) DIFF k)`;
    `relative_homology_group(p,euclidean,(:real^N) DIFF l)`;
    `relative_homology_group(p - &1,subtopology euclidean ((:real^N) DIFF k),{y:real^N})`;
    `relative_homology_group(p - &1,subtopology euclidean ((:real^N) DIFF l),{y:real^N})`]
   GROUP_ISOMORPHISM_SQUARE) THEN
  MAP_EVERY EXISTS_TAC
   [`hom_induced (p - &1) (subtopology euclidean ((:real^N) DIFF k),{y:real^N})
                 (subtopology euclidean ((:real^N) DIFF l),{y}) (\x. x)`;
    `hom_relboundary p (euclidean,(:real^N) DIFF l,{y:real^N})`;
    `hom_relboundary p (euclidean,(:real^N) DIFF k,{y:real^N})`] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GROUP_ISOMORPHISM_HOM_RELBOUNDARY_CONTRACTIBLE THEN
    ASM_REWRITE_TAC[CONTRACTIBLE_SPACE_SUBTOPOLOGY_SING; TOPSPACE_EUCLIDEAN] THEN
    REWRITE_TAC[SING_SUBSET; IN_DIFF; IN_UNIV; INTER_UNIV; NOT_INSERT_EMPTY] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC GROUP_ISOMORPHISM_HOM_RELBOUNDARY_CONTRACTIBLE THEN
    ASM_REWRITE_TAC[CONTRACTIBLE_SPACE_SUBTOPOLOGY_SING; TOPSPACE_EUCLIDEAN] THEN
    REWRITE_TAC[SING_SUBSET; IN_DIFF; IN_UNIV; INTER_UNIV; NOT_INSERT_EMPTY] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL
     [`hom_induced (p - &1) (subtopology euclidean (sphere(a:real^N,r)),{y:real^N})
                   (subtopology euclidean ((:real^N) DIFF k),{y}) (\x. x)`;
      `hom_induced (p - &1) (subtopology euclidean ((:real^N) DIFF k),{y:real^N})
                   (subtopology euclidean ((:real^N) DIFF l),{y}) (\x. x)`;
      `relative_homology_group(p - &1,subtopology euclidean (sphere(a:real^N,r)),{y:real^N})`;
      `relative_homology_group(p - &1,subtopology euclidean ((:real^N) DIFF k),{y:real^N})`;
      `relative_homology_group(p - &1,subtopology euclidean ((:real^N) DIFF l),{y:real^N})`]
     GROUP_EPIMORPHISM_ISOMORPHISM_COMPOSE_REV) THEN
    REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GROUP_ISOMORPHISM_IMP_EPIMORPHISM THEN
      MATCH_MP_TAC GROUP_ISOMORPHISM_HOM_INDUCED_SPHERE_COMPLEMENT_CONVEX THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; CONTINUOUS_ON_ID; IMAGE_ID] THEN
      ASM SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    REWRITE_TAC[o_DEF; ETA_AX] THEN
    MATCH_MP_TAC GROUP_ISOMORPHISM_HOM_INDUCED_SPHERE_COMPLEMENT_CONVEX THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `c:((num->real)->real^N)frag->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`p:int`; `euclidean:(real^N)topology`; `(:real^N) DIFF k`; `{y:real^N}`;
      `euclidean:(real^N)topology`; `(:real^N) DIFF l`; `{y:real^N}`; `\x:real^N. x`]
     NATURALITY_HOM_INDUCED_RELBOUNDARY) THEN
    REWRITE_TAC[CONTINUOUS_MAP_ID; IMAGE_ID] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C AP_THM `c:((num->real)->real^N)frag->bool`) THEN
    REWRITE_TAC[o_THM]]);;

(* ========================================================================= *)
(* G2, the local homology of R^N.                                            *)
(* ========================================================================= *)

let ATOP_EUCLIDEAN_LOCAL_HOMOLOGY = prove
 (`ATOP_EUCLIDEAN_LOCAL_HOMOLOGY_STATEMENT (:N)`,
  REWRITE_TAC[ATOP_EUCLIDEAN_LOCAL_HOMOLOGY_STATEMENT] THEN
  SUBGOAL_THEN `!x:real^N. (:real^N) DELETE x = (:real^N) DIFF {x}`
  (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(CONJUNCT1 RELATIVE_HOMOLOGY_GROUP_COMPLEMENT_CONVEX) THEN
    ASM_REWRITE_TAC[BOUNDED_SING; CONVEX_SING; NOT_INSERT_EMPTY];
    GEN_TAC THEN MATCH_MP_TAC(CONJUNCT2 RELATIVE_HOMOLOGY_GROUP_COMPLEMENT_CONVEX) THEN
    REWRITE_TAC[BOUNDED_SING; CONVEX_SING; NOT_INSERT_EMPTY];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ISOMORPHISM_HOM_INDUCED_COMPLEMENT_CONVEX THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; CONVEX_SING; NOT_INSERT_EMPTY; SING_SUBSET]]);;

(* ========================================================================= *)
(* M2, local homology of topological manifolds: excision                    *)
(* of the complement of a chart, and transport along the chart.             *)
(* ========================================================================= *)

let ATOP_EXCISION_CLOSED = prove
 (`!p top (w:A->bool) k.
        open_in top w /\ closed_in top k /\ k SUBSET w
        ==> group_isomorphism
              (relative_homology_group(p,subtopology top w,w DIFF k),
               relative_homology_group(p,top,topspace top DIFF k))
              (hom_induced p (subtopology top w,w DIFF k)
                             (top,topspace top DIFF k) (\x. x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(w:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:int`; `top:A topology`; `topspace top:A->bool`;
                 `topspace top DIFF (k:A->bool)`; `topspace top DIFF w:A->bool`]
                HOMOLOGY_EXCISION_AXIOM) THEN
  REWRITE_TAC[SUBTOPOLOGY_TOPSPACE] THEN
  SUBGOAL_THEN `topspace top DIFF (topspace top DIFF w) = w:A->bool /\
                (topspace top DIFF k) DIFF (topspace top DIFF w) = w DIFF (k:A->bool)`
  (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[SUBSET_DIFF] THEN
  SUBGOAL_THEN `top closure_of (topspace top DIFF w) = topspace top DIFF (w:A->bool) /\
                top interior_of (topspace top DIFF k) = topspace top DIFF (k:A->bool)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[CLOSURE_OF_EQ] THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
      ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE];
      REWRITE_TAC[INTERIOR_OF_EQ] THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
      ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]];
    ASM SET_TAC[]]);;

let ATOP_CHART_FACTS = prove
 (`!top u (h:A->real^N) g.
        open_in top u /\ homeomorphic_maps (subtopology top u,euclidean) (h,g)
        ==> u SUBSET topspace top /\
            topspace(subtopology top u) = u /\
            continuous_map (subtopology top u,euclidean) h /\
            continuous_map (euclidean,subtopology top u) g /\
            continuous_map (euclidean,top) g /\
            homeomorphic_map (subtopology top u,euclidean) h /\
            (!x. x IN u ==> g(h x) = x) /\ (!y. h(g y) = y) /\ (!y. g y IN u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace(subtopology top u) = u:A->bool` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ASSUME `homeomorphic_maps (subtopology top u,euclidean) (h:A->real^N,g)`) THEN
  REWRITE_TAC[HOMEOMORPHIC_MAPS_MAP] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `homeomorphic_maps (subtopology top u,euclidean) (h:A->real^N,g)`) THEN
  REWRITE_TAC[homeomorphic_maps] THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^N. (g:real^N->A) y IN u` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (fun th -> concl th =
        `continuous_map (euclidean,subtopology top u) (g:real^N->A)`)) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (euclidean,top) (g:real^N->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
    EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `!x. x IN topspace (subtopology top u)
                     ==> (g:real^N->A) ((h:A->real^N) x) = x` THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `!y. y IN topspace euclidean
                     ==> (h:A->real^N) ((g:real^N->A) y) = y` THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV]]);;

let ATOP_CHART_LOCAL_HOMOLOGY_ISO = prove
 (`!p top u (h:A->real^N) g k y.
        hausdorff_space top /\ open_in top u /\
        homeomorphic_maps (subtopology top u,euclidean) (h,g) /\
        compact k /\ convex k /\ y IN IMAGE g k
        ==> group_isomorphism
              (relative_homology_group(p,top,topspace top DIFF IMAGE g k),
               relative_homology_group(p,top,topspace top DELETE y))
              (hom_induced p (top,topspace top DIFF IMAGE g k)
                             (top,topspace top DELETE y) (\x. x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `u:A->bool`; `h:A->real^N`; `g:real^N->A`]
                ATOP_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (g:real^N->A) k SUBSET u` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (IMAGE (g:real^N->A) k)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `euclidean:(real^N)topology` THEN
    ASM_REWRITE_TAC[COMPACT_IN_EUCLIDEAN];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN u /\ (h:A->real^N) y IN k` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN IMAGE (g:real^N->A) k` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:A->real^N) (u DIFF IMAGE g k) = (:real^N) DIFF k`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF; IN_UNIV] THEN X_GEN_TAC `z:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(?x. (w:A) = g x /\ (x:real^N) IN k)` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `(h:A->real^N) w` THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `(g:real^N->A) z` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~((z:real^N) IN k)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `z:real^N = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `h:A->real^N`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:A->real^N) (u DELETE y) = (:real^N) DELETE h y`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV] THEN X_GEN_TAC `z:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `~((w:A) = y)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `g:real^N->A`) THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `(g:real^N->A) z` THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `~((z:real^N) = h(y:A))` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `h:A->real^N`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1_space (top:A topology)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_IMP_T1_SPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:int`; `top:A topology`; `u:A->bool`; `IMAGE (g:real^N->A) k`]
                ATOP_EXCISION_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:int`; `top:A topology`; `u:A->bool`; `y:A`] ATOP_EXCISION_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:int`; `subtopology top (u:A->bool)`; `euclidean:(real^N)topology`;
                 `u DIFF IMAGE (g:real^N->A) k`; `(:real^N) DIFF k`; `h:A->real^N`]
                HOMEOMORPHIC_MAP_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`p:int`; `subtopology top (u:A->bool)`; `euclidean:(real^N)topology`;
                 `u DELETE (y:A)`; `(:real^N) DELETE (h:A->real^N) y`; `h:A->real^N`]
                HOMEOMORPHIC_MAP_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`p:int`; `k:real^N->bool`; `{(h:A->real^N) y}`]
                GROUP_ISOMORPHISM_HOM_INDUCED_COMPLEMENT_CONVEX) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; CONVEX_SING; NOT_INSERT_EMPTY; SING_SUBSET] THEN
  REWRITE_TAC[SET_RULE `(:real^N) DIFF {a} = (:real^N) DELETE a`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `group_isomorphism
      (relative_homology_group(p,subtopology top u,u DIFF IMAGE (g:real^N->A) k),
       relative_homology_group(p,subtopology top u,u DELETE (y:A)))
      (hom_induced p (subtopology top u,u DIFF IMAGE g k)
                     (subtopology top u,u DELETE y) (\x. x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL
     [`relative_homology_group(p,subtopology top u,u DIFF IMAGE (g:real^N->A) k)`;
      `relative_homology_group(p,subtopology top u,u DELETE (y:A))`;
      `relative_homology_group(p,euclidean,(:real^N) DIFF k)`;
      `relative_homology_group(p,euclidean,(:real^N) DELETE (h:A->real^N) y)`]
     GROUP_ISOMORPHISM_SQUARE) THEN
    MAP_EVERY EXISTS_TAC
     [`hom_induced p (euclidean,(:real^N) DIFF k)
                     (euclidean,(:real^N) DELETE (h:A->real^N) y) (\x. x)`;
      `hom_induced p (subtopology top u,u DELETE (y:A))
                     (euclidean,(:real^N) DELETE (h:A->real^N) y) h`;
      `hom_induced p (subtopology top u,u DIFF IMAGE (g:real^N->A) k)
                     (euclidean,(:real^N) DIFF k) (h:A->real^N)`] THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED] THEN
    X_GEN_TAC `c:((num->real)->A)frag->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p:int`; `subtopology top (u:A->bool)`; `u DIFF IMAGE (g:real^N->A) k`;
                   `euclidean:(real^N)topology`; `(:real^N) DIFF k`;
                   `euclidean:(real^N)topology`; `(:real^N) DELETE (h:A->real^N) y`;
                   `h:A->real^N`; `\x:real^N. x`] HOM_INDUCED_COMPOSE) THEN
    MP_TAC(ISPECL [`p:int`; `subtopology top (u:A->bool)`; `u DIFF IMAGE (g:real^N->A) k`;
                   `subtopology top (u:A->bool)`; `u DELETE (y:A)`;
                   `euclidean:(real^N)topology`; `(:real^N) DELETE (h:A->real^N) y`;
                   `\x:A. x`; `h:A->real^N`] HOM_INDUCED_COMPOSE) THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_ID; IMAGE_ID] THEN
    SUBGOAL_THEN `(h:A->real^N) o (\x. x) = h /\ (\x:real^N. x) o h = h`
    (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C AP_THM `c:((num->real)->A)frag->bool`) THEN
    REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`hom_induced p (subtopology top u,u DIFF IMAGE (g:real^N->A) k)
                   (top,topspace top DIFF IMAGE g k) (\x:A. x)`;
    `hom_induced p (top,topspace top DIFF IMAGE (g:real^N->A) k)
                   (top,topspace top DELETE (y:A)) (\x:A. x)`;
    `relative_homology_group(p,subtopology top u,u DIFF IMAGE (g:real^N->A) k)`;
    `relative_homology_group(p,top,topspace top DIFF IMAGE (g:real^N->A) k)`;
    `relative_homology_group(p,top,topspace top DELETE (y:A))`]
   GROUP_EPIMORPHISM_ISOMORPHISM_COMPOSE_REV) THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GROUP_ISOMORPHISM_IMP_EPIMORPHISM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:int`; `subtopology top (u:A->bool)`; `u DIFF IMAGE (g:real^N->A) k`;
                 `top:A topology`; `topspace top DIFF IMAGE (g:real^N->A) k`;
                 `top:A topology`; `topspace top DELETE (y:A)`; `\x:A. x`; `\x:A. x`]
                HOM_INDUCED_COMPOSE) THEN
  MP_TAC(ISPECL [`p:int`; `subtopology top (u:A->bool)`; `u DIFF IMAGE (g:real^N->A) k`;
                 `subtopology top (u:A->bool)`; `u DELETE (y:A)`;
                 `top:A topology`; `topspace top DELETE (y:A)`; `\x:A. x`; `\x:A. x`]
                HOM_INDUCED_COMPOSE) THEN
  SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID; IMAGE_ID] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC GROUP_ISOMORPHISM_COMPOSE THEN
  EXISTS_TAC `relative_homology_group(p,subtopology top u,u DELETE (y:A))` THEN
  ASM_REWRITE_TAC[]);;

let ATOP_CHART_LOCAL_HOMOLOGY_POINT = prove
 (`!p top u (h:A->real^N) g y.
        hausdorff_space top /\ open_in top u /\
        homeomorphic_maps (subtopology top u,euclidean) (h,g) /\ y IN u
        ==> relative_homology_group(p,top,topspace top DELETE y) isomorphic_group
            relative_homology_group(p,euclidean,(:real^N) DELETE h y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `u:A->bool`; `h:A->real^N`; `g:real^N->A`]
                ATOP_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL
   [`relative_homology_group(p,top,topspace top DELETE (y:A))`;
    `relative_homology_group(p,subtopology top u,u DELETE (y:A))`;
    `relative_homology_group(p,euclidean,(:real^N) DELETE (h:A->real^N) y)`]
   ISOMORPHIC_GROUP_TRANS) THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    MATCH_MP_TAC GROUP_ISOMORPHISM_IMP_ISOMORPHIC THEN
    EXISTS_TAC `hom_induced p (subtopology top u,u DELETE (y:A))
                              (top,topspace top DELETE y) (\x. x)` THEN
    MATCH_MP_TAC ATOP_EXCISION_POINT THEN ASM_SIMP_TAC[HAUSDORFF_IMP_T1_SPACE];
    MATCH_MP_TAC GROUP_ISOMORPHISM_IMP_ISOMORPHIC THEN
    EXISTS_TAC `hom_induced p (subtopology top u,u DELETE (y:A))
                              (euclidean,(:real^N) DELETE (h:A->real^N) y) h` THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISM THEN
    ASM_REWRITE_TAC[DELETE_SUBSET] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV] THEN X_GEN_TAC `z:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `~((w:A) = y)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `g:real^N->A`) THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `(g:real^N->A) z` THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `~((z:real^N) = h(y:A))` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `h:A->real^N`) THEN ASM_REWRITE_TAC[]]]);;

let ATOP_MANIFOLD_LOCAL_HOMOLOGY = prove
 (`ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT (:A) (:N)`,
  REWRITE_TAC[ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `x:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o REWRITE_RULE[locally_euclidean_space]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[homeomorphic_space; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:A->real^N`; `g:real^N->A`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `u:A->bool`; `h:A->real^N`; `g:real^N->A`]
                ATOP_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC ATOP_EUCLIDEAN_LOCAL_HOMOLOGY THEN
  REWRITE_TAC[ATOP_EUCLIDEAN_LOCAL_HOMOLOGY_STATEMENT] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `p:int` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p:int`; `top:A topology`; `u:A->bool`; `h:A->real^N`;
                   `g:real^N->A`; `x:A`] ATOP_CHART_LOCAL_HOMOLOGY_POINT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP ISOMORPHIC_GROUP_TRIVIALITY th]) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC(ISPECL
     [`relative_homology_group(&(dimindex(:N)),top,topspace top DELETE (x:A))`;
      `relative_homology_group(&(dimindex(:N)),euclidean,
                               (:real^N) DELETE (h:A->real^N) x)`;
      `integer_group`] ISOMORPHIC_GROUP_TRANS) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ATOP_CHART_LOCAL_HOMOLOGY_POINT THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `g:real^N->A`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC
     [`IMAGE (g:real^N->A) (ball((h:A->real^N) x,&1))`;
      `IMAGE (g:real^N->A) (cball((h:A->real^N) x,&1))`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `u:A->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `homeomorphic_maps (subtopology top u,euclidean)
                                       (h:A->real^N,g)`) THEN
      REWRITE_TAC[HOMEOMORPHIC_MAPS_MAP] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`g:real^N->A`; `euclidean:(real^N)topology`;
                     `subtopology top (u:A->bool)`; `ball((h:A->real^N) x,&1)`]
                    HOMEOMORPHIC_MAP_OPENNESS) THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; SUBSET_UNIV; GSYM OPEN_IN; OPEN_BALL];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h:A->real^N) x` THEN
      ASM_SIMP_TAC[CENTRE_IN_BALL; REAL_LT_01];
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `euclidean:(real^N)topology` THEN
      ASM_REWRITE_TAC[COMPACT_IN_EUCLIDEAN; COMPACT_CBALL];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC ATOP_CHART_LOCAL_HOMOLOGY_ISO THEN
      MAP_EVERY EXISTS_TAC [`u:A->bool`; `h:A->real^N`] THEN
      ASM_REWRITE_TAC[COMPACT_CBALL; CONVEX_CBALL]]]);;


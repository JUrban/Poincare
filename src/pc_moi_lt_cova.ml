(* ========================================================================= *)
(* pc_moi_lt_cova: Moise GTM 47, the tower of the loop theorem (p.189,       *)
(* 24.1, 24.6): simplicial coverings (lt_cover_a). Main theorems             *)
(* COVER_LIFT_CELLWISE, COVER_BOUNDARY, DESCENT_INPUT (the statement terms   *)
(* MOI_LT_COVER_LIFT_CELLWISE, MOI_LT_COVER_BOUNDARY, MOI_LT_DESCENT_INPUT   *)
(* of pc_moi_loop_stmt.ml). Route: a covering map is locally injective and a *)
(* simplicial map is affine on simplices, so q is injective on simplices,    *)
(* two simplices of c' with the same image that meet are equal, and a        *)
(* connected set over the relative interior of a simplex s of c lies in one  *)
(* lift of s (the sheet lemmas, also used by pc_moi_lt_coverb).              *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt.ml";;
needs "src/pc_moi_fnd_m3b.ml";;

prioritize_real();;
type_invention_error := true;;



(* ------------------------------------------------------------------------- *)
(* The sheet lemmas, generic for a simplicial map q of lf complexes c' -> c  *)
(* that is a covering map of the polyhedra. A covering map is locally        *)
(* injective (MOI_LCA_LOCAL_INJ); comparing two segments from a common point *)
(* (MOI_LCA_SEGMENT) shows that q is injective on each simplex of c' and     *)
(* that two simplices of c' with the same image that meet are equal. A       *)
(* connected set over the relative interior of a simplex s of c lies in one  *)
(* lift of s (MOI_LCA_SHEET); every point over s lies in a lift of s         *)
(* (MOI_LCA_POINT_LIFT, lifting the inclusion of s).                         *)
(* ------------------------------------------------------------------------- *)

let MOI_LCA_LOCAL_INJ = prove
 (`!(p:real^M->real^N) c s z.
     covering_space (c,p) s /\ z IN c
     ==> ?e. &0 < e /\
             !x y. x IN c /\ y IN c /\ dist(z,x) < e /\ dist(z,y) < e /\ p x = p y
                   ==> x = y`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M` o MATCH_MP COVERING_SPACE_LOCAL_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` (X_CHOOSE_THEN `u:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `open_in (subtopology euclidean c) (t:real^M->bool)` THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^M` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
  UNDISCH_TAC `homeomorphism (t,u) (p:real^M->real^N,q)` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^M) IN t /\ (y:real^M) IN t` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ball(z:real^M,e) INTER c SUBSET t` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_LCA_SMALL_T = prove
 (`!a b e. &0 <= a /\ &0 <= b /\ &0 < e
           ==> ?t. &0 < t /\ t <= &1 /\ t * a < e /\ t * b < e`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = e / (a + b + &1)` THEN
  SUBGOAL_THEN `&0 < d /\ d * (a + b + &1) = e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min (&1) d` THEN
  SUBGOAL_THEN `min (&1) d * a <= d * a /\ min (&1) d * b <= d * b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d * a < d * (a + b + &1) /\ d * b < d * (a + b + &1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_LCA_AFFINE_COMB = prove
 (`!(f:real^M->real^N) l y k a b t.
     linear l /\ (!x. x IN k ==> f x = l x + y) /\ a IN k /\ b IN k /\
     (&1 - t) % a + t % b IN k
     ==> f((&1 - t) % a + t % b) = (&1 - t) % f a + t % f b`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN VECTOR_ARITH_TAC);;

(* The core: two convex pieces on which q is affine, a common point z, and   *)
(* points u, u2 with the same image: compare (1-t)z + tu and (1-t)z + tu2.  *)

let MOI_LCA_SEGMENT = prove
 (`!(q:real^M->real^N) c s L1 L2 l1 y1 l2 y2 z u u2.
     covering_space (c,q) s /\ L1 SUBSET c /\ L2 SUBSET c /\ convex L1 /\ convex L2 /\
     linear l1 /\ (!x. x IN L1 ==> q x = l1 x + y1) /\
     linear l2 /\ (!x. x IN L2 ==> q x = l2 x + y2) /\
     z IN L1 /\ z IN L2 /\ u IN L1 /\ u2 IN L2 /\ q u = q u2
     ==> u = u2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`q:real^M->real^N`; `c:real^M->bool`; `s:real^N->bool`; `z:real^M`]
    MOI_LCA_LOCAL_INJ) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj"))) THEN
  MP_TAC(ISPECL [`norm(u - z:real^M)`; `norm(u2 - z:real^M)`; `e:real`] MOI_LCA_SMALL_T) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(&1 - t) % z + t % u:real^M IN L1 /\ (&1 - t) % z + t % u2:real^M IN L2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] (ASSUME `convex(L1:real^M->bool)`));
      MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] (ASSUME `convex(L2:real^M->bool)`))] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^M->real^N) ((&1 - t) % z + t % u) = (&1 - t) % q z + t % q u /\
                q ((&1 - t) % z + t % u2) = (&1 - t) % q z + t % q u2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LCA_AFFINE_COMB THENL
     [MAP_EVERY EXISTS_TAC [`l1:real^M->real^N`; `y1:real^N`; `L1:real^M->bool`];
      MAP_EVERY EXISTS_TAC [`l2:real^M->real^N`; `y2:real^N`; `L2:real^M->bool`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - t) % z + t % u:real^M = (&1 - t) % z + t % u2` MP_TAC THENL
   [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM SET_TAC[];
      REWRITE_TAC[dist; VECTOR_ARITH `z - ((&1 - t) % z + t % u):real^M = t % (z - u)`;
                  NORM_MUL] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`];
      REWRITE_TAC[dist; VECTOR_ARITH `z - ((&1 - t) % z + t % u):real^M = t % (z - u)`;
                  NORM_MUL] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`]];
    DISCH_TAC THEN
    SUBGOAL_THEN `t % (u - u2):real^M = vec 0` MP_TAC THENL
     [UNDISCH_TAC `(&1 - t) % z + t % u:real^M = (&1 - t) % z + t % u2` THEN
      VECTOR_ARITH_TAC;
      ASM_SIMP_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; REAL_LT_IMP_NZ]]]);;

let MOI_LCA_SIMPLEX_INJ = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q t.
     lf_simplicial_complex c' /\ simplicial_map_on c' c q /\
     covering_space (UNIONS c',q) (UNIONS c) /\ t IN c'
     ==> !x y. x IN t /\ y IN t /\ q x = q y ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `t:real^M->bool` (REWRITE_RULE[simplicial_map_on]
    (ASSUME `simplicial_map_on c' (c:(real^N->bool)->bool) (q:real^M->real^N)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y0:real^N`
    STRIP_ASSUME_TAC) o CONJUNCT2) THEN
  SUBGOAL_THEN `(t:real^M->bool) SUBSET UNIONS c' /\ convex t` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[MOI_FM3_LF_CONVEX]]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_LCA_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`q:real^M->real^N`; `UNIONS c':real^M->bool`;
    `UNIONS c:real^N->bool`; `t:real^M->bool`; `t:real^M->bool`;
    `l:real^M->real^N`; `y0:real^N`; `l:real^M->real^N`; `y0:real^N`; `x:real^M`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_LCA_LIFT_UNIQUE = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q L1 L2.
     lf_simplicial_complex c' /\ simplicial_map_on c' c q /\
     covering_space (UNIONS c',q) (UNIONS c) /\ L1 IN c' /\ L2 IN c' /\
     IMAGE q L1 = IMAGE q L2 /\ ~DISJOINT L1 L2
     ==> L1 = L2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!A B:real^M->bool. A IN c' /\ B IN c' /\ IMAGE (q:real^M->real^N) A = IMAGE q B /\
                       ~DISJOINT A B ==> A SUBSET B`
  (fun th -> MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN MATCH_MP_TAC th THEN
             ASM_REWRITE_TAC[] THEN ASM SET_TAC[]) THEN
  MAP_EVERY X_GEN_TAC [`A:real^M->bool`; `B:real^M->bool`] THEN STRIP_TAC THEN
  UNDISCH_TAC `~DISJOINT (A:real^M->bool) B` THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^M` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `u:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?u2:real^M. u2 IN B /\ (q:real^M->real^N) u = q u2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (q:real^M->real^N) A = IMAGE q B` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `(q:real^M->real^N) u`) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `A:real^M->bool` (REWRITE_RULE[simplicial_map_on]
    (ASSUME `simplicial_map_on c' (c:(real^N->bool)->bool) (q:real^M->real^N)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lA:real^M->real^N` (X_CHOOSE_THEN `yA:real^N`
    STRIP_ASSUME_TAC) o CONJUNCT2) THEN
  MP_TAC(ISPEC `B:real^M->bool` (REWRITE_RULE[simplicial_map_on]
    (ASSUME `simplicial_map_on c' (c:(real^N->bool)->bool) (q:real^M->real^N)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lB:real^M->real^N` (X_CHOOSE_THEN `yB:real^N`
    STRIP_ASSUME_TAC) o CONJUNCT2) THEN
  SUBGOAL_THEN `(A:real^M->bool) SUBSET UNIONS c' /\ B SUBSET UNIONS c' /\
                convex A /\ convex B`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[];
      ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ASM_MESON_TAC[MOI_FM3_LF_CONVEX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `u:real^M = u2` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MOI_LCA_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`q:real^M->real^N`; `UNIONS c':real^M->bool`;
    `UNIONS c:real^N->bool`; `A:real^M->bool`; `B:real^M->bool`;
    `lA:real^M->real^N`; `yA:real^N`; `lB:real^M->real^N`; `yB:real^N`; `z:real^M`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_LCA_LIFT_INVERSE = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q t.
     lf_simplicial_complex c' /\ simplicial_map_on c' c q /\
     covering_space (UNIONS c',q) (UNIONS c) /\ t IN c'
     ==> ?l' y'. linear l' /\ !x. x IN t ==> l'(q x) + y' = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:real^M->bool` (REWRITE_RULE[simplicial_map_on]
    (ASSUME `simplicial_map_on c' (c:(real^N->bool)->bool) (q:real^M->real^N)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC) o CONJUNCT2) THEN
  MP_TAC(ISPECL [`l:real^M->real^N`; `y:real^N`; `t:real^M->bool`]
    MOI_PLM_AFFINE_INJECTIVE_LEFT_INVERSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_CONVEX];
      MAP_EVERY X_GEN_TAC [`x:real^M`; `x':real^M`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`;
                     `q:real^M->real^N`; `t:real^M->bool`] MOI_LCA_SIMPLEX_INJ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l':real^N->real^M` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y':real^M` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

let MOI_LCA_AFFINE_AFF_DIM_LE = prove
 (`!(f:real^M->real^N) l y s.
     linear l /\ (!x. x IN s ==> f x = l x + y) ==> aff_dim (IMAGE f s) <= aff_dim s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) s = IMAGE (\x. y + x) (IMAGE l s)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[VECTOR_ADD_SYM]; ALL_TAC] THEN
  REWRITE_TAC[AFF_DIM_TRANSLATION_EQ] THEN ASM_SIMP_TAC[AFF_DIM_LINEAR_IMAGE_LE]);;

let MOI_LCA_AFF_DIM = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q t.
     lf_simplicial_complex c' /\ simplicial_map_on c' c q /\
     covering_space (UNIONS c',q) (UNIONS c) /\ t IN c'
     ==> aff_dim (IMAGE q t) = aff_dim t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:real^M->bool` (REWRITE_RULE[simplicial_map_on]
    (ASSUME `simplicial_map_on c' (c:(real^N->bool)->bool) (q:real^M->real^N)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC) o CONJUNCT2) THEN
  MP_TAC(ISPECL [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^M->real^N`;
                 `t:real^M->bool`] MOI_LCA_LIFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^M` (X_CHOOSE_THEN `y':real^M`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LCA_AFFINE_AFF_DIM_LE THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `t = IMAGE (\z. (l':real^N->real^M) z + y') (IMAGE (q:real^M->real^N) t)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_LCA_AFFINE_AFF_DIM_LE THEN
    MAP_EVERY EXISTS_TAC [`l':real^N->real^M`; `y':real^M`] THEN ASM_REWRITE_TAC[]]);;

let MOI_LCA_AFFINE_RELINT = prove
 (`!(f:real^M->real^N) l y k.
     linear l /\ convex k /\ (!x. x IN k ==> f x = l x + y)
     ==> relative_interior (IMAGE f k) = IMAGE f (relative_interior k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. u SUBSET k ==> IMAGE (f:real^M->real^N) u = IMAGE (\x. y + x) (IMAGE l u)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[VECTOR_ADD_SYM]; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET_REFL] THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_TRANSLATION; RELATIVE_INTERIOR_LINEAR_IMAGE_CONVEX]);;

let MOI_LCA_OVER_RELINT = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q s x.
     lf_simplicial_complex c' /\ lf_simplicial_complex c /\ simplicial_map_on c' c q /\
     s IN c /\ x IN UNIONS c' /\ q x IN relative_interior s
     ==> ?L. L IN c' /\ IMAGE q L = s /\ x IN L`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?t:real^M->bool. t IN c' /\ x IN relative_interior t` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^M) IN UNIONS c'` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real^M->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t0:real^M->bool`; `x:real^M`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `t0:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^M) IN t /\ (q:real^M->real^N) x IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `t:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `t:real^M->bool` (REWRITE_RULE[simplicial_map_on]
    (ASSUME `simplicial_map_on c' (c:(real^N->bool)->bool) (q:real^M->real^N)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `l:real^M->real^N`
    (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(q:real^M->real^N) x IN relative_interior (IMAGE q t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`q:real^M->real^N`; `l:real^M->real^N`; `y:real^N`; `t:real^M->bool`]
      MOI_LCA_AFFINE_RELINT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^M->real^N) x IN IMAGE q t` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `(q:real^M->real^N) x`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_LCA_SHEET = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q s S.
     FINITE c' /\ lf_simplicial_complex c' /\ lf_simplicial_complex c /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c) /\
     s IN c /\ connected S /\ ~(S = {}) /\ S SUBSET UNIONS c' /\
     IMAGE q S SUBSET relative_interior s
     ==> ?L. L IN c' /\ IMAGE q L = s /\ S SUBSET L`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Ls = {L:real^M->bool | L IN c' /\ IMAGE (q:real^M->real^N) L = s}` THEN
  SUBGOAL_THEN `!L:real^M->bool. L IN Ls <=> L IN c' /\ IMAGE (q:real^M->real^N) L = s`
  ASSUME_TAC THENL
   [EXPAND_TAC "Ls" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (Ls:(real^M->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c':(real^M->bool)->bool` THEN
    ASM_SIMP_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^M. x IN S ==> ?L. L IN Ls /\ x IN L` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN ASM_REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC MOI_LCA_OVER_RELINT THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!L1 L2:real^M->bool. L1 IN Ls /\ L2 IN Ls /\ ~(L1 = L2) ==> DISJOINT L1 L2`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `DISJOINT (L1:real^M->bool) L2` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(L1:real^M->bool = L2)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_LCA_LIFT_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`;
                          `q:real^M->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(S:real^M->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x0:real^M`) THEN
  SUBGOAL_THEN `?L0:real^M->bool. L0 IN Ls /\ x0 IN L0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `L0:real^M->bool` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `connected (S:real^M->bool)` THEN REWRITE_TAC[CONNECTED_CLOSED_IN] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`S INTER (L0:real^M->bool)`;
                             `S INTER UNIONS (Ls DELETE (L0:real^M->bool))`]) THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ c /\ d /\ e /\ (f ==> g)
                     ==> ~(a /\ b /\ c /\ d /\ e /\ ~f) ==> g`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN
    ASM_MESON_TAC[MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED];
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
    ASM_MESON_TAC[MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED];
    REWRITE_TAC[SUBSET; IN_UNION; IN_INTER; IN_UNIONS; IN_DELETE] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC(SET_RULE `(!x:real^M. x IN L0 /\ x IN u ==> F)
                           ==> (S INTER L0) INTER (S INTER u) = {}`) THEN
    REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN X_GEN_TAC `x:real^M` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^M->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `DISJOINT (L0:real^M->bool) t` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ASM SET_TAC[]];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x0:real^M` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?L:real^M->bool. L IN Ls /\ x IN L` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `L:real^M->bool = L0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `S INTER UNIONS (Ls DELETE L0) = {}:real^M->bool` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_DELETE; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_MESON_TAC[]]);;

let MOI_LCA_SHEET_CLOSED = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q s (g:real^P->real^M) K.
     FINITE c' /\ lf_simplicial_complex c' /\ lf_simplicial_complex c /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c) /\
     s IN c /\ closed K /\ convex K /\ ~(K = {}) /\ g continuous_on K /\
     IMAGE g K SUBSET UNIONS c' /\
     IMAGE (q o g) (relative_interior K) SUBSET relative_interior s
     ==> ?L. L IN c' /\ IMAGE q L = s /\ IMAGE g K SUBSET L`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^M->real^N`;
                 `s:real^N->bool`; `IMAGE (g:real^P->real^M) (relative_interior K)`]
    MOI_LCA_SHEET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; RELATIVE_INTERIOR_SUBSET];
        ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_RELATIVE_INTERIOR]];
      ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY];
      MP_TAC(ISPEC `K:real^P->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[GSYM IMAGE_o]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `L:real^M->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `K = closure (relative_interior K:real^P->bool)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
  MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED] THEN
  ASM_MESON_TAC[MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED]);;

let MOI_LCA_POINT_LIFT = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q s x.
     FINITE c' /\ lf_simplicial_complex c' /\ lf_simplicial_complex c /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c) /\
     s IN c /\ x IN UNIONS c' /\ q x IN s
     ==> ?L. L IN c' /\ IMAGE q L = s /\ x IN L`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex (s:real^N->bool) /\ closed s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_CONVEX; MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^M->real^N`; `UNIONS c':real^M->bool`; `UNIONS c:real^N->bool`;
                 `\y:real^N. y`; `s:real^N->bool`; `x:real^M`; `(q:real^M->real^N) x`]
    COVERING_SPACE_LIFT_STRONG) THEN
  ASM_SIMP_TAC[CONVEX_IMP_SIMPLY_CONNECTED; CONVEX_IMP_LOCALLY_PATH_CONNECTED;
               CONTINUOUS_ON_ID; IMAGE_ID] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^M->real^N`;
                 `s:real^N->bool`; `g:real^N->real^M`; `s:real^N->bool`]
    MOI_LCA_SHEET_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `L:real^M->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:real^M) = g((q:real^M->real^N) x)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM SET_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* COVER_LIFT_CELLWISE.  The lift f2 of f exists because                    *)
(* std_triangle is simply connected and locally path connected; on a cell  *)
(* r of f the lift lies in one lift L of the simplex f(r) (SHEET_CLOSED),   *)
(* equals the affine left inverse of q on L composed with f, and maps r    *)
(* onto L.  The same cells serve for f2; the empty cell maps to {} IN c'.   *)
(* ------------------------------------------------------------------------- *)

let MOI_LCA_CELL_LIFT = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q (f:real^P->real^N) g r.
     FINITE c' /\ lf_simplicial_complex c' /\ lf_simplicial_complex c /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c) /\
     polytope r /\ ~(r = {}) /\ IMAGE f r IN c /\
     (?l y. linear l /\ !x. x IN r ==> f x = l x + y) /\
     g continuous_on r /\ IMAGE g r SUBSET UNIONS c' /\ (!x. x IN r ==> q(g x) = f x)
     ==> IMAGE g r IN c' /\ ?l y. linear l /\ !x. x IN r ==> g x = l x + y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (r:real^P->bool) /\ convex r` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT; POLYTOPE_IMP_CONVEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^M->real^N`;
                 `IMAGE (f:real^P->real^N) r`; `g:real^P->real^M`; `r:real^P->bool`]
    MOI_LCA_SHEET_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    MP_TAC(ISPECL [`f:real^P->real^N`; `l:real^P->real^N`; `y:real^N`; `r:real^P->bool`]
      MOI_LCA_AFFINE_RELINT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `x:real^P` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^P) IN r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^P` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `IMAGE (g:real^P->real^M) r = L` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q:real^M->real^N) w IN IMAGE (f:real^P->real^N) r` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (q:real^M->real^N) L = IMAGE (f:real^P->real^N) r` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^P` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^P` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^M->real^N`;
                   `L:real^M->bool`] MOI_LCA_SIMPLEX_INJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^M->real^N`;
                 `L:real^M->bool`] MOI_LCA_LIFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^M` (X_CHOOSE_THEN `y':real^M`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(l':real^N->real^M) o (l:real^P->real^N)`;
                        `(l':real^N->real^M) y + y'`] THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE; o_THM] THEN X_GEN_TAC `x:real^P` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(g:real^P->real^M) x IN L` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^P->real^M) x` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `y':real^M`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[LINEAR_ADD] THEN VECTOR_ARITH_TAC);;

let COVER_LIFT_CELLWISE = prove
 (MOI_LT_COVER_LIFT_CELLWISE,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LTD_CELLWISE_BASIC) THEN
  MP_TAC(ISPECL [`q:real^N->real^N`; `UNIONS c':real^N->bool`; `UNIONS c:real^N->bool`;
                 `f:real^2->real^N`; `std_triangle`] COVERING_SPACE_LIFT) THEN
  ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f2:real^2->real^N` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_lt_cellwise (f:real^2->real^N) c` THEN REWRITE_TAC[moi_lt_cellwise] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p:(real^2->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(r:real^2->bool) SUBSET std_triangle` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real^2->bool` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `polytope:(real^2->bool)->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r:real^2->bool = {}` THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `?t:real^N->bool. t IN c'` STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `(f2:real^2->real^N) (vec 0) IN UNIONS c'` MP_TAC THENL
         [MP_TAC MOI_LTD_STD_TRIANGLE_BASIC THEN ASM SET_TAC[];
          REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[]];
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[EMPTY_FACE_OF];
      REWRITE_TAC[] THEN MESON_TAC[LINEAR_ZERO]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LCA_CELL_LIFT THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `q:real^N->real^N`; `f:real^2->real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`l:real^2->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM SET_TAC[];
    ASM_MESON_TAC[SUBSET]]);;


(* ------------------------------------------------------------------------- *)
(* COVER_BOUNDARY.  For a nonempty simplex t of c', IMAGE q is               *)
(* a bijection from the simplices of c' of a given dimension containing t   *)
(* onto those of c containing q(t): injective by LIFT_UNIQUE (they meet in  *)
(* t), onto by POINT_LIFT at a point of the relative interior of t.  So t   *)
(* is a boundary triangle of c' iff q(t) is one of c.                        *)
(* ------------------------------------------------------------------------- *)

let MOI_LCA_STAR_IMAGE = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q t n.
     FINITE c' /\ lf_simplicial_complex c' /\ lf_simplicial_complex c /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c) /\
     t IN c' /\ ~(t = {})
     ==> IMAGE (IMAGE q) {r | r IN c' /\ aff_dim r = n /\ t SUBSET r} =
         {r | r IN c /\ aff_dim r = n /\ IMAGE q t SUBSET r}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `R:real^N->bool` THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:real^M->bool` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_map_on];
      ASM_MESON_TAC[MOI_LCA_AFF_DIM];
      ASM_SIMP_TAC[IMAGE_SUBSET]];
    STRIP_TAC THEN
    SUBGOAL_THEN `?z:real^M. z IN relative_interior t` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MOI_FM3_LF_CONVEX];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^M) IN t` ASSUME_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^M->real^N`;
                   `R:real^N->bool`; `z:real^M`] MOI_LCA_POINT_LIFT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real^M->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `L:real^M->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_LCA_AFF_DIM];
      MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`c':(real^M->bool)->bool`; `z:real^M`] THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_LCA_STAR_CARD = prove
 (`!(c':(real^M->bool)->bool) (c:(real^N->bool)->bool) q t n.
     FINITE c' /\ lf_simplicial_complex c' /\ lf_simplicial_complex c /\
     simplicial_map_on c' c q /\ covering_space (UNIONS c',q) (UNIONS c) /\
     t IN c' /\ ~(t = {})
     ==> CARD {r | r IN c /\ aff_dim r = n /\ IMAGE q t SUBSET r} =
         CARD {r | r IN c' /\ aff_dim r = n /\ t SUBSET r}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^M->real^N`;
                 `t:real^M->bool`; `n:int`] MOI_LCA_STAR_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`r1:real^M->bool`; `r2:real^M->bool`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_LCA_LIFT_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`c':(real^M->bool)->bool`; `c:(real^N->bool)->bool`;
                          `q:real^M->real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c':(real^M->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let COVER_BOUNDARY = prove
 (MOI_LT_COVER_BOUNDARY,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool) /\
                lf_simplicial_complex (c':(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t:real^N->bool. t IN c' /\ aff_dim t = &2
        ==> (CARD {r | r IN c /\ aff_dim r = &3 /\ IMAGE (q:real^N->real^N) t SUBSET r} = 1
             <=> CARD {r | r IN c' /\ aff_dim r = &3 /\ t SUBSET r} = 1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c':(real^N->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^N->real^N`;
                   `t:real^N->bool`; `&3:int`] MOI_LCA_STAR_CARD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[AFF_DIM_EMPTY; INT_ARITH `~(-- &1:int = &2)`];
      SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[complex_boundary; EXTENSION; IN_ELIM_THM; IN_UNIONS] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
     [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `IMAGE (q:real^N->real^N) t` THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_map_on];
      ASM_MESON_TAC[MOI_LCA_AFF_DIM];
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `CARD:((real^N->bool)->bool)->num`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[FUN_IN_IMAGE]];
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c':(real^N->bool)->bool`; `c:(real^N->bool)->bool`; `q:real^N->real^N`;
                   `t:real^N->bool`; `x:real^N`] MOI_LCA_POINT_LIFT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `aff_dim (L:real^N->bool) = &2` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_LCA_AFF_DIM]; ALL_TAC] THEN
    EXISTS_TAC `L:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `L:real^N->bool` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `CARD:((real^N->bool)->bool)->num`)) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* DESCENT_INPUT.  q is PL on the finite c' (piecewise affine               *)
(* on polytopes), so q o e2 is PL; local injectivity of q o e2 comes from    *)
(* that of q (MOI_LCA_LOCAL_INJ) and continuity and injectivity of e2; e2  *)
(* maps each fibre of q o e2 injectively into a 2-point fibre of q (and the *)
(* fibres off UNIONS c are empty).                                          *)
(* ------------------------------------------------------------------------- *)

let DESCENT_INPUT = prove
 (MOI_LT_DESCENT_INPUT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c':(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  UNDISCH_TAC `pl_homeomorphism (std_triangle,d2) (e2:real^2->real^N,e2')` THEN
  REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `IMAGE (e2:real^2->real^N) std_triangle SUBSET UNIONS c'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (q:real^N->real^N) (UNIONS c') = UNIONS c` ASSUME_TAC THENL
   [ASM_MESON_TAC[COVERING_SPACE_IMP_SURJECTIVE]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `UNIONS c':real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`q:real^N->real^N`; `c':(real^N->bool)->bool`]
      MOI_REAL_PIECEWISE_AFFINE_UNIONS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_FM3_LF_POLYTOPE]; ASM_MESON_TAC[simplicial_map_on]];
      SIMP_TAC[]];
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`q:real^N->real^N`; `UNIONS c':real^N->bool`; `UNIONS c:real^N->bool`;
                   `(e2:real^2->real^N) x`] MOI_LCA_LOCAL_INJ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj"))) THEN
    UNDISCH_TAC `(e2:real^2->real^N) continuous_on std_triangle` THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(x:real^2,dl)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    MAP_EVERY X_GEN_TAC [`y:real^2`; `z:real^2`] THEN
    REWRITE_TAC[IN_INTER; IN_BALL; o_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e2:real^2->real^N) y = e2 z` ASSUME_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        ASM SET_TAC[];
        ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
      ASM_MESON_TAC[]];
    X_GEN_TAC `w:real^N` THEN
    ASM_CASES_TAC `(w:real^N) IN UNIONS c` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
        can (find_term ((=) `(HAS_SIZE):(real^N->bool)->num->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `IMAGE (e2:real^2->real^N) {x | x IN std_triangle /\ ((q:real^N->real^N) o e2) x = w}
        SUBSET {x | x IN UNIONS c' /\ q x = w}`
      ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!x y. x IN {x | x IN std_triangle /\ ((q:real^N->real^N) o (e2:real^2->real^N)) x = w} /\
              y IN {x | x IN std_triangle /\ (q o e2) x = w} /\ e2 x = e2 y ==> x = y`
      ASSUME_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `FINITE {x | x IN std_triangle /\ ((q:real^N->real^N) o (e2:real^2->real^N)) x = w}`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL [`e2:real^2->real^N`;
          `{x | x IN std_triangle /\ ((q:real^N->real^N) o (e2:real^2->real^N)) x = w}`]
          FINITE_IMAGE_INJ_EQ) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{x | x IN UNIONS c' /\ (q:real^N->real^N) x = w}` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`e2:real^2->real^N`;
        `{x | x IN std_triangle /\ ((q:real^N->real^N) o (e2:real^2->real^N)) x = w}`]
        CARD_IMAGE_INJ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rand(concl th) = `2`)) THEN
      MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `{x | x IN std_triangle /\ ((q:real^N->real^N) o (e2:real^2->real^N)) x = w} = {}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; o_THM] THEN ASM SET_TAC[];
        REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES] THEN ARITH_TAC]]]);;


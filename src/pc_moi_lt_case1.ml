needs "src/pc_moi_loop_stmt3.ml";;
needs "src/pc_moi_lt_cuta1.ml";;
needs "src/pc_moi_s35_deg.ml";;
needs "src/pc_moi_fnd_m3a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_lt_case1: Case 1 of the C25 cut (Moise p.185).  Main theorem      *)
(*   CASE1_FROM_ORIENT : |- MOI_LT3_CASE1_FROM_ORIENT                        *)
(* (= MOI_LT_ORIENT_SIGN ==> MOI_LT2_CASE1_EXCLUDED, pc_moi_loop_stmt3.ml):  *)
(* with genuine crossings and c orientable, the preimage of a closed double  *)
(* component is not connected. Route: if it were one polygon J, the sign     *)
(* sigma(x) = eps(chart) t a(x) b(x) chi(sheet) (chart orientation sign      *)
(* relative to sg, direction of k, inner half-planes of the sheets through x *)
(* and through the other preimage) would be locally constant on J and chart  *)
(* independent, but sigma(tau x) = -sigma(x). General lemmas: regular        *)
(* points of PL embeddings, chart independence of the orientation sign       *)
(* (MOI_S35_LOCAL_SIGN), the configuration lemma; the orientation sign       *)
(* predicate moi_lc1_osign.                                                  *)
(* ========================================================================= *)

(* The orientation sign property of MOI_LT_ORIENT_SIGN, as a predicate:    *)
(* the PL map g on w has the sign s relative to sg at all its regular      *)
(* points (small balls mapped affinely into a 3-simplex of c).              *)

let moi_lc1_osign = new_definition
 `moi_lc1_osign (c:(real^N->bool)->bool) sg (g:real^3->real^N) w s <=>
    !a b d e (l:real^3->real^N) y z r.
       convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
       linear l /\ &0 < r /\ ball(z,r) SUBSET w /\
       (!x. x IN ball(z,r) ==> g x = l x + y /\ g x IN convex hull {a,b,d,e})
       ==> sg a b d e *
           real_sgn(det((lambda i j. l(basis j) dot
                           (if i = 1 then b - a else if i = 2 then d - a else e - a))
                        :real^3^3)) = s`;;

(* ------------------------------------------------------------------------- *)
(* G1. Regular points: an injective PL map of an open set of real^3 into a  *)
(* complex of dimension at most 3 is affine into a single 3-simplex on some *)
(* small ball inside any nonempty open subset (Baire for the finitely many  *)
(* closed pieces).                                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_LC1_REGULAR_POINT = prove
 (`!(c:(real^N->bool)->bool) (g:real^3->real^N) w v.
     FINITE c /\ lf_simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &3) /\
     open w /\ pl_map_on w g /\ (!x y. x IN w /\ y IN w /\ g x = g y ==> x = y) /\
     IMAGE g w SUBSET UNIONS c /\ open v /\ ~(v = {}) /\ v SUBSET w
     ==> ?a b d e (l:real^3->real^N) y z r.
            convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
            linear l /\ (!u. l u = vec 0 ==> u = vec 0) /\
            &0 < r /\ ball(z,r) SUBSET v /\
            (!x. x IN ball(z,r) ==> g x = l x + y /\ g x IN convex hull {a,b,d,e})`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `z0:real^3` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  UNDISCH_TAC `pl_map_on w (g:real^3->real^N)` THEN REWRITE_TAC[pl_map_on] THEN
  DISCH_THEN(MP_TAC o SPEC `z0:real^3`) THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:(real^3->bool)->bool` (X_CHOOSE_THEN `u0:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?rho. &0 < rho /\ cball(z0:real^3,rho) SUBSET v INTER u0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `v INTER u0:real^3->bool` OPEN_CONTAINS_CBALL) THEN
    ASM_SIMP_TAC[OPEN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `z0:real^3`) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  ABBREV_TAC
   `Q = {cball(z0:real^3,rho) INTER {x | x IN k /\ (g:real^3->real^N) x IN s} |
         k IN c0 /\ s IN c}` THEN
  SUBGOAL_THEN `FINITE (Q:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:real^3->bool. q IN Q ==> closed q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`k:real^3->bool`; `s:real^N->bool`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CLOSED_INTER THEN REWRITE_TAC[CLOSED_CBALL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^3->bool` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "polytope"))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `l:real^3->real^N` (X_CHOOSE_THEN `y:real^N`
        STRIP_ASSUME_TAC)))) THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `\x. (l:real^3->real^N) x + y` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST];
      ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS Q = cball(z0:real^3,rho)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN w INTER u0` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP (MATCH_MP (SET_RULE
      `!s t. s SUBSET t ==> (x:real^3) IN s ==> x IN t`)
      (ASSUME `w INTER u0 SUBSET UNIONS(c0:(real^3->bool)->bool)`)) th)) THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(g:real^3->real^N) x IN UNIONS c` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `?q:real^3->bool. q IN Q /\ ~(interior q = {})` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    MP_TAC(ISPEC `Q:(real^3->bool)->bool` NOWHERE_DENSE_COUNTABLE_UNIONS_CLOSED) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMP_COUNTABLE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[INTERIOR_CBALL; BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(q:real^3->bool) IN Q` THEN EXPAND_TAC "Q" THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `s:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^3->bool` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "polytope"))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l:real^3->real^N` (X_CHOOSE_THEN `y:real^N`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `?z r. &0 < r /\
          ball(z:real^3,r) SUBSET
          cball(z0,rho) INTER {x | x IN k /\ (g:real^3->real^N) x IN s}`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `z:real^3` o GEN_REWRITE_RULE I
      [GSYM MEMBER_NOT_EMPTY]) THEN
    MP_TAC(ISPEC `interior(cball(z0:real^3,rho) INTER
                   {x | x IN k /\ (g:real^3->real^N) x IN s})` OPEN_CONTAINS_BALL) THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`z:real^3`; `r:real`] THEN
    ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN ball(z,r) ==> (g:real^3->real^N) x = l x + y /\
                                               g x IN s`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN k /\ (g:real^3->real^N) x IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^3. (l:real^3->real^N) u = vec 0 ==> u = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `z + (r / (&2 * norm(u:real^3))) % u = z` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun t -> t = `w:real^3->bool`)) (concl th))) THEN
      SUBGOAL_THEN `z + (r / (&2 * norm(u:real^3))) % u IN ball(z,r)` ASSUME_TAC THENL
       [REWRITE_TAC[IN_BALL; NORM_ARITH `dist(z:real^3,z + x) = norm x`; NORM_MUL] THEN
        SUBGOAL_THEN `&0 < norm(u:real^3)` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_NORM;
                     REAL_ARITH `&0 < r ==> abs r = r`] THEN
        ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> r / (&2 * n) * n = r / &2`] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^3) IN ball(z,r)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID];
      REWRITE_TAC[VECTOR_ARITH `z + a % u = z <=> a % u = vec 0:real^3`] THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < norm(u:real^3)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = &3` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `aff_dim(IMAGE (\x. (l:real^3->real^N) x + y) (ball(z,r)))` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE (\x. (l:real^3->real^N) x + y) (ball(z,r)) =
                    IMAGE (\x. y + x) (IMAGE l (ball(z,r)))` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[AFF_DIM_TRANSLATION_EQ] THEN
      MP_TAC(ISPECL [`l:real^3->real^N`; `ball(z:real^3,r)`]
        AFF_DIM_INJECTIVE_LINEAR_IMAGE) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[LINEAR_INJECTIVE_0]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[AFF_DIM_BALL; DIMINDEX_3] THEN
      INT_ARITH_TAC;
      MATCH_MP_TAC AFF_DIM_SUBSET THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a b d e:real^N. s = convex hull {a,b,d,e}` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
    SUBGOAL_THEN `n:int = &3` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(V:real^N->bool) HAS_SIZE 4` MP_TAC THENL
     [REWRITE_TAC[HAS_SIZE] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
      UNDISCH_TAC `&(CARD(V:real^N->bool)):int = &3 + &1` THEN
      REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      (X_CHOOSE_THEN `d:real^N` (X_CHOOSE_THEN `e:real^N` STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `l:real^3->real^N`;
    `y:real^N`; `z:real^3`; `r:real`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `s:real^N->bool`)) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* G2. Chart independence of the orientation sign: if g2 o psi = g1 on a    *)
(* connected open set, psi has the determinant sign s1 * s2 at all its      *)
(* locally affine points (common regular point, Gram matrix of a            *)
(* composition, MOI_S35_LOCAL_SIGN).                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_LC1_GRAM_COMPOSE = prove
 (`!(l:real^3->real^N) (m:real^3->real^3) (u:num->real^N).
     linear l /\ linear m
     ==> ((lambda i j. (l(m(basis j))) dot u i):real^3^3) =
         ((lambda i j. l(basis j) dot u i):real^3^3) ** matrix m`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; matrix_mul; matrix] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(m:real^3->real^3)(basis j) =
                vsum(1..dimindex(:3)) (\k. m(basis j)$k % basis k)`
  SUBST1_TAC THENL [REWRITE_TAC[BASIS_EXPANSION]; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; DOT_LSUM] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  BETA_TAC THEN
  ASM_SIMP_TAC[LINEAR_CMUL; DOT_LMUL; LAMBDA_BETA] THEN
  REWRITE_TAC[BASIS_EXPANSION] THEN REWRITE_TAC[REAL_MUL_SYM]);;

let MOI_LC1_TRANSITION_SIGN = prove
 (`!(c:(real^N->bool)->bool) sg (g1:real^3->real^N) (g2:real^3->real^N) w1 w2 s1 s2
    (psi:real^3->real^3) w.
     FINITE c /\ lf_simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &3) /\
     (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
                ==> (sg a b d e = &1 \/ sg a b d e = -- &1)) /\
     open w1 /\ pl_map_on w1 g1 /\ (!x y. x IN w1 /\ y IN w1 /\ g1 x = g1 y ==> x = y) /\
     IMAGE g1 w1 SUBSET UNIONS c /\ moi_lc1_osign c sg g1 w1 s1 /\
     open w2 /\ pl_map_on w2 g2 /\ (!x y. x IN w2 /\ y IN w2 /\ g2 x = g2 y ==> x = y) /\
     IMAGE g2 w2 SUBSET UNIONS c /\ moi_lc1_osign c sg g2 w2 s2 /\
     (s2 = &1 \/ s2 = -- &1) /\
     open w /\ connected w /\ ~(w = {}) /\ w SUBSET w1 /\
     psi continuous_on w /\ IMAGE psi w SUBSET w2 /\ (!x. x IN w ==> g2(psi x) = g1 x)
     ==> !x m. x IN w /\ moi_s35_lin_at psi x m ==> real_sgn(det(matrix m)) = s1 * s2`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `!x y. x IN w /\ y IN w /\ (psi:real^3->real^3) x = psi y ==> x = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `w1:real^3->bool`)) (concl th))) THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g1:real^3->real^N`; `w1:real^3->bool`;
                 `w:real^3->bool`] MOI_LC1_REGULAR_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `d:real^N` (X_CHOOSE_THEN `e:real^N`
    (X_CHOOSE_THEN `l1:real^3->real^N` (X_CHOOSE_THEN `y1:real^N`
    (X_CHOOSE_THEN `z1:real^3` (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN `open(IMAGE (psi:real^3->real^3) (ball(z1,r1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[OPEN_BALL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g2:real^3->real^N`; `w2:real^3->bool`;
                 `IMAGE (psi:real^3->real^3) (ball(z1,r1))`] MOI_LC1_REGULAR_POINT) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; BALL_EQ_EMPTY] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a':real^N` (X_CHOOSE_THEN `b':real^N`
    (X_CHOOSE_THEN `d':real^N` (X_CHOOSE_THEN `e':real^N`
    (X_CHOOSE_THEN `l2:real^3->real^N` (X_CHOOSE_THEN `y2:real^N`
    (X_CHOOSE_THEN `z2:real^3` (X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN `?x2:real^3. x2 IN ball(z1,r1) /\ (psi:real^3->real^3) x2 = z2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(z2:real^3) IN IMAGE (psi:real^3->real^3) (ball(z1,r1))` MP_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!x:real^3 s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `ball(z2:real^3,r2)` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r3. &0 < r3 /\ ball(x2:real^3,r3) SUBSET ball(z1,r1) /\
                     IMAGE (psi:real^3->real^3) (ball(x2,r3)) SUBSET ball(z2,r2)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`psi:real^3->real^3`; `ball(z1:real^3,r1)`; `ball(z2:real^3,r2)`]
      CONTINUOUS_OPEN_PREIMAGE) THEN
    REWRITE_TAC[OPEN_BALL] THEN ANTS_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `x2:real^3`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r3:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN ball(x2,r3)
                           ==> (l2:real^3->real^N)((psi:real^3->real^3) x) + y2 =
                               l1 x + y1 /\
                               l1 x + y1 IN convex hull {a',b',d',e'}`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN ball(z1,r1) /\ (psi:real^3->real^3) x IN ball(z2,r2)`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(g1:real^3->real^N) x = l1 x + y1 /\ g2((psi:real^3->real^3) x) =
                  l2(psi x) + y2 /\ g2(psi x) IN convex hull {a',b',d',e'} /\
                  g2(psi x) = g1 x`
    MP_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a',b',d',e'} = convex hull {a:real^N,b,d,e}`
  ASSUME_TAC THENL
   [ABBREV_TAC `s1':real^N->bool = convex hull {a,b,d,e}` THEN
    ABBREV_TAC `s2':real^N->bool = convex hull {a',b',d',e'}` THEN
    SUBGOAL_THEN `(s1':real^N->bool) IN c /\ s2' IN c /\
                  aff_dim(s1':real^N->bool) = &3 /\ aff_dim(s2':real^N->bool) = &3 /\
                  convex(s1':real^N->bool) /\ convex(s2':real^N->bool)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["s1'"; "s2'"] THEN
      ASM_REWRITE_TAC[CONVEX_CONVEX_HULL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s1' INTER s2') face_of (s1':real^N->bool) /\
                  (s1' INTER s2') face_of (s2':real^N->bool)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPECL [`s1':real^N->bool`; `s2':real^N->bool`] o
        CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (\x. (l1:real^3->real^N) x + y1) (ball(x2,r3)) SUBSET s1' INTER s2'`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN ball(z1,r1)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> t = `g1:real^3->real^N`)) (concl th) &&
          can (find_term (fun t -> t = `l1:real^3->real^N`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "s1'" THEN MESON_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> t = `psi:real^3->real^3`)) (concl th) &&
          can (find_term (fun t -> t = `y2:real^N`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "s2'" THEN MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim((s1':real^N->bool) INTER s2') = &3` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim(s1':real^N->bool)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC AFF_DIM_SUBSET THEN SET_TAC[];
          ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC `aff_dim(IMAGE (\x. (l1:real^3->real^N) x + y1) (ball(x2,r3)))` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `IMAGE (\x. (l1:real^3->real^N) x + y1) (ball(x2,r3)) =
                      IMAGE (\x. y1 + x) (IMAGE l1 (ball(x2,r3)))` SUBST1_TAC THENL
         [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[AFF_DIM_TRANSLATION_EQ] THEN
        MP_TAC(ISPECL [`l1:real^3->real^N`; `ball(x2:real^3,r3)`]
          AFF_DIM_INJECTIVE_LINEAR_IMAGE) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[LINEAR_INJECTIVE_0]; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[AFF_DIM_BALL; DIMINDEX_3] THEN
        INT_ARITH_TAC;
        MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s1':real^N->bool) INTER s2' = s1' /\ s1' INTER s2' = s2'`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THENL
       [MP_TAC(ISPECL [`(s1':real^N->bool) INTER s2'`; `s1':real^N->bool`]
          FACE_OF_AFF_DIM_LT);
        MP_TAC(ISPECL [`(s1':real^N->bool) INTER s2'`; `s2':real^N->bool`]
          FACE_OF_AFF_DIM_LT)] THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. ?v':real^3. (l1:real^3->real^N) v = l2 v'` ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN
    ASM_CASES_TAC `v:real^3 = vec 0` THENL
     [EXISTS_TAC `vec 0:real^3` THEN ASM_MESON_TAC[LINEAR_0]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(v:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `?t. &0 < t /\ x2 + t % v IN ball(x2:real^3,r3)` STRIP_ASSUME_TAC
    THENL
     [EXISTS_TAC `r3 / (&2 * norm(v:real^3))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x:real^3,x + y) = norm y`; NORM_MUL] THEN
        ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_NORM;
                     REAL_ARITH `&0 < r ==> abs r = r`] THEN
        ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> r / (&2 * n) * n = r / &2`] THEN
        UNDISCH_TAC `&0 < r3` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `inv t % ((psi:real^3->real^3)(x2 + t % v) - psi x2)` THEN
    SUBGOAL_THEN `(l2:real^3->real^N)((psi:real^3->real^3)(x2 + t % v)) + y2 =
                  l1(x2 + t % v) + y1 /\ l2(psi x2) + y2 = l1 x2 + y1`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    SIMP_TAC[ASSUME `linear(l2:real^3->real^N)`; LINEAR_CMUL; LINEAR_SUB] THEN
    SUBGOAL_THEN `(l2:real^3->real^N)((psi:real^3->real^3)(x2 + t % v)) -
                  l2(psi x2) = t % l1 v` SUBST1_TAC THENL
     [SUBGOAL_THEN `(l1:real^3->real^N)(x2 + t % v) = l1 x2 + t % l1 v`
      ASSUME_TAC THENL [ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL]; ALL_TAC] THEN
      UNDISCH_TAC `(l2:real^3->real^N)((psi:real^3->real^3)(x2 + t % v)) + y2 =
                   l1(x2 + t % v) + y1` THEN
      UNDISCH_TAC `(l2:real^3->real^N)((psi:real^3->real^3) x2) + y2 = l1 x2 + y1` THEN
      REWRITE_TAC[ASSUME `(l1:real^3->real^N)(x2 + t % v) = l1 x2 + t % l1 v`] THEN
      CONV_TAC VECTOR_ARITH;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPEC `l2:real^3->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LINEAR_INJECTIVE_0]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2':real^N->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `M = (l2':real^N->real^3) o (l1:real^3->real^N)` THEN
  SUBGOAL_THEN `linear (M:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN ASM_SIMP_TAC[LINEAR_COMPOSE]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. (l2:real^3->real^N)((M:real^3->real^3) v) = l1 v`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN EXPAND_TAC "M" THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `v':real^3` SUBST1_TAC o SPEC `v:real^3`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s35_lin_at (psi:real^3->real^3) x2 M` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_lin_at] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `r3:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x2:real^3) IN ball(x2,r3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN ball(x2,r3)`)) THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x2:real^3) IN ball(x2,r3)`)) THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN
     `(l2:real^3->real^N)((psi:real^3->real^3) x - (psi x2 + M(x - x2))) = vec 0`
    MP_TAC THENL
     [SIMP_TAC[ASSUME `linear(l2:real^3->real^N)`; LINEAR_SUB; LINEAR_ADD] THEN
      REWRITE_TAC[ASSUME `!v:real^3. (l2:real^3->real^N)((M:real^3->real^3) v) = l1 v`] THEN
      SIMP_TAC[ASSUME `linear(l1:real^3->real^N)`; LINEAR_SUB] THEN
      UNDISCH_TAC `(l2:real^3->real^N)((psi:real^3->real^3) x) + y2 = l1 x + y1` THEN
      UNDISCH_TAC `(l2:real^3->real^N)((psi:real^3->real^3) x2) + y2 = l1 x2 + y1` THEN
      CONV_TAC VECTOR_ARITH;
      DISCH_THEN(MP_TAC o MATCH_MP (ASSUME
        `!u:real^3. (l2:real^3->real^N) u = vec 0 ==> u = vec 0`)) THEN
      REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_sgn(det(matrix(M:real^3->real^3))) = s1 * s2` ASSUME_TAC THENL
   [ABBREV_TAC `sgv:real = sg (a:real^N) (b:real^N) (d:real^N) (e:real^N)` THEN
    ABBREV_TAC
     `G1 = real_sgn(det((lambda i j. (l1:real^3->real^N)(basis j) dot
             (if i = 1 then (b:real^N) - a else if i = 2 then d - a else e - a))
             :real^3^3))` THEN
    ABBREV_TAC
     `G2 = real_sgn(det((lambda i j. (l2:real^3->real^N)(basis j) dot
             (if i = 1 then (b:real^N) - a else if i = 2 then d - a else e - a))
             :real^3^3))` THEN
    SUBGOAL_THEN `sgv * G1 = s1` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["sgv"; "G1"] THEN
      UNDISCH_TAC `moi_lc1_osign c sg (g1:real^3->real^N) w1 s1` THEN
      REWRITE_TAC[moi_lc1_osign] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`y1:real^N`; `z1:real^3`; `r1:real`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `w:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `sgv * G2 = s2` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["sgv"; "G2"] THEN
      UNDISCH_TAC `moi_lc1_osign c sg (g2:real^3->real^N) w2 s2` THEN
      REWRITE_TAC[moi_lc1_osign] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`y2:real^N`; `z2:real^3`; `r2:real`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (psi:real^3->real^3) (ball(z1,r1))` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (psi:real^3->real^3) w` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN ball(z2,r2)`)) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `sgv * sgv = &1 /\ s2 * s2 = &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `sgv = &1 \/ sgv = -- &1` MP_TAC THENL
         [EXPAND_TAC "sgv" THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
        UNDISCH_TAC `s2 = &1 \/ s2 = -- &1` THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l2:real^3->real^N`; `M:real^3->real^3`;
       `\i. if i = 1 then (b:real^N) - a else if i = 2 then d - a else e - a`]
      MOI_LC1_GRAM_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `\A:real^3^3. real_sgn(det A)`) THEN
    BETA_TAC THEN REWRITE_TAC[DET_MUL; REAL_SGN_MUL] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `sgv * G1 = s1` THEN UNDISCH_TAC `sgv * G2 = s2` THEN
    UNDISCH_TAC `sgv * sgv = &1` THEN UNDISCH_TAC `s2 * s2 = &1` THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `G1:real`)) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `m:real^3->real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `w:real^3->bool`; `x:real^3`; `x2:real^3`;
                 `m:real^3->real^3`; `M:real^3->real^3`] LOCAL_SIGN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `s1 * s2:real`)) THEN
  REWRITE_TAC[REAL_MUL_POS_LT] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[real_sgn] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* G3. Triangulations adapted to a PL map and finitely many polytopes; a    *)
(* simplex containing a relative interior point of another contains it.    *)
(* ------------------------------------------------------------------------- *)

let MOI_LC1_ADAPTED_TRIANGULATION = prove
 (`!(psi:real^M->real^N) w K d.
     pl_map_on w psi /\ polytope K /\ K SUBSET w /\ FINITE d /\
     (!k. k IN d ==> polytope k /\ k SUBSET K)
     ==> ?t. simplicial_complex t /\ UNIONS t = K /\
             (!s. s IN t ==> ?l y. linear l /\ !z. z IN s ==> psi z = l z + y) /\
             (!k. k IN d ==> ?f. f SUBSET t /\ k = UNIONS f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{K:real^M->bool}` POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ASM_REWRITE_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t0:(real^M->bool)->bool`; `psi:real^M->real^N`]
    SIMPLICIAL_SUBDIVISION_PL_MAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `w:real^M->bool` THEN ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(real^M->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "aff"))))) THEN
  MP_TAC(ISPECL [`t1:(real^M->bool)->bool`; `d:(real^M->bool)->bool`]
    SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^M->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sub")
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  EXISTS_TAC `t:(real^M->bool)->bool` THEN
  SUBGOAL_THEN `!s:real^M->bool. s IN t
                  ==> ?l y. linear l /\ !z. z IN s ==> (psi:real^M->real^N) z = l z + y`
  (fun th -> ASM_REWRITE_TAC[th] THEN ASM_MESON_TAC[]) THEN
  X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
  REMOVE_THEN "sub" (MP_TAC o SPEC `s:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^M->bool` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "aff" (MP_TAC o SPEC `s':real^M->bool`) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]);;

let MOI_LC1_COFACE = prove
 (`!(t:(real^N->bool)->bool) s s' x.
     simplicial_complex t /\ s IN t /\ s' IN t /\
     x IN relative_interior s /\ x IN s'
     ==> s SUBSET s'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s INTER s') face_of (s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  ASM_CASES_TAC `(s:real^N->bool) INTER s' = s` THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `(s:real^N->bool) INTER s'`]
    FACE_OF_SUBSET_RELATIVE_FRONTIER) THEN
  ASM_REWRITE_TAC[relative_frontier] THEN
  SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* G4. A tetrahedron of an adapted triangulation of a box around an axis    *)
(* point p, inside the closed quadrant {z1 >= 0, z2 >= 0}, containing an   *)
(* axis edge above p, a point of the half-plane {z2 = 0, z1 > 0} over an   *)
(* axis point, and a point of the open quadrant side over a point of the   *)
(* plane z2 = 0 (the frame of the configuration lemma).                     *)
(* ------------------------------------------------------------------------- *)

let MOI_LC1_SING_IN = prove
 (`!(t:(real^N->bool)->bool) p.
     (?f. f SUBSET t /\ {p} = UNIONS f) ==> {p} IN t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^N) IN UNIONS f` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_SING]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s = {p:real^N}` (fun th -> REWRITE_TAC[SYM th] THEN
    ASM_MESON_TAC[SUBSET]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS f:real^N->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; IN_UNIONS]; ASM_MESON_TAC[SUBSET_REFL]];
    ASM_REWRITE_TAC[SING_SUBSET]]);;

let MOI_LC1_PIECE_AT = prove
 (`!(t:(real^N->bool)->bool) R f x z r.
     simplicial_complex t /\ f SUBSET t /\ R = UNIONS f /\ z IN R /\ &0 < r /\
     (!s y. s IN t /\ y IN s /\ dist(x,y) < r ==> x IN s) /\ dist(x,z) < r
     ==> ?s. s IN t /\ s SUBSET R /\ x IN s /\ z IN s`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(z:real^N) IN R` THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN
  SUBGOAL_THEN `(s:real^N->bool) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s:real^N->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[]]);;

let MOI_LC1_AXIS_COLLINEAR = prove
 (`!s:real^3->bool. s SUBSET {z | z$1 = &0 /\ z$2 = &0} ==> collinear s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[collinear] THEN
  EXISTS_TAC `basis 3:real^3` THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
  EXISTS_TAC `(x:real^3)$3 - (y:real^3)$3` THEN
  SUBGOAL_THEN `(x:real^3)$1 = &0 /\ x$2 = &0 /\ (y:real^3)$1 = &0 /\ y$2 = &0`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_SUB_COMPONENT;
           VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_LC1_CORNER = prove
 (`!(t:(real^3->bool)->bool) a b p.
     simplicial_complex t /\ UNIONS t = interval[a,b] /\
     p IN interval(a,b) /\ p$1 = &0 /\ p$2 = &0 /\
     (?f. f SUBSET t /\ {p} = UNIONS f) /\
     (?f. f SUBSET t /\
          interval[a,b] INTER {z:real^3 | z$1 = &0 /\ z$2 = &0} = UNIONS f) /\
     (?f. f SUBSET t /\
          interval[a,b] INTER {z:real^3 | z$2 = &0 /\ &0 <= z$1} = UNIONS f) /\
     (?f. f SUBSET t /\
          interval[a,b] INTER {z:real^3 | &0 <= z$1 /\ &0 <= z$2} = UNIONS f)
     ==> ?s p1 m b0 g c0.
           s IN t /\ s SUBSET {z:real^3 | &0 <= z$1 /\ &0 <= z$2} /\
           p IN s /\ p1 IN s /\ m IN s /\ b0 IN s /\ g IN s /\ c0 IN s /\
           p1$1 = &0 /\ p1$2 = &0 /\ p$3 < p1$3 /\
           m$1 = &0 /\ m$2 = &0 /\ b0$2 = &0 /\ &0 < b0$1 /\ b0$3 = m$3 /\
           g$2 = &0 /\ c0$1 = g$1 /\ c0$3 = g$3 /\ &0 < c0$2 /\
           ~(interior s = {})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `fA:(real^3->bool)->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `fH:(real^3->bool)->bool` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `fQ:(real^3->bool)->bool` STRIP_ASSUME_TAC))))))))) THEN
  SUBGOAL_THEN `{p:real^3} IN t` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LC1_SING_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (t:(real^3->bool)->bool) /\ (!s. s IN t ==> closed s) /\
                (!s. s IN t ==> convex s)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3)$1 < &0 /\ &0 < (b:real^3)$1 /\ a$2 < &0 /\ &0 < b$2 /\
                a$3 < (p:real^3)$3 /\ p$3 < b$3`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN interval(a,b)` THEN
    SIMP_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN interval[a,b] <=>
                           a$1 <= z$1 /\ z$1 <= b$1 /\ a$2 <= z$2 /\ z$2 <= b$2 /\
                           a$3 <= z$3 /\ z$3 <= b$3`
  ASSUME_TAC THENL
   [SIMP_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* the axis edge above p *)
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `p:real^3`] MOI_LCC_NEAR_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n0"))) THEN
  ABBREV_TAC `s0 = min (r0 / &2) (((b:real^3)$3 - (p:real^3)$3) / &2)` THEN
  SUBGOAL_THEN `&0 < s0 /\ s0 < r0 /\ (p:real^3)$3 + s0 <= (b:real^3)$3`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "s0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`;
                 `interval[a,b] INTER {z:real^3 | z$1 = &0 /\ z$2 = &0}`;
                 `fA:(real^3->bool)->bool`; `p:real^3`;
                 `p + s0 % basis 3:real^3`; `r0:real`] MOI_LC1_PIECE_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[NORM_ARITH `dist(p:real^3,p + x) = norm x`; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sE:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?p1:real^3. ~(p1 = p) /\ sE = segment[p,p1]` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (sE:real^3->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    MP_TAC(ISPECL [`sE:real^3->bool`; `n:int`] MOI_LCC_SIMPLEX_LE1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM COLLINEAR_AFF_DIM] THEN
      MATCH_MP_TAC MOI_LC1_AXIS_COLLINEAR THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(p + s0 % basis 3 = p:real^3)` ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `p + x = p:real^3 <=> x = vec 0`; VECTOR_MUL_EQ_0] THEN
      SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `p:real^3`; `a':real^3`; `b':real^3`]
      MOI_LCC_VERTEX_OF_EDGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THENL
     [EXISTS_TAC `b':real^3` THEN ASM_MESON_TAC[];
      EXISTS_TAC `a':real^3` THEN ASM_MESON_TAC[SEGMENT_SYM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sE:real^3->bool) SUBSET interval[a,b] /\
                (!z:real^3. z IN sE ==> z$1 = &0 /\ z$2 = &0)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(p1:real^3)$1 = &0 /\ p1$2 = &0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3)$3 < (p1:real^3)$3` ASSUME_TAC THENL
   [UNDISCH_TAC `p + s0 % basis 3 IN (sE:real^3->bool)` THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\z:real^3. z$3`) THEN BETA_TAC THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_3; ARITH] THEN
    DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `~(y <= x) ==> x < y`) THEN DISCH_TAC THEN
    MP_TAC(SPECL [`u:real`; `(p:real^3)$3 - (p1:real^3)$3`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < s0` THEN UNDISCH_TAC
     `(p:real^3)$3 + s0 * &1 = (&1 - u) * p$3 + u * (p1:real^3)$3` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m:real^3 = midpoint(p,p1)` THEN
  SUBGOAL_THEN `(m:real^3) IN relative_interior sE /\ m IN sE /\
                m$1 = &0 /\ m$2 = &0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(p:real^3 = p1)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "m" THEN
    REWRITE_TAC[ASSUME `sE = segment[p:real^3,p1]`; RELATIVE_INTERIOR_SEGMENT;
                ASSUME `~(p:real^3 = p1)`; MIDPOINT_IN_SEGMENT] THEN
    REWRITE_TAC[midpoint; VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT] THEN
    REWRITE_TAC[ASSUME `(p:real^3)$1 = &0`; ASSUME `(p:real^3)$2 = &0`;
                ASSUME `(p1:real^3)$1 = &0`; ASSUME `(p1:real^3)$2 = &0`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `m:real^3`] MOI_LCC_NEAR_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))) THEN
  ABBREV_TAC `s1 = min (r1 / &2) ((b:real^3)$1 / &2)` THEN
  SUBGOAL_THEN `&0 < s1 /\ s1 < r1 /\ s1 <= (b:real^3)$1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^3) IN interval[a,b]` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`;
                 `interval[a,b] INTER {z:real^3 | z$2 = &0 /\ &0 <= z$1}`;
                 `fH:(real^3->bool)->bool`; `m:real^3`;
                 `m + s1 % basis 1:real^3`; `r1:real`] MOI_LC1_PIECE_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[NORM_ARITH `dist(p:real^3,p + x) = norm x`; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
    UNDISCH_TAC `(m:real^3) IN interval[a,b]` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sF:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(sE:real^3->bool) SUBSET sF` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LC1_COFACE THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `m:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?g:real^3. g IN relative_interior sF` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `convex(sF:real^3->bool)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `m:real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3) IN sF` ASSUME_TAC THENL
   [MP_TAC(ISPEC `sF:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(g:real^3) IN relative_interior sF` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3) IN interval[a,b] /\ g$2 = &0 /\ &0 <= g$1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^3) IN sF` THEN
    UNDISCH_TAC `(sF:real^3->bool) SUBSET
                 interval[a,b] INTER {z:real^3 | z$2 = &0 /\ &0 <= z$1}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `g:real^3`] MOI_LCC_NEAR_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n2"))) THEN
  ABBREV_TAC `s2 = min (r2 / &2) ((b:real^3)$2 / &2)` THEN
  SUBGOAL_THEN `&0 < s2 /\ s2 < r2 /\ s2 <= (b:real^3)$2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`;
                 `interval[a,b] INTER {z:real^3 | &0 <= z$1 /\ &0 <= z$2}`;
                 `fQ:(real^3->bool)->bool`; `g:real^3`;
                 `g + s2 % basis 2:real^3`; `r2:real`] MOI_LC1_PIECE_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[NORM_ARITH `dist(p:real^3,p + x) = norm x`; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
    UNDISCH_TAC `(g:real^3) IN interval[a,b]` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(sF:real^3->bool) SUBSET tau` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LC1_COFACE THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `g:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN tau /\ (p1:real^3) IN tau /\ (m:real^3) IN tau /\
                (m + s1 % basis 1:real^3) IN tau /\ (g:real^3) IN tau /\
                tau SUBSET {z:real^3 | &0 <= z$1 /\ &0 <= z$2}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(p:real^3) IN sE /\ (p1:real^3) IN sE` MP_TAC THENL
     [REWRITE_TAC[ASSUME `sE = segment[p:real^3,p1]`; ENDS_IN_SEGMENT]; ALL_TAC] THEN
    UNDISCH_TAC `(m:real^3) IN sE` THEN
    UNDISCH_TAC `(m + s1 % basis 1:real^3) IN sF` THEN
    UNDISCH_TAC `(g:real^3) IN sF` THEN
    UNDISCH_TAC `(sE:real^3->bool) SUBSET sF` THEN
    UNDISCH_TAC `(sF:real^3->bool) SUBSET tau` THEN
    UNDISCH_TAC `(tau:real^3->bool) SUBSET
                 interval[a,b] INTER {z:real^3 | &0 <= z$1 /\ &0 <= z$2}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(interior(tau:real^3->bool) = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPEC `tau:real^3->bool` EMPTY_INTERIOR_SUBSET_HYPERPLANE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `cc:real`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(u:real^3) dot p = cc /\ u dot p1 = cc /\ u dot m = cc /\
                  u dot (m + s1 % basis 1) = cc /\ u dot g = cc /\
                  u dot (g + s2 % basis 2) = cc`
    MP_TAC THENL
     [UNDISCH_TAC `(p:real^3) IN tau` THEN UNDISCH_TAC `(p1:real^3) IN tau` THEN
      UNDISCH_TAC `(m:real^3) IN tau` THEN
      UNDISCH_TAC `(m + s1 % basis 1:real^3) IN tau` THEN
      UNDISCH_TAC `(g:real^3) IN tau` THEN
      UNDISCH_TAC `(g + s2 % basis 2:real^3) IN tau` THEN
      UNDISCH_TAC `(tau:real^3->bool) SUBSET {x:real^3 | u dot x = cc}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SIMP_TAC[DOT_RADD; DOT_RMUL; DOT_BASIS; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[DOT_3] THEN
    REWRITE_TAC[ASSUME `(p:real^3)$1 = &0`; ASSUME `(p:real^3)$2 = &0`;
                ASSUME `(p1:real^3)$1 = &0`; ASSUME `(p1:real^3)$2 = &0`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `s1 * (u:real^3)$1 = &0 /\ s2 * u$2 = &0 /\
                  u$3 * ((p1:real^3)$3 - (p:real^3)$3) = &0`
    MP_TAC THENL
     [POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN
    SUBGOAL_THEN `~(s1 = &0) /\ ~(s2 = &0) /\ ~((p1:real^3)$3 - (p:real^3)$3 = &0)`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN UNDISCH_TAC `~(u:real^3 = vec 0)` THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`tau:real^3->bool`; `p1:real^3`; `m:real^3`; `m + s1 % basis 1:real^3`;
    `g:real^3`; `g + s2 % basis 2:real^3`] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
           DIMINDEX_3; ARITH] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID; REAL_ADD_LID]);;

(* ------------------------------------------------------------------------- *)
(* G5. The configuration lemma: an injective continuous map of a connected  *)
(* open set of real^3, PL near an axis point p, preserving the planes       *)
(* z1 = 0 and z2 = 0 near p, the half-planes z2 = 0 < z1 and z1 = 0 < z2   *)
(* and the axis direction above p, has positive determinant at all its      *)
(* locally affine points (a tetrahedron of MOI_LC1_CORNER, the triangular   *)
(* determinant of its linear part, MOI_S35_LOCAL_SIGN).                     *)
(* ------------------------------------------------------------------------- *)

let MOI_LC1_SIDE_POS = prove
 (`!(psi:real^3->real^3) s i z0.
     connected s /\ psi continuous_on s /\ 1 <= i /\ i <= 3 /\
     z0 IN s /\ &0 < (psi z0)$i /\ (!z. z IN s ==> ~((psi z)$i = &0))
     ==> !z. z IN s ==> &0 < (psi z)$i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (psi:real^3->real^3) s`; `(psi:real^3->real^3) z`;
                 `(psi:real^3->real^3) z0`; `basis i:real^3`; `&0`]
    CONNECTED_IVT_HYPERPLANE) THEN
  ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3; FUN_IN_IMAGE; CONNECTED_CONTINUOUS_IMAGE;
               REAL_LT_IMP_LE] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[]);;

let MOI_LC1_DET_POS = prove
 (`!l:real^3->real^3.
     (l(basis 3))$1 = &0 /\ (l(basis 3))$2 = &0 /\ &0 < (l(basis 3))$3 /\
     (l(basis 1))$2 = &0 /\ &0 < (l(basis 1))$1 /\ &0 < (l(basis 2))$2
     ==> &0 < det(matrix l)`,
  GEN_TAC THEN SIMP_TAC[DET_3; matrix; LAMBDA_BETA; DIMINDEX_3; ARITH] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  SUBGOAL_THEN `&0 < (l:real^3->real^3)(basis 1)$1 * l(basis 2)$2 * l(basis 3)$3`
  MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; REAL_ARITH_TAC]);;

let MOI_LC1_PLANE_POLYHEDRA = prove
 (`!i. 1 <= i /\ i <= 3
       ==> polyhedron {z:real^3 | z$i = &0} /\ polyhedron {z:real^3 | &0 <= z$i}`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`basis i:real^3`; `&0`] POLYHEDRON_HYPERPLANE);
    MP_TAC(ISPECL [`basis i:real^3`; `&0`] POLYHEDRON_HALFSPACE_GE)] THEN
  ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3; real_ge]);;

let MOI_LC1_CONFIG_SIGN = prove
 (`!(psi:real^3->real^3) w p r.
     open w /\ connected w /\ psi continuous_on w /\
     (!x y. x IN w /\ y IN w /\ psi x = psi y ==> x = y) /\
     &0 < r /\ ball(p,r) SUBSET w /\ pl_map_on (ball(p,r)) psi /\
     p$1 = &0 /\ p$2 = &0 /\
     (!z. z IN ball(p,r) ==> ((psi z)$1 = &0 <=> z$1 = &0) /\
                             ((psi z)$2 = &0 <=> z$2 = &0)) /\
     (!z. z IN ball(p,r) /\ z$2 = &0 /\ &0 < z$1 ==> &0 < (psi z)$1) /\
     (!z. z IN ball(p,r) /\ z$1 = &0 /\ &0 < z$2 ==> &0 < (psi z)$2) /\
     (!z. z IN ball(p,r) /\ z$1 = &0 /\ z$2 = &0 /\ p$3 < z$3
          ==> (psi p)$3 < (psi z)$3)
     ==> (?x0 m0. x0 IN ball(p,r) /\ moi_s35_lin_at psi x0 m0) /\
         !x m. x IN w /\ moi_s35_lin_at psi x m ==> &0 < det(matrix m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = r / &4` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `a:real^3 = p - d % vec 1` THEN
  ABBREV_TAC `b:real^3 = p + d % vec 1` THEN
  SUBGOAL_THEN `!z:real^3. z IN interval[a,b] <=>
                           (p:real^3)$1 - d <= z$1 /\ z$1 <= p$1 + d /\
                           p$2 - d <= z$2 /\ z$2 <= p$2 + d /\
                           p$3 - d <= z$3 /\ z$3 <= p$3 + d`
  (LABEL_TAC "box") THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    SIMP_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_SUB_COMPONENT;
             VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[a:real^3,b] SUBSET ball(p,r)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; dist] THEN X_GEN_TAC `z:real^3` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `p - z:real^3` NORM_LE_L1) THEN
    REWRITE_TAC[DIMINDEX_3; SUM_3; VECTOR_SUB_COMPONENT] THEN
    EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN interval(a,b) /\ p IN interval[a,b] /\
                (p + (d / &2) % basis 2:real^3) IN interval[a,b]`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    SIMP_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_SUB_COMPONENT;
             VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "box" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `polytope(interval[a:real^3,b] INTER {z:real^3 | z$1 = &0 /\ z$2 = &0}) /\
    polytope(interval[a:real^3,b] INTER {z:real^3 | z$2 = &0 /\ &0 <= z$1}) /\
    polytope(interval[a:real^3,b] INTER {z:real^3 | &0 <= z$1 /\ &0 <= z$2})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `{z:real^3 | P z /\ Q z} = {z | P z} INTER {z | Q z}`] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
    REWRITE_TAC[POLYTOPE_INTERVAL] THEN MATCH_MP_TAC POLYHEDRON_INTER THEN
    SIMP_TAC[MOI_LC1_PLANE_POLYHEDRA; ARITH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `ball(p:real^3,r)`; `interval[a:real^3,b]`;
                 `{{p:real^3},
                   interval[a:real^3,b] INTER {z:real^3 | z$1 = &0 /\ z$2 = &0},
                   interval[a:real^3,b] INTER {z:real^3 | z$2 = &0 /\ &0 <= z$1},
                   interval[a:real^3,b] INTER {z:real^3 | &0 <= z$1 /\ &0 <= z$2}}`]
    MOI_LC1_ADAPTED_TRIANGULATION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[POLYTOPE_INTERVAL; FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT;
                    NOT_IN_EMPTY; POLYTOPE_SING; INTER_SUBSET; SING_SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "aff") MP_TAC)))) THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `a:real^3`; `b:real^3`; `p:real^3`]
    MOI_LC1_CORNER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real^3->bool` (X_CHOOSE_THEN `p1:real^3`
    (X_CHOOSE_THEN `m0:real^3` (X_CHOOSE_THEN `b0:real^3` (X_CHOOSE_THEN `g:real^3`
    (X_CHOOSE_THEN `c0:real^3` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `?x0 e. &0 < e /\ ball(x0:real^3,e) SUBSET tau` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(interior(tau:real^3->bool) = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTERIOR] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^3) IN tau` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(x0:real^3,e) SUBSET tau` THEN
    MP_TAC(ISPECL [`x0:real^3`; `e:real`] CENTRE_IN_BALL) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "aff" (MP_TAC o SPEC `tau:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^3->real^3` (X_CHOOSE_THEN `y:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "aft")))) THEN
  SUBGOAL_THEN `moi_s35_lin_at (psi:real^3->real^3) x0 l` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s35_lin_at] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `e:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN tau` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(x0:real^3,e) SUBSET tau` THEN
      UNDISCH_TAC `(z:real^3) IN ball(x0,e)` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_SUB] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^3->real^3)(p1 - p) = (psi:real^3->real^3) p1 - psi p /\
                l(b0 - m0) = psi b0 - psi m0 /\ l(c0 - g) = psi c0 - psi g`
  (LABEL_TAC "lfr") THENL
   [ASM_SIMP_TAC[LINEAR_SUB] THEN REPEAT CONJ_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "aft" (K ALL_TAC) THEN
  SUBGOAL_THEN `!z:real^3. z IN tau ==> z IN interval[a,b] /\ z IN ball(p,r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN interval[a,b]` ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS t = interval[a:real^3,b]` THEN
      UNDISCH_TAC `(tau:real^3->bool) IN t` THEN UNDISCH_TAC `(z:real^3) IN tau` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `interval[a:real^3,b] SUBSET ball(p,r)` THEN
    UNDISCH_TAC `(z:real^3) IN interval[a,b]` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN tau ==> (((psi:real^3->real^3) z)$1 = &0 <=> z$1 = &0) /\
                            ((psi z)$2 = &0 <=> z$2 = &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ASSUME `!z:real^3. z IN ball(p,r)
                           ==> (((psi:real^3->real^3) z)$1 = &0 <=> z$1 = &0) /\
                               ((psi z)$2 = &0 <=> z$2 = &0)`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((psi:real^3->real^3) p)$1 = &0 /\ (psi p)$2 = &0 /\
    (psi p1)$1 = &0 /\ (psi p1)$2 = &0 /\ (psi m0)$1 = &0 /\ (psi m0)$2 = &0 /\
    (psi b0)$2 = &0 /\ (psi g)$2 = &0`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((psi:real^3->real^3) p)$3 < (psi p1)$3` ASSUME_TAC THENL
   [MATCH_MP_TAC(ASSUME `!z:real^3. z IN ball(p,r) /\ z$1 = &0 /\ z$2 = &0 /\
                                    p$3 < z$3
                                    ==> ((psi:real^3->real^3) p)$3 < (psi z)$3`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ((psi:real^3->real^3) b0)$1` ASSUME_TAC THENL
   [MATCH_MP_TAC(ASSUME `!z:real^3. z IN ball(p,r) /\ z$2 = &0 /\ &0 < z$1
                                    ==> &0 < ((psi:real^3->real^3) z)$1`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ((psi:real^3->real^3) c0)$2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`psi:real^3->real^3`;
                   `interval[a:real^3,b] INTER {z:real^3 | z$2 > &0}`; `2`;
                   `p + (d / &2) % basis 2:real^3`] MOI_LC1_SIDE_POS) THEN
    SUBGOAL_THEN `(p + (d / &2) % basis 2:real^3) IN ball(p,r)` ASSUME_TAC THENL
     [UNDISCH_TAC `interval[a:real^3,b] SUBSET ball(p,r)` THEN
      UNDISCH_TAC `(p + (d / &2) % basis 2:real^3) IN interval[a,b]` THEN SET_TAC[];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[CONVEX_INTERVAL; CONVEX_HALFSPACE_COMPONENT_GT];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `interval[a:real^3,b] SUBSET ball(p,r)` THEN
        UNDISCH_TAC `ball(p:real^3,r) SUBSET w` THEN SET_TAC[];
        ARITH_TAC;
        ARITH_TAC;
        ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
        SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
                 DIMINDEX_3; ARITH] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(ASSUME `!z:real^3. z IN ball(p,r) /\ z$1 = &0 /\ &0 < z$2
                                        ==> &0 < ((psi:real^3->real^3) z)$2`) THEN
        ASM_REWRITE_TAC[] THEN
        SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
                 DIMINDEX_3; ARITH] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt] THEN X_GEN_TAC `z:real^3` THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `(z:real^3) IN ball(p,r)` ASSUME_TAC THENL
         [UNDISCH_TAC `interval[a:real^3,b] SUBSET ball(p,r)` THEN
          UNDISCH_TAC `(z:real^3) IN interval[a,b]` THEN SET_TAC[];
          ALL_TAC] THEN
        MP_TAC(CONJUNCT2(MATCH_MP (ASSUME `!z:real^3. z IN ball(p,r)
                           ==> (((psi:real^3->real^3) z)$1 = &0 <=> z$1 = &0) /\
                               ((psi z)$2 = &0 <=> z$2 = &0)`)
                         (ASSUME `(z:real^3) IN ball(p,r)`))) THEN
        DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the linear part on the frame *)
  SUBGOAL_THEN `(p1:real^3) - p = ((p1:real^3)$3 - (p:real^3)$3) % basis 3 /\
                (b0:real^3) - m0 = (b0:real^3)$1 % basis 1 /\
                (c0:real^3) - g = (c0:real^3)$2 % basis 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT; ARITH] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (p1:real^3)$3 - (p:real^3)$3` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(l:real^3->real^3)(basis 3) =
      inv((p1:real^3)$3 - (p:real^3)$3) % ((psi:real^3->real^3) p1 - psi p) /\
    l(basis 1) = inv((b0:real^3)$1) % (psi b0 - psi m0) /\
    l(basis 2) = inv((c0:real^3)$2) % (psi c0 - psi g)`
  STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "lfr" MP_TAC THEN ASM_SIMP_TAC[LINEAR_CMUL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
      (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (SUBST1_TAC o SYM))) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det(matrix(l:real^3->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LC1_DET_POS THEN
    ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT; REAL_SUB_REFL;
                    REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^3) IN ball(p,r)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^3) IN w` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(p:real^3,r) SUBSET w` THEN
    UNDISCH_TAC `(x0:real^3) IN ball(p,r)` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`x0:real^3`; `l:real^3->real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `m:real^3->real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `w:real^3->bool`; `x:real^3`; `x0:real^3`;
                 `m:real^3->real^3`; `l:real^3->real^3`] LOCAL_SIGN) THEN
  ASM_REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* B3a. Generic tools: PL circles are topological circles; a nonvanishing   *)
(* continuous function on a connected set has constant sign; two close     *)
(* unit vectors with zero cross product are equal; the local preimage of a  *)
(* point with at most two preimages; germs of images; the open triangle.   *)
(* ------------------------------------------------------------------------- *)

let MOI_LC1_PL_SPHERE1_CIRCLE = prove
 (`!j:real^N->bool. pl_sphere 1 j ==> j homeomorphic sphere(vec 0:real^2,&1)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`j:real^N->bool`; `relative_frontier k:real^N->bool`;
                 `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_TRANS) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    ASM_MESON_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] RELATIVE_FRONTIER_CBALL) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
  ASM_SIMP_TAC[CONVEX_CBALL; BOUNDED_CBALL] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
                  ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  REWRITE_TAC[AFF_DIM_CBALL; REAL_LT_01; DIMINDEX_2]);;

let MOI_LC1_CONNECTED_SIGN = prove
 (`!(ff:real^M->real) s.
     connected s /\ (lift o ff) continuous_on s /\ (!w. w IN s ==> ~(ff w = &0))
     ==> (!w. w IN s ==> &0 < ff w) \/ (!w. w IN s ==> ff w < &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TAUT `p \/ q <=> ~p ==> q`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^M` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (lift o (ff:real^M->real)) s`; `lift((ff:real^M->real) w0)`;
                 `lift((ff:real^M->real) w)`; `vec 1:real^1`; `&0`]
    CONNECTED_IVT_HYPERPLANE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE; DOT_1; VEC_COMPONENT; LIFT_COMPONENT;
                 REAL_MUL_LID] THEN
    REWRITE_TAC[IN_IMAGE; o_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; o_THM; DOT_1; VEC_COMPONENT; LIFT_COMPONENT;
              REAL_MUL_LID] THEN
  ASM_MESON_TAC[]);;

let MOI_LC1_UNIT_CROSS = prove
 (`!a b:real^2.
     norm a = &1 /\ norm b = &1 /\ norm(a - b) < &1 /\ a$1 * b$2 - a$2 * b$1 = &0
     ==> a = b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[NORM_EQ_1; NORM_LT_SQUARE; DOT_2; VECTOR_SUB_COMPONENT] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((a:real^2)$1 * (b:real^2)$1 + a$2 * b$2 = &1) \/
                (a$1 * b$1 + a$2 * b$2 = -- &1)` MP_TAC THENL
   [UNDISCH_TAC `(a:real^2)$1 * a$1 + a$2 * a$2 = &1` THEN
    UNDISCH_TAC `(b:real^2)$1 * b$1 + b$2 * b$2 = &1` THEN
    UNDISCH_TAC `(a:real^2)$1 * (b:real^2)$2 - a$2 * b$1 = &0` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `((a:real^2)$1 - (b:real^2)$1) * (a$1 - b$1) + (a$2 - b$2) * (a$2 - b$2) =
                &2 - &2 * (a$1 * b$1 + a$2 * b$2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(a:real^2)$1 * a$1 + a$2 * a$2 = &1` THEN
    UNDISCH_TAC `(b:real^2)$1 * b$1 + b$2 * b$2 = &1` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  STRIP_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `((a:real^2)$1 - (b:real^2)$1) * (a$1 - b$1) = &0 /\
                (a$2 - b$2) * (a$2 - b$2) = &0` MP_TAC THENL
   [MP_TAC(SPEC `(a:real^2)$1 - (b:real^2)$1` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `(a:real^2)$2 - (b:real^2)$2` REAL_LE_SQUARE) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ENTIRE] THEN REAL_ARITH_TAC]);;

let MOI_LC1_LOCAL_PREIMAGE = prove
 (`!(f:real^2->real^N) x x' e.
     f continuous_on std_triangle /\ x IN std_triangle /\
     (!z. z IN std_triangle /\ f z = f x ==> z = x \/ z = x') /\ &0 < e
     ==> ?d. &0 < d /\
             !z. z IN std_triangle /\ dist(f z,f x) < d
                 ==> dist(x,z) < e \/ dist(x',z) < e`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `kk = std_triangle DIFF (ball(x:real^2,e) UNION ball(x',e))` THEN
  SUBGOAL_THEN `compact(IMAGE (f:real^2->real^N) kk)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "kk" THEN SET_TAC[];
      EXPAND_TAC "kk" THEN MATCH_MP_TAC COMPACT_DIFF THEN
      REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN
      SIMP_TAC[OPEN_UNION; OPEN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((f:real^2->real^N) x IN IMAGE f kk)` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_UNION; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `z:real^2 = x \/ z = x'` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN UNDISCH_TAC `~(dist(x:real^2,z) < e \/ dist(x',z) < e)` THEN
    ASM_REWRITE_TAC[DIST_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f:real^2->real^N) kk`; `(f:real^2->real^N) x`]
    SEPARATE_POINT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^2) IN kk` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNION; IN_BALL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^2->real^N) z`) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_LC1_GERM = prove
 (`!(f:real^2->real^N) x x' A e.
     f continuous_on std_triangle /\ x IN std_triangle /\
     (!z. z IN std_triangle /\ f z = f x ==> z = x \/ z = x') /\
     &0 < e /\ A SUBSET std_triangle /\ A INTER ball(x',e) = {}
     ==> ?d. &0 < d /\
             !y. dist(y,f x) < d
                 ==> (y IN IMAGE f A <=> y IN IMAGE f (A INTER ball(x,e)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `x:real^2`; `x':real^2`; `e:real`]
    MOI_LC1_LOCAL_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EQ_TAC THENL
   [ALL_TAC; SPEC_TAC(`y:real^N`,`y:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[IN_BALL] THEN
  SUBGOAL_THEN `dist(x:real^2,z) < e \/ dist(x',z) < e` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
  REWRITE_TAC[GSYM IN_BALL] THEN ASM SET_TAC[]);;

let MOI_LC1_OPEN_TRIANGLE = prove
 (`std_triangle DIFF relative_frontier std_triangle = interior std_triangle`,
  SUBGOAL_THEN `~(interior std_triangle = {})` ASSUME_TAC THENL
   [MP_TAC(ISPEC `std_triangle` AFF_DIM_NONEMPTY_INTERIOR_EQ) THEN
    REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[DIMINDEX_2] THEN MATCH_MP_TAC AFF_DIM_SIMPLEX THEN
    REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[relative_frontier; GSYM RELATIVE_INTERIOR_NONEMPTY_INTERIOR] THEN
  SIMP_TAC[CLOSURE_CLOSED; MOI_LTD_STD_TRIANGLE_BASIC] THEN
  MP_TAC(ISPEC `std_triangle` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* B3b. Normalized charts at a point x of the preimage polygon J with other *)
(* preimage x': a PL chart g of the interior of c on the unit ball whose    *)
(* planes z2 = 0 and z1 = 0 near p carry the sheets through x and x', whose *)
(* half-planes z1 > 0 and z2 > 0 carry their inner sides (towards inside J) *)
(* and whose axis is ordered by the local cyclic order of k (the sign of    *)
(* the cross product of th, a homeomorphism of k onto the unit circle).     *)
(* ------------------------------------------------------------------------- *)

let moi_lc1_cross = new_definition
 `moi_lc1_cross (a:real^2) (b:real^2) = a$1 * b$2 - a$2 * b$1`;;

let moi_lc1_nchart = new_definition
 `moi_lc1_nchart (c:(real^N->bool)->bool) (f:real^2->real^N) (J:real^2->bool)
                 (th:real^N->real^2) rho (x:real^2) (x':real^2) (g:real^3->real^N)
                 (p:real^3) r <=>
    (?g'. pl_homeomorphism (ball(vec 0,&1),IMAGE g (ball(vec 0,&1))) (g,g')) /\
    open_in (subtopology euclidean (UNIONS c)) (IMAGE g (ball(vec 0,&1))) /\
    IMAGE g (ball(vec 0,&1)) INTER complex_boundary c = {} /\
    p$1 = &0 /\ p$2 = &0 /\ g p = f x /\ &0 < r /\ ball(p,r) SUBSET ball(vec 0,&1) /\
    !z. z IN ball(p,r)
        ==> (z$2 = &0 <=> g z IN IMAGE f (std_triangle INTER ball(x,rho))) /\
            (z$1 = &0 <=> g z IN IMAGE f (std_triangle INTER ball(x',rho))) /\
            (z$2 = &0 /\ &0 < z$1 <=> g z IN IMAGE f (inside J INTER ball(x,rho))) /\
            (z$1 = &0 /\ &0 < z$2 <=> g z IN IMAGE f (inside J INTER ball(x',rho))) /\
            (!z'. z' IN ball(p,r) /\ z$1 = &0 /\ z$2 = &0 /\ z'$1 = &0 /\ z'$2 = &0
                  ==> (z$3 < z'$3 <=> &0 < moi_lc1_cross (th(g z)) (th(g z'))))`;;

(* The swap of the first two coordinates. *)

let moi_lc1_swap = new_definition
 `moi_lc1_swap (z:real^3) = vector[z$2; z$1; z$3]:real^3`;;

let MOI_LC1_SWAP_COMPONENTS = prove
 (`!z:real^3. (moi_lc1_swap z)$1 = z$2 /\ (moi_lc1_swap z)$2 = z$1 /\
              (moi_lc1_swap z)$3 = z$3`,
  REWRITE_TAC[moi_lc1_swap; VECTOR_3]);;

let MOI_LC1_SWAP_SWAP = prove
 (`!z:real^3. moi_lc1_swap(moi_lc1_swap z) = z`,
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MOI_LC1_SWAP_COMPONENTS]);;

let MOI_LC1_SWAP_LINEAR = prove
 (`linear moi_lc1_swap`,
  REWRITE_TAC[linear] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MOI_LC1_SWAP_COMPONENTS;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT]);;

let MOI_LC1_SWAP_DIST = prove
 (`!y z:real^3. dist(moi_lc1_swap y,moi_lc1_swap z) = dist(y,z)`,
  REWRITE_TAC[dist; vector_norm; DOT_3; VECTOR_SUB_COMPONENT;
              MOI_LC1_SWAP_COMPONENTS] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let MOI_LC1_SWAP_BALL = prove
 (`!z:real^3 r. IMAGE moi_lc1_swap (ball(z,r)) = ball(moi_lc1_swap z,r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BALL] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[MOI_LC1_SWAP_DIST];
    DISCH_TAC THEN EXISTS_TAC `moi_lc1_swap y` THEN
    REWRITE_TAC[MOI_LC1_SWAP_SWAP] THEN
    ONCE_REWRITE_TAC[GSYM MOI_LC1_SWAP_DIST] THEN
    ASM_REWRITE_TAC[MOI_LC1_SWAP_SWAP]]);;

let MOI_LC1_SWAP_VEC0 = prove
 (`moi_lc1_swap(vec 0) = vec 0`,
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MOI_LC1_SWAP_COMPONENTS; VEC_COMPONENT]);;

let MOI_LC1_SWAP_DET = prove
 (`det(matrix moi_lc1_swap) = -- &1`,
  SIMP_TAC[DET_3; matrix; LAMBDA_BETA; DIMINDEX_3; ARITH; MOI_LC1_SWAP_COMPONENTS;
           BASIS_COMPONENT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let MOI_LC1_SWAP_PL_HOMEO = prove
 (`pl_homeomorphism (ball(vec 0:real^3,&1),ball(vec 0,&1)) (moi_lc1_swap,moi_lc1_swap)`,
  REWRITE_TAC[pl_homeomorphism; homeomorphism; MOI_LC1_SWAP_SWAP] THEN
  REWRITE_TAC[MOI_LC1_SWAP_BALL; MOI_LC1_SWAP_VEC0] THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_LC1_SWAP_LINEAR] THEN
  SUBGOAL_THEN `moi_lc1_swap = (\x. moi_lc1_swap x + vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_RID]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
  SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_BALL; MOI_LC1_SWAP_LINEAR]);;

let MOI_LC1_NCHART_SWAP = prove
 (`!c (f:real^2->real^N) J th rho x x' g p r.
     moi_lc1_nchart c f J th rho x x' g p r /\ f x' = f x
     ==> moi_lc1_nchart c f J th rho x' x (g o moi_lc1_swap) (moi_lc1_swap p) r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lc1_nchart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `g':real^N->real^3`) MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN DISCH_THEN(LABEL_TAC "cond") THEN
  SUBGOAL_THEN `IMAGE ((g:real^3->real^N) o moi_lc1_swap) (ball(vec 0,&1)) =
                IMAGE g (ball(vec 0,&1))` SUBST1_TAC THENL
   [REWRITE_TAC[IMAGE_o; MOI_LC1_SWAP_BALL; MOI_LC1_SWAP_VEC0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_LC1_SWAP_COMPONENTS; o_THM; MOI_LC1_SWAP_SWAP] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `moi_lc1_swap o (g':real^N->real^3)` THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `ball(vec 0:real^3,&1)` THEN ASM_REWRITE_TAC[MOI_LC1_SWAP_PL_HOMEO];
    REWRITE_TAC[GSYM MOI_LC1_SWAP_BALL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE moi_lc1_swap (ball(vec 0,&1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MOI_LC1_SWAP_BALL; MOI_LC1_SWAP_VEC0; SUBSET_REFL]];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_lc1_swap z IN ball(p:real^3,r)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[GSYM MOI_LC1_SWAP_DIST] THEN
    ASM_REWRITE_TAC[MOI_LC1_SWAP_SWAP; GSYM IN_BALL];
    ALL_TAC] THEN
  USE_THEN "cond" (MP_TAC o C MATCH_MP (ASSUME `moi_lc1_swap z IN ball(p:real^3,r)`)) THEN
  REWRITE_TAC[MOI_LC1_SWAP_COMPONENTS] THEN
  MATCH_MP_TAC(TAUT `(e ==> e') ==> (a /\ b /\ c /\ d /\ e ==> b /\ a /\ d /\ c /\ e')`) THEN
  DISCH_THEN(LABEL_TAC "ax") THEN X_GEN_TAC `z':real^3` THEN STRIP_TAC THEN
  USE_THEN "ax" (MP_TAC o SPEC `moi_lc1_swap z'`) THEN
  REWRITE_TAC[MOI_LC1_SWAP_COMPONENTS] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[GSYM MOI_LC1_SWAP_DIST] THEN
  REWRITE_TAC[MOI_LC1_SWAP_SWAP; GSYM IN_BALL] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* B3c. Orientation signs of normalized charts: the swapped chart has the   *)
(* opposite sign; two normalized charts at the same point (same rho) have   *)
(* the same sign (the transition psi = g2^-1 o g1 is a normalized           *)
(* configuration map: MOI_LC1_CONFIG_SIGN and MOI_LC1_TRANSITION_SIGN).     *)
(* ------------------------------------------------------------------------- *)

let MOI_LC1_OSIGN_SWAP = prove
 (`!(c:(real^N->bool)->bool) sg (g:real^3->real^N) s s'.
     FINITE c /\ lf_simplicial_complex c /\ (!t. t IN c ==> aff_dim t <= &3) /\
     (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
                ==> (sg a b d e = &1 \/ sg a b d e = -- &1)) /\
     pl_map_on (ball(vec 0,&1)) g /\
     (!x y. x IN ball(vec 0,&1) /\ y IN ball(vec 0,&1) /\ g x = g y ==> x = y) /\
     IMAGE g (ball(vec 0,&1)) SUBSET UNIONS c /\
     moi_lc1_osign c sg g (ball(vec 0,&1)) s /\ (s = &1 \/ s = -- &1) /\
     moi_lc1_osign c sg (g o moi_lc1_swap) (ball(vec 0,&1)) s'
     ==> s' = --s`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real^N->real`;
                 `(g:real^3->real^N) o moi_lc1_swap`; `g:real^3->real^N`;
                 `ball(vec 0:real^3,&1)`; `ball(vec 0:real^3,&1)`; `s':real`; `s:real`;
                 `moi_lc1_swap`; `ball(vec 0:real^3,&1)`] MOI_LC1_TRANSITION_SIGN) THEN
  SUBGOAL_THEN `IMAGE moi_lc1_swap (ball(vec 0,&1)) = ball(vec 0,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LC1_SWAP_BALL; MOI_LC1_SWAP_VEC0]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; CONNECTED_BALL; BALL_EQ_EMPTY; SUBSET_REFL; o_THM;
                    IMAGE_o] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `ball(vec 0:real^3,&1)` THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN
      MP_TAC MOI_LC1_SWAP_PL_HOMEO THEN SIMP_TAC[pl_homeomorphism];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `moi_lc1_swap x = moi_lc1_swap y` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE moi_lc1_swap (ball(vec 0,&1)) = ball(vec 0,&1)` THEN
        ASM SET_TAC[];
        MESON_TAC[MOI_LC1_SWAP_SWAP]];
      REAL_ARITH_TAC;
      SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_LC1_SWAP_LINEAR]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`vec 0:real^3`; `moi_lc1_swap`]) THEN
  REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_01; moi_s35_lin_at; MOI_LC1_SWAP_LINEAR] THEN
  ANTS_TAC THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; MOI_LC1_SWAP_VEC0; VECTOR_SUB_RZERO;
                                     VECTOR_ADD_LID];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_LC1_SWAP_DET; real_sgn] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  UNDISCH_TAC `s = &1 \/ s = -- &1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let MOI_LC1_CHART_INDEP = prove
 (`!(c:(real^N->bool)->bool) sg (f:real^2->real^N) J th rho x x' g1 p1 r1 g2 p2 r2
    s1 s2.
     FINITE c /\ lf_simplicial_complex c /\ (!t. t IN c ==> aff_dim t <= &3) /\
     (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
                ==> (sg a b d e = &1 \/ sg a b d e = -- &1)) /\
     moi_lc1_nchart c f J th rho x x' g1 p1 r1 /\
     moi_lc1_nchart c f J th rho x x' g2 p2 r2 /\
     moi_lc1_osign c sg g1 (ball(vec 0,&1)) s1 /\ (s1 = &1 \/ s1 = -- &1) /\
     moi_lc1_osign c sg g2 (ball(vec 0,&1)) s2 /\ (s2 = &1 \/ s2 = -- &1)
     ==> s1 = s2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))) THEN
  REWRITE_TAC[moi_lc1_nchart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `g2':real^N->real^3`) MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN DISCH_THEN(LABEL_TAC "c2") THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `g1':real^N->real^3`) MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN DISCH_THEN(LABEL_TAC "c1") THEN
  SUBGOAL_THEN
   `homeomorphism (ball(vec 0,&1),IMAGE (g1:real^3->real^N) (ball(vec 0,&1))) (g1,g1') /\
    pl_map_on (ball(vec 0,&1)) g1 /\
    homeomorphism (ball(vec 0,&1),IMAGE (g2:real^3->real^N) (ball(vec 0,&1))) (g2,g2') /\
    pl_map_on (ball(vec 0,&1)) g2 /\ pl_map_on (IMAGE g2 (ball(vec 0,&1))) g2'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `(g1:real^3->real^N) continuous_on ball(vec 0,&1) /\
                (g2':real^N->real^3) continuous_on IMAGE g2 (ball(vec 0,&1)) /\
                (!z. z IN ball(vec 0,&1) ==> g2'((g2:real^3->real^N) z) = z) /\
                (!y. y IN IMAGE g2 (ball(vec 0,&1)) ==> g2(g2' y) = y) /\
                (!z z'. z IN ball(vec 0,&1) /\ z' IN ball(vec 0,&1) /\
                        (g1:real^3->real^N) z = g1 z' ==> z = z')`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p1:real^3) IN ball(p1,r1) /\ (p2:real^3) IN ball(p2,r2) /\
                p1 IN ball(vec 0,&1) /\ p2 IN ball(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ball(p1:real^3,r1) SUBSET ball(vec 0,&1)` THEN
      MP_TAC(ISPECL [`p1:real^3`; `r1:real`] CENTRE_IN_BALL) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      UNDISCH_TAC `ball(p2:real^3,r2) SUBSET ball(vec 0,&1)` THEN
      MP_TAC(ISPECL [`p2:real^3`; `r2:real`] CENTRE_IN_BALL) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (UNIONS c))
            (IMAGE (g2:real^3->real^N) (ball(p2,r2)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN
    EXISTS_TAC `IMAGE (g2:real^3->real^N) (ball(vec 0,&1))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g2':real^N->real^3`; `ball(vec 0:real^3,&1)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_SUBSET THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?r3. &0 < r3 /\ r3 <= r1 /\
         IMAGE (g1:real^3->real^N) (ball(p1,r3)) SUBSET IMAGE (g2:real^3->real^N) (ball(p2,r2))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g1:real^3->real^N`; `ball(vec 0:real^3,&1)`; `UNIONS c:real^N->bool`;
                   `IMAGE (g2:real^3->real^N) (ball(p2,r2))`]
      CONTINUOUS_OPEN_IN_PREIMAGE_GEN) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] OPEN_IN_OPEN_TRANS)) THEN
    REWRITE_TAC[OPEN_BALL; OPEN_CONTAINS_BALL; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `p1:real^3`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `p2:real^3` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "be"))) THEN
    EXISTS_TAC `min e r1` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (g1:real^3->real^N) (ball(p1,e))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN
      SIMP_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC;
      REMOVE_THEN "be" MP_TAC THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `psi = (g2':real^N->real^3) o (g1:real^3->real^N)` THEN
  SUBGOAL_THEN `!z:real^3. z IN ball(p1,r3)
                           ==> (psi:real^3->real^3) z IN ball(p2,r2) /\
                               (g2:real^3->real^N)(psi z) = (g1:real^3->real^N) z /\
                               z IN ball(p1,r1) /\ z IN ball(vec 0,&1)`
  (LABEL_TAC "pz") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN ball(p1,r1)` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(p1,r3)` THEN REWRITE_TAC[IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `?w:real^3. w IN ball(p2,r2) /\ (g1:real^3->real^N) z = g2 w`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (g1:real^3->real^N) (ball(p1,r3)) SUBSET
                   IMAGE (g2:real^3->real^N) (ball(p2,r2))` THEN
      UNDISCH_TAC `(z:real^3) IN ball(p1,r3)` THEN SET_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "psi" THEN REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(w:real^3) IN ball(vec 0,&1) /\ (z:real^3) IN ball(vec 0,&1)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ball(p2:real^3,r2) SUBSET ball(vec 0,&1)` THEN
      UNDISCH_TAC `ball(p1:real^3,r1) SUBSET ball(vec 0,&1)` THEN
      UNDISCH_TAC `(w:real^3) IN ball(p2,r2)` THEN
      UNDISCH_TAC `(z:real^3) IN ball(p1,r1)` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^3->real^3) p1 = p2` ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(g1:real^3->real^N) p1 = f(x:real^2)` THEN
    UNDISCH_TAC `(g2:real^3->real^N) p2 = f(x:real^2)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(p1:real^3,r3) SUBSET ball(p1,r1) /\
                ball(p1:real^3,r3) SUBSET ball(vec 0,&1) /\
                IMAGE (g1:real^3->real^N) (ball(p1,r3)) SUBSET
                IMAGE (g2:real^3->real^N) (ball(vec 0,&1)) /\
                IMAGE (g1:real^3->real^N) (ball(vec 0,&1)) SUBSET UNIONS c /\
                IMAGE (g2:real^3->real^N) (ball(vec 0,&1)) SUBSET UNIONS c`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `ball(p1:real^3,r3) SUBSET ball(p1,r1)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(p1:real^3,r1)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (g2:real^3->real^N) (ball(p2,r2))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_IMP_SUBSET THEN EXISTS_TAC `euclidean:(real^N)topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_IMP_SUBSET THEN EXISTS_TAC `euclidean:(real^N)topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^3->real^3) continuous_on ball(p1,r3)` ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&1)` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (g2:real^3->real^N) (ball(vec 0,&1))` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z z':real^3. z IN ball(p1,r3) /\ z' IN ball(p1,r3) /\
                              (psi:real^3->real^3) z = psi z' ==> z = z'`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:real^3`; `z':real^3`] THEN STRIP_TAC THEN
    USE_THEN "pz" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(p1,r3)`)) THEN
    USE_THEN "pz" (MP_TAC o C MATCH_MP (ASSUME `(z':real^3) IN ball(p1,r3)`)) THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ASSUME `!z z'. z IN ball(vec 0,&1) /\ z' IN ball(vec 0,&1) /\
                                (g1:real^3->real^N) z = g1 z' ==> z = z'`) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(g2:real^3->real^N)((psi:real^3->real^3) z) = (g1:real^3->real^N) z` THEN
    UNDISCH_TAC `(g2:real^3->real^N)((psi:real^3->real^3) z') = (g1:real^3->real^N) z'` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z z':real^3. z IN ball(vec 0,&1) /\ z' IN ball(vec 0,&1) /\
                              (g2:real^3->real^N) z = g2 z' ==> z = z'`
  ASSUME_TAC THENL
   [MESON_TAC[ASSUME `!z. z IN ball(vec 0,&1)
                          ==> (g2':real^N->real^3)((g2:real^3->real^N) z) = z`];
    ALL_TAC] THEN
  (* the transition sign *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real^N->real`;
                 `g1:real^3->real^N`; `g2:real^3->real^N`;
                 `ball(vec 0:real^3,&1)`; `ball(vec 0:real^3,&1)`; `s1:real`; `s2:real`;
                 `psi:real^3->real^3`; `ball(p1:real^3,r3)`] MOI_LC1_TRANSITION_SIGN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; CONNECTED_BALL; BALL_EQ_EMPTY; REAL_NOT_LE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      USE_THEN "pz" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(p1,r3)`)) THEN
      STRIP_TAC THEN
      UNDISCH_TAC `ball(p2:real^3,r2) SUBSET ball(vec 0,&1)` THEN
      UNDISCH_TAC `(psi:real^3->real^3) z IN ball(p2,r2)` THEN SET_TAC[];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      USE_THEN "pz" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(p1,r3)`)) THEN
      SIMP_TAC[]];
    DISCH_THEN(LABEL_TAC "trans")] THEN
  (* the plane conditions for psi *)
  SUBGOAL_THEN
   `!z. z IN ball(p1,r3)
        ==> (((psi:real^3->real^3) z)$1 = &0 <=> z$1 = &0) /\
            ((psi z)$2 = &0 <=> z$2 = &0)`
  (LABEL_TAC "piff") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "pz" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(p1,r3)`)) THEN
    STRIP_TAC THEN
    USE_THEN "c1" (fun th -> ASSUME_TAC(MATCH_MP th (ASSUME `(z:real^3) IN ball(p1,r1)`))) THEN
    USE_THEN "c2" (fun th -> ASSUME_TAC(MATCH_MP th
      (ASSUME `(psi:real^3->real^3) z IN ball(p2,r2)`))) THEN
    POP_ASSUM(fun th2 -> POP_ASSUM(fun th1 -> REWRITE_TAC[th1; th2;
      ASSUME `(g2:real^3->real^N)((psi:real^3->real^3) z) = (g1:real^3->real^N) z`]));
    ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `ball(p1:real^3,r3)`; `p1:real^3`; `r3:real`]
    MOI_LC1_CONFIG_SIGN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; CONNECTED_BALL; SUBSET_REFL] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "psi" THEN MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
      EXISTS_TAC `IMAGE (g2:real^3->real^N) (ball(vec 0,&1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&1)` THEN
        ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_BALL];
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      USE_THEN "pz" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(p1,r3)`)) THEN
      STRIP_TAC THEN
      USE_THEN "c1" (fun th -> MP_TAC(el 2 (CONJUNCTS(MATCH_MP th
        (ASSUME `(z:real^3) IN ball(p1,r1)`))))) THEN
      USE_THEN "c2" (fun th -> MP_TAC(el 2 (CONJUNCTS(MATCH_MP th
        (ASSUME `(psi:real^3->real^3) z IN ball(p2,r2)`))))) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      USE_THEN "pz" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(p1,r3)`)) THEN
      STRIP_TAC THEN
      USE_THEN "c1" (fun th -> MP_TAC(el 3 (CONJUNCTS(MATCH_MP th
        (ASSUME `(z:real^3) IN ball(p1,r1)`))))) THEN
      USE_THEN "c2" (fun th -> MP_TAC(el 3 (CONJUNCTS(MATCH_MP th
        (ASSUME `(psi:real^3->real^3) z IN ball(p2,r2)`))))) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      USE_THEN "pz" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(p1,r3)`)) THEN
      STRIP_TAC THEN
      USE_THEN "piff" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(p1,r3)`)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "c1" (fun th -> MP_TAC(SPEC `z:real^3` (el 4 (CONJUNCTS(MATCH_MP th
        (ASSUME `(p1:real^3) IN ball(p1,r1)`)))))) THEN
      USE_THEN "c2" (fun th -> MP_TAC(SPEC `(psi:real^3->real^3) z`
        (el 4 (CONJUNCTS(MATCH_MP th (ASSUME `(p2:real^3) IN ball(p2,r2)`)))))) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x0:real^3` (X_CHOOSE_THEN `m0:real^3->real^3`
    STRIP_ASSUME_TAC)) (MP_TAC o SPECL [`x0:real^3`; `m0:real^3->real^3`])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `real_sgn(det(matrix(m0:real^3->real^3))) = s1 * s2` MP_TAC THENL
   [USE_THEN "trans" (MATCH_MP_TAC o SPEC `x0:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[real_sgn] THEN
  MAP_EVERY UNDISCH_TAC [`s1 = &1 \/ s1 = -- &1`; `s2 = &1 \/ s2 = -- &1`] THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* B3d. Local constancy: a normalized chart at x is a normalized chart at   *)
(* every nearby point x1 (other preimage x1'), for any admissible radius,   *)
(* by the germ lemma (the images of two sets agreeing near x1 and missing  *)
(* a ball around x1' agree near f x1).                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_LC1_GERM_EQ = prove
 (`!(f:real^2->real^N) b b' A B e.
     f continuous_on std_triangle /\ b IN std_triangle /\
     (!z. z IN std_triangle /\ f z = f b ==> z = b \/ z = b') /\ &0 < e /\
     A SUBSET std_triangle /\ B SUBSET std_triangle /\
     A INTER ball(b',e) = {} /\ B INTER ball(b',e) = {} /\
     A INTER ball(b,e) = B INTER ball(b,e)
     ==> ?d. &0 < d /\ !y. dist(y,f b) < d ==> (y IN IMAGE f A <=> y IN IMAGE f B)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `b:real^2`; `b':real^2`; `A:real^2->bool`; `e:real`]
    MOI_LC1_GERM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g1"))) THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `b:real^2`; `b':real^2`; `B:real^2->bool`; `e:real`]
    MOI_LC1_GERM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g2"))) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  USE_THEN "g1" (MP_TAC o C MATCH_MP (ASSUME `dist(y:real^N,f(b:real^2)) < d1`)) THEN
  USE_THEN "g2" (MP_TAC o C MATCH_MP (ASSUME `dist(y:real^N,f(b:real^2)) < d2`)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_LC1_BALLS = prove
 (`!x x' x1 x1':real^2 rho rho1 e e5.
     &0 < rho /\ &2 * rho <= dist(x,x') /\ dist(x,x1) < e /\ e <= rho / &4 /\
     dist(x',x1') < rho / &4 /\ &0 < rho1 /\ &2 * rho1 <= dist(x1,x1') /\
     e5 <= rho1 /\ e5 <= rho / &4
     ==> ball(x1,e5) SUBSET ball(x,rho) /\ ball(x1,e5) SUBSET ball(x1,rho1) /\
         ball(x,rho) INTER ball(x1',e5) = {} /\ ball(x1,rho1) INTER ball(x1',e5) = {} /\
         ball(x1',e5) SUBSET ball(x',rho) /\ ball(x1',e5) SUBSET ball(x1',rho1) /\
         ball(x',rho) INTER ball(x1,e5) = {} /\ ball(x1',rho1) INTER ball(x1,e5) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; EXTENSION; IN_BALL; IN_INTER; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `y:real^2` THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NORM_ARITH);;

let MOI_LC1_NCHART_LOCAL = prove
 (`!c (f:real^2->real^N) J th rho x x' g p r.
     moi_lt_singular_disk c f /\ J SUBSET std_triangle /\
     x IN std_triangle /\ x' IN std_triangle /\ f x' = f x /\
     (!z. z IN std_triangle /\ f z = f x ==> z = x \/ z = x') /\
     &0 < rho /\ &2 * rho <= dist(x,x') /\
     moi_lc1_nchart c f J th rho x x' g p r
     ==> ?e. &0 < e /\
             !x1 x1' rho1.
               x1 IN std_triangle /\ dist(x,x1) < e /\ x1' IN std_triangle /\
               ~(x1' = x1) /\ f x1' = f x1 /\
               (!z. z IN std_triangle /\ f z = f x1 ==> z = x1 \/ z = x1') /\
               &0 < rho1 /\ &2 * rho1 <= dist(x1,x1')
               ==> ?p1 r1. moi_lc1_nchart c f J th rho1 x1 x1' g p1 r1`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `(f:real^2->real^N) continuous_on std_triangle /\
                IMAGE f std_triangle SUBSET UNIONS c`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_singular_disk; PL_MAP_ON_IMP_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `inside J SUBSET std_triangle` ASSUME_TAC THENL
   [MP_TAC(ISPEC `J:real^2->bool` MOI_LA1_INSIDE_TRIANGLE) THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[moi_lc1_nchart]
   (ASSUME `moi_lc1_nchart c (f:real^2->real^N) J th rho x x' g p r`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `g':real^N->real^3`) MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN DISCH_THEN(LABEL_TAC "cond") THEN
  SUBGOAL_THEN
   `homeomorphism (ball(vec 0,&1),IMAGE (g:real^3->real^N) (ball(vec 0,&1))) (g,g') /\
    (g:real^3->real^N) continuous_on ball(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN ball(p,r) /\ p IN ball(vec 0,&1)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    UNDISCH_TAC `ball(p:real^3,r) SUBSET ball(vec 0,&1)` THEN
    MP_TAC(ISPECL [`p:real^3`; `r:real`] CENTRE_IN_BALL) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (UNIONS c)) (IMAGE (g:real^3->real^N) (ball(p,r)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN
    EXISTS_TAC `IMAGE (g:real^3->real^N) (ball(vec 0,&1))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g':real^N->real^3`; `ball(vec 0:real^3,&1)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?e1. &0 < e1 /\
         !z. z IN std_triangle /\ dist(x,z) < e1
             ==> (f:real^2->real^N) z IN IMAGE (g:real^3->real^N) (ball(p,r))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^2->real^N`; `std_triangle`; `UNIONS c:real^N->bool`;
                   `IMAGE (g:real^3->real^N) (ball(p,r))`]
      CONTINUOUS_OPEN_IN_PREIMAGE_GEN) THEN
    ASM_REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2` o CONJUNCT2) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_ELIM_THM] THEN DISCH_TAC THEN
    EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `x:real^2`]
    MOI_LCC_LOCINJ_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj"))) THEN
  ABBREV_TAC `e3 = min (e2 / &2) (rho / &4)` THEN
  SUBGOAL_THEN `&0 < e3 /\ e3 <= e2 / &2 /\ e3 <= rho / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e3" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `x:real^2`; `x':real^2`; `e3:real`]
    MOI_LC1_LOCAL_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lp"))) THEN
  SUBGOAL_THEN
   `?e4. &0 < e4 /\ !z. z IN std_triangle /\ dist(z,x) < e4
                        ==> dist((f:real^2->real^N) z,f x) < d0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `(f:real^2->real^N) continuous_on std_triangle`) THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `d0:real`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `min e1 (min e3 e4)` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`x1:real^2`; `x1':real^2`; `rho1:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `dist((f:real^2->real^N) x1,f x) < d0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist((f:real^2->real^N) x1',f x) < d0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `dist(x':real^2,x1') < e3` ASSUME_TAC THENL
   [USE_THEN "lp" (MP_TAC o SPEC `x1':real^2`) THEN
    REWRITE_TAC[ASSUME `(x1':real^2) IN std_triangle`;
                ASSUME `dist((f:real^2->real^N) x1',f x) < d0`] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~(x1':real^2 = x1)` THEN REWRITE_TAC[] THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?p1:real^3. p1 IN ball(p,r) /\ (g:real^3->real^N) p1 = f(x1:real^2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:real^2->real^N) x1 IN IMAGE (g:real^3->real^N) (ball(p,r))`
    MP_TAC THENL
     [MATCH_MP_TAC(ASSUME `!z. z IN std_triangle /\ dist(x:real^2,z) < e1
                               ==> (f:real^2->real^N) z IN
                                   IMAGE (g:real^3->real^N) (ball(p,r))`) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p1:real^3)$2 = &0 /\ p1$1 = &0` STRIP_ASSUME_TAC THENL
   [USE_THEN "cond" (MP_TAC o C MATCH_MP (ASSUME `(p1:real^3) IN ball(p,r)`)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT1(CONJUNCT2 th)]) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_INTER; IN_BALL] THEN CONJ_TAC THENL
     [EXISTS_TAC `x1:real^2` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `x1':real^2` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `e5 = min rho1 (rho / &4)` THEN
  SUBGOAL_THEN `&0 < e5 /\ e5 <= rho1 /\ e5 <= rho / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e5" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^2`; `x':real^2`; `x1:real^2`; `x1':real^2`; `rho:real`;
                 `rho1:real`; `e3:real`; `e5:real`] MOI_LC1_BALLS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `!z. z IN std_triangle /\ (f:real^2->real^N) z = f x1'
                    ==> z = x1' \/ z = x1`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    MP_TAC(MATCH_MP (ASSUME `!z. z IN std_triangle /\ (f:real^2->real^N) z = f x1
                                 ==> z = x1 \/ z = x1'`)
      (CONJ (ASSUME `(z:real^2) IN std_triangle`)
            (TRANS (ASSUME `(f:real^2->real^N) z = f x1'`)
                   (ASSUME `(f:real^2->real^N) x1' = f x1`)))) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `x1:real^2`; `x1':real^2`;
                 `std_triangle INTER ball(x:real^2,rho)`;
                 `std_triangle INTER ball(x1:real^2,rho1)`; `e5:real`] MOI_LC1_GERM_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET] THEN
    MAP_EVERY UNDISCH_TAC
     [`ball(x1:real^2,e5) SUBSET ball(x,rho)`; `ball(x1:real^2,e5) SUBSET ball(x1,rho1)`;
      `ball(x:real^2,rho) INTER ball(x1',e5) = {}`;
      `ball(x1:real^2,rho1) INTER ball(x1',e5) = {}`] THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "q1")))] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `x1:real^2`; `x1':real^2`;
                 `inside J INTER ball(x:real^2,rho)`;
                 `inside J INTER ball(x1:real^2,rho1)`; `e5:real`] MOI_LC1_GERM_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`inside J SUBSET std_triangle`;
      `ball(x1:real^2,e5) SUBSET ball(x,rho)`; `ball(x1:real^2,e5) SUBSET ball(x1,rho1)`;
      `ball(x:real^2,rho) INTER ball(x1',e5) = {}`;
      `ball(x1:real^2,rho1) INTER ball(x1',e5) = {}`] THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "q2")))] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `x1':real^2`; `x1:real^2`;
                 `std_triangle INTER ball(x':real^2,rho)`;
                 `std_triangle INTER ball(x1':real^2,rho1)`; `e5:real`] MOI_LC1_GERM_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET] THEN
    MAP_EVERY UNDISCH_TAC
     [`ball(x1':real^2,e5) SUBSET ball(x',rho)`;
      `ball(x1':real^2,e5) SUBSET ball(x1',rho1)`;
      `ball(x':real^2,rho) INTER ball(x1,e5) = {}`;
      `ball(x1':real^2,rho1) INTER ball(x1,e5) = {}`] THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "q3" o
      REWRITE_RULE[ASSUME `(f:real^2->real^N) x1' = f x1`])))] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `x1':real^2`; `x1:real^2`;
                 `inside J INTER ball(x':real^2,rho)`;
                 `inside J INTER ball(x1':real^2,rho1)`; `e5:real`] MOI_LC1_GERM_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`inside J SUBSET std_triangle`;
      `ball(x1':real^2,e5) SUBSET ball(x',rho)`;
      `ball(x1':real^2,e5) SUBSET ball(x1',rho1)`;
      `ball(x':real^2,rho) INTER ball(x1,e5) = {}`;
      `ball(x1':real^2,rho1) INTER ball(x1,e5) = {}`] THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "q4" o
      REWRITE_RULE[ASSUME `(f:real^2->real^N) x1' = f x1`])))] THEN
  ABBREV_TAC `dd = min (min d1 d2) (min d3 d4)` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= d1 /\ dd <= d2 /\ dd <= d3 /\ dd <= d4`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "dd" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(p1:real^3) IN ball(vec 0,&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(p:real^3,r) SUBSET ball(vec 0,&1)` THEN
    UNDISCH_TAC `(p1:real^3) IN ball(p,r)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?r1. &0 < r1 /\ ball(p1:real^3,r1) SUBSET ball(p,r) /\
         !z. z IN ball(p1,r1) ==> dist((g:real^3->real^N) z,f(x1:real^2)) < dd`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `(g:real^3->real^N) continuous_on ball(vec 0,&1)`) THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `p1:real^3`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `dd:real`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gc"))) THEN
    EXISTS_TAC `min r0 (r - dist(p:real^3,p1))` THEN
    SUBGOAL_THEN `dist(p:real^3,p1) < r` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_BALL]; ALL_TAC] THEN
    SUBGOAL_THEN `ball(p1:real^3,min r0 (r - dist(p,p1))) SUBSET ball(p,r)`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `y:real^3` THEN
      UNDISCH_TAC `dist(p:real^3,p1) < r` THEN CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "gc" MATCH_MP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `ball(p:real^3,r) SUBSET ball(vec 0,&1)` THEN
      UNDISCH_TAC `ball(p1:real^3,min r0 (r - dist(p,p1))) SUBSET ball(p,r)` THEN
      UNDISCH_TAC `(z:real^3) IN ball(p1,min r0 (r - dist(p,p1)))` THEN SET_TAC[];
      UNDISCH_TAC `(z:real^3) IN ball(p1,min r0 (r - dist(p,p1)))` THEN
      REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p1:real^3`; `r1:real`] THEN REWRITE_TAC[moi_lc1_nchart] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `g':real^N->real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(p:real^3,r)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN ball(p,r)` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(p1:real^3,r1) SUBSET ball(p,r)` THEN
    UNDISCH_TAC `(z:real^3) IN ball(p1,r1)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist((g:real^3->real^N) z,f(x1:real^2)) < dd` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `dist((g:real^3->real^N) z,f(x1:real^2)) < d1 /\
                dist((g:real^3->real^N) z,f(x1:real^2)) < d2 /\
                dist((g:real^3->real^N) z,f(x1:real^2)) < d3 /\
                dist((g:real^3->real^N) z,f(x1:real^2)) < d4`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "q1" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
    (ASSUME `dist((g:real^3->real^N) z,f(x1:real^2)) < d1`))]) THEN
  USE_THEN "q2" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
    (ASSUME `dist((g:real^3->real^N) z,f(x1:real^2)) < d2`))]) THEN
  USE_THEN "q3" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
    (ASSUME `dist((g:real^3->real^N) z,f(x1:real^2)) < d3`))]) THEN
  USE_THEN "q4" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
    (ASSUME `dist((g:real^3->real^N) z,f(x1:real^2)) < d4`))]) THEN
  USE_THEN "cond" (MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN ball(p,r)`)) THEN
  MATCH_MP_TAC(TAUT `(e ==> e') ==> a /\ b /\ c /\ d /\ e ==> a /\ b /\ c /\ d /\ e'`) THEN
  DISCH_THEN(LABEL_TAC "ax") THEN X_GEN_TAC `z':real^3` THEN STRIP_TAC THEN
  USE_THEN "ax" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ball(p1:real^3,r1) SUBSET ball(p,r)` THEN
  UNDISCH_TAC `(z':real^3) IN ball(p1,r1)` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* B3e. Sheet sides: a sheet n through a point x of the Jordan curve J,     *)
(* mapped homeomorphically onto a plane disk whose diameter z_i = 0 carries *)
(* J INTER n, has one open half inside J and the other outside J            *)
(* (invariance of domain, Jordan curve theorem).                             *)
(* ------------------------------------------------------------------------- *)

let MOI_LC1_CONNECTED_OUTSIDE = prove
 (`!s t:real^2->bool.
     closed s /\ connected t /\ DISJOINT s t /\ ~(t INTER outside s = {})
     ==> t SUBSET outside s`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t INTER inside(s:real^2->bool) = {}` THENL
   [MP_TAC(ISPEC `s:real^2->bool` INSIDE_OUTSIDE) THEN ASM SET_TAC[];
    MP_TAC(ISPECL [`s:real^2->bool`; `t:real^2->bool`] MOI_LA1_CONNECTED_INSIDE) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `s:real^2->bool` INSIDE_OUTSIDE) THEN
    ASM SET_TAC[]]);;

let MOI_LC1_SHEET_SIDE = prove
 (`!(J:real^2->bool) (n:real^2->bool) (phi:real^2->real^3) i j x.
     (?gam:real^1->real^2. simple_path gam /\ pathfinish gam = pathstart gam /\
                           path_image gam = J) /\
     ((i = 1 /\ j = 2) \/ (i = 2 /\ j = 1)) /\
     open n /\ x IN n /\ x IN J /\
     phi continuous_on n /\ (!y z. y IN n /\ z IN n /\ phi y = phi z ==> y = z) /\
     IMAGE phi n = ball(vec 0,&1) INTER {z | z$j = &0} /\
     (!y. y IN n ==> (y IN J <=> (phi y)$i = &0))
     ==> ?a. (a = &1 \/ a = -- &1) /\
             !y. y IN n ==> (&0 < a * (phi y)$i ==> y IN inside J) /\
                            (a * (phi y)$i < &0 ==> y IN outside J)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `gam:real^1->real^2` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "ij") STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `gam:real^1->real^2` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed(J:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `path_image(gam:real^1->real^2) = J` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_PATH_IMAGE THEN
    ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH];
    ALL_TAC] THEN
  ABBREV_TAC `psi = \y:real^2. vector[((phi:real^2->real^3) y)$i; (phi y)$3]:real^2` THEN
  SUBGOAL_THEN `!y:real^2. (psi:real^2->real^2) y$1 = ((phi:real^2->real^3) y)$i /\
                           psi y$2 = (phi y)$3`
  ASSUME_TAC THENL [EXPAND_TAC "psi" THEN REWRITE_TAC[VECTOR_2]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. y IN n ==> ((phi:real^2->real^3) y)$j = &0` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(phi:real^2->real^3) y IN ball(vec 0,&1) INTER {z | z$j = &0}` MP_TAC
    THENL [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
             is_comb(lhs(concl th)) && rator(lhs(concl th)) = `IMAGE (phi:real^2->real^3)`)) THEN
           ASM SET_TAC[];
           SIMP_TAC[IN_INTER; IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^2->real^2) continuous_on n` ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN
    ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[o_DEF]
      `(\z:real^3. vector[z$i; z$3]:real^2) o (phi:real^2->real^3)`)] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    REWRITE_TAC[linear] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y z:real^2. y IN n /\ z IN n /\ (psi:real^2->real^2) y = psi z ==> y = z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(psi:real^2->real^2) y = psi z` THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `((phi:real^2->real^3) y)$j = &0 /\ ((phi:real^2->real^3) z)$j = &0`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "ij" (DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:real^2->real^2) n = ball(vec 0,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `w:real^2` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(phi:real^2->real^3) y IN ball(vec 0,&1) INTER {z | z$j = &0}`
      MP_TAC THENL
       [UNDISCH_TAC `IMAGE (phi:real^2->real^3) n = ball(vec 0,&1) INTER {z | z$j = &0}` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_BALL_0] THEN
      SIMP_TAC[NORM_LT_SQUARE; DOT_2; DOT_3; REAL_LT_01] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "ij" (DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC)) THEN
      STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
      REAL_ARITH_TAC;
      DISCH_TAC THEN
      ABBREV_TAC `z:real^3 = if i = 1 then vector[(w:real^2)$1; &0; w$2]
                             else vector[&0; w$1; w$2]` THEN
      SUBGOAL_THEN `(z:real^3)$i = (w:real^2)$1 /\ z$j = &0 /\ z$3 = w$2 /\
                    norm z = norm w`
      STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "z" THEN
        USE_THEN "ij" (DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC)) THEN
        REWRITE_TAC[ARITH_RULE `~(2 = 1)`; VECTOR_3; NORM_EQ; DOT_2; DOT_3] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^3) IN IMAGE (phi:real^2->real^3) n` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_BALL_0]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) = (phi:real^2->real^3) y` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real^2->real^2`; `n:real^2->bool`]
    INVARIANCE_OF_DOMAIN_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi':real^2->real^2` MP_TAC) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. (s = &1 \/ s = -- &1)
        ==> connected {y | y IN n /\ &0 < s * ((phi:real^2->real^3) y)$i} /\
            DISJOINT J {y | y IN n /\ &0 < s * ((phi:real^2->real^3) y)$i}`
  (LABEL_TAC "half") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `{y | y IN n /\ &0 < s * ((phi:real^2->real^3) y)$i} =
        IMAGE (psi':real^2->real^2) (ball(vec 0,&1) INTER {w | &0 < s * w$1})`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_INTER] THEN
        X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
         [STRIP_TAC THEN EXISTS_TAC `(psi:real^2->real^2) y` THEN
          ASM_SIMP_TAC[] THEN
          UNDISCH_TAC `IMAGE (psi:real^2->real^2) n = ball(vec 0,&1)` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
          DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN `(y:real^2) IN n` ASSUME_TAC THENL
           [UNDISCH_TAC `IMAGE (psi':real^2->real^2) (ball(vec 0,&1)) = n` THEN
            DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
            ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `(psi:real^2->real^2) y = w` (fun th -> ASM_MESON_TAC[th]) THEN
          ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `ball(vec 0:real^2,&1)` THEN ASM_REWRITE_TAC[INTER_SUBSET];
        MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[CONVEX_BALL] THEN
        SUBGOAL_THEN `{w:real^2 | &0 < s * w$1} = {w | (s % basis 1) dot w > &0}`
        SUBST1_TAC THENL
         [SIMP_TAC[DOT_LMUL; DOT_BASIS; DIMINDEX_2; ARITH; real_gt];
          REWRITE_TAC[CONVEX_HALFSPACE_GT]]];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `y:real^2` THEN
      ASM_CASES_TAC `(y:real^2) IN n` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(MATCH_MP (ASSUME `!y. y IN n ==> (y IN J <=> ((phi:real^2->real^3) y)$i = &0)`)
        (ASSUME `(y:real^2) IN n`)) THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_CASES_TAC `((phi:real^2->real^3) y)$i = &0` THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n INTER inside J:real^2->bool = {}) /\ ~(n INTER outside J = {})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:real^2->bool`; `inside J:real^2->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    MP_TAC(ISPECL [`n:real^2->bool`; `outside J:real^2->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN CONJ_TAC THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(ASSUME `frontier(inside J:real^2->bool) = J`);
      MP_TAC(ASSUME `frontier(outside J:real^2->bool) = J`)] THEN
    REWRITE_TAC[frontier] THEN UNDISCH_TAC `(x:real^2) IN J` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN n /\ ~(y IN J)
        ==> &0 < &1 * ((phi:real^2->real^3) y)$i \/ &0 < -- &1 * (phi y)$i`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
    MP_TAC(MATCH_MP (ASSUME `!y. y IN n ==> (y IN J <=> ((phi:real^2->real^3) y)$i = &0)`)
      (ASSUME `(y:real^2) IN n`)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. (s = &1 \/ s = -- &1) /\
        ~({y | y IN n /\ &0 < s * ((phi:real^2->real^3) y)$i} INTER inside J = {})
        ==> {y | y IN n /\ &0 < s * ((phi:real^2->real^3) y)$i} SUBSET inside J`
  (LABEL_TAC "inh") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LA1_CONNECTED_INSIDE THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. (s = &1 \/ s = -- &1) /\
        ~({y | y IN n /\ &0 < s * ((phi:real^2->real^3) y)$i} INTER outside J = {})
        ==> {y | y IN n /\ &0 < s * ((phi:real^2->real^3) y)$i} SUBSET outside J`
  (LABEL_TAC "outh") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LC1_CONNECTED_OUTSIDE THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(n INTER inside J:real^2->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:real^2` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~(n INTER outside J:real^2->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y2:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((y1:real^2) IN J) /\ ~((y2:real^2) IN J) /\ ~((y2:real^2) IN inside J)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `J:real^2->bool` INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `J:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `inside J INTER outside J:real^2->bool = {}` THEN
    UNDISCH_TAC `(y1:real^2) IN inside J` THEN UNDISCH_TAC `(y2:real^2) IN outside J` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (ASSUME `!y. y IN n /\ ~(y IN J)
                        ==> &0 < &1 * ((phi:real^2->real^3) y)$i \/
                            &0 < -- &1 * (phi y)$i`)
    (CONJ (ASSUME `(y1:real^2) IN n`) (ASSUME `~((y1:real^2) IN J)`))) THEN
  MP_TAC(MATCH_MP (ASSUME `!y. y IN n /\ ~(y IN J)
                        ==> &0 < &1 * ((phi:real^2->real^3) y)$i \/
                            &0 < -- &1 * (phi y)$i`)
    (CONJ (ASSUME `(y2:real^2) IN n`) (ASSUME `~((y2:real^2) IN J)`))) THEN
  SUBGOAL_THEN
   `!s y. (s = &1 \/ s = -- &1) /\ y IN n /\ &0 < s * ((phi:real^2->real^3) y)$i /\
          y IN inside J
          ==> {y | y IN n /\ &0 < s * ((phi:real^2->real^3) y)$i} SUBSET inside J`
  (LABEL_TAC "inh1") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    USE_THEN "inh" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
    EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y. (s = &1 \/ s = -- &1) /\ y IN n /\ &0 < s * ((phi:real^2->real^3) y)$i /\
          y IN outside J
          ==> {y | y IN n /\ &0 < s * ((phi:real^2->real^3) y)$i} SUBSET outside J`
  (LABEL_TAC "outh1") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    USE_THEN "outh" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
    EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [USE_THEN "inh1" (MP_TAC o SPECL [`&1`; `y1:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `y2:real^2`) THEN
    ASM_REWRITE_TAC[];
    USE_THEN "inh1" (MP_TAC o SPECL [`-- &1`; `y1:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    USE_THEN "outh1" (MP_TAC o SPECL [`&1`; `y2:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    EXISTS_TAC `-- &1` THEN REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `{y | y IN n /\ &0 < -- &1 * ((phi:real^2->real^3) y)$i}
                   SUBSET inside J` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `{y | y IN n /\ &0 < &1 * ((phi:real^2->real^3) y)$i}
                   SUBSET outside J` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    USE_THEN "inh1" (MP_TAC o SPECL [`&1`; `y1:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    USE_THEN "outh1" (MP_TAC o SPECL [`-- &1`; `y2:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `{y | y IN n /\ &0 < &1 * ((phi:real^2->real^3) y)$i}
                   SUBSET inside J` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `{y | y IN n /\ &0 < -- &1 * ((phi:real^2->real^3) y)$i}
                   SUBSET outside J` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    USE_THEN "inh1" (MP_TAC o SPECL [`-- &1`; `y1:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `y2:real^2`) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* B3f. Direction of the axis: for an injective continuous chart map G of   *)
(* the unit ball whose axis lies in k, and a homeomorphism th of k into the *)
(* unit circle, the sign of the cross product of th at two axis points near *)
(* s0 orders them, up to one global sign t (connectedness of the convex set *)
(* of ordered pairs).                                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_LC1_CROSS_BILINEAR = prove
 (`bilinear (\a b:real^2. lift(moi_lc1_cross a b))`,
  REWRITE_TAC[bilinear; linear; moi_lc1_cross; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
  REPEAT STRIP_TAC THEN CONV_TAC REAL_RING);;

let MOI_LC1_CROSS_ANTI = prove
 (`!a b:real^2. moi_lc1_cross b a = --(moi_lc1_cross a b) /\ moi_lc1_cross a a = &0`,
  REWRITE_TAC[moi_lc1_cross] THEN REAL_ARITH_TAC);;

let MOI_LC1_AXIS_DIR = prove
 (`!(G:real^3->real^N) (th:real^N->real^2) k s0.
     G continuous_on ball(vec 0,&1) /\
     (!y z. y IN ball(vec 0,&1) /\ z IN ball(vec 0,&1) /\ G y = G z ==> y = z) /\
     th continuous_on k /\ (!y z. y IN k /\ z IN k /\ th y = th z ==> y = z) /\
     (!y. y IN k ==> norm(th y) = &1) /\
     (!s. abs s < &1 ==> G(vector[&0;&0;s]) IN k) /\
     abs s0 < &1
     ==> ?t r0. (t = &1 \/ t = -- &1) /\ &0 < r0 /\ abs s0 + r0 < &1 /\
                !s s'. abs(s - s0) < r0 /\ abs(s' - s0) < r0
                       ==> (s < s' <=>
                            &0 < t * moi_lc1_cross (th(G(vector[&0;&0;s])))
                                                   (th(G(vector[&0;&0;s']))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `al = \v:real^1. (th:real^N->real^2)((G:real^3->real^N)
                                (vector[&0;&0;drop v]))` THEN
  SUBGOAL_THEN `!s. (al:real^1->real^2)(lift s) =
                    (th:real^N->real^2)((G:real^3->real^N)(vector[&0;&0;s]))`
  ASSUME_TAC THENL [EXPAND_TAC "al" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. abs s < &1 ==> vector[&0;&0;s] IN ball(vec 0:real^3,&1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0; NORM_EQ_SQUARE] THEN
    SIMP_TAC[vector_norm; DOT_3; VECTOR_3] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
    SUBGOAL_THEN `sqrt(s * s) = abs s` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_2; POW_2_SQRT_ABS]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(al:real^1->real^2) continuous_on {v | abs(drop v) < &1}`
  ASSUME_TAC THENL
   [EXPAND_TAC "al" THEN
    SUBGOAL_THEN
     `(\v:real^1. (th:real^N->real^2)((G:real^3->real^N)(vector[&0;&0;drop v]))) =
      ((th:real^N->real^2) o (G:real^3->real^N)) o
      (\v:real^1. vector[&0;&0;drop v]:real^3)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[linear] THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT; DROP_ADD; DROP_CMUL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&1)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM; IMAGE_o] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?r1. &0 < r1 /\
         !s. abs s < &1 /\ abs(s - s0) < r1
             ==> dist((al:real^1->real^2)(lift s),al(lift s0)) < &1 / &2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `(al:real^1->real^2) continuous_on {v | abs(drop v) < &1}`) THEN
    REWRITE_TAC[continuous_on; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `lift s0`) THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN REWRITE_TAC[REAL_HALF; REAL_LT_01] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r1:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1")) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "c1" (MP_TAC o SPEC `lift s`) THEN
    REWRITE_TAC[LIFT_DROP; DIST_LIFT; ASSUME `abs s < &1`; ASSUME `abs(s - s0) < r1`] THEN
    REWRITE_TAC[ASSUME `!s. (al:real^1->real^2)(lift s) =
                            (th:real^N->real^2)((G:real^3->real^N)(vector[&0;&0;s]))`];
    ALL_TAC] THEN
  POP_ASSUM(MP_TAC o REWRITE_RULE[ASSUME `!s. (al:real^1->real^2)(lift s) =
                            (th:real^N->real^2)((G:real^3->real^N)(vector[&0;&0;s]))`]) THEN
  DISCH_TAC THEN
  ABBREV_TAC `r0 = min r1 ((&1 - abs s0) / &2)` THEN
  SUBGOAL_THEN `&0 < r0 /\ r0 <= r1 /\ abs s0 + r0 < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. abs(s - s0) < r0
        ==> abs s < &1 /\ (G:real^3->real^N)(vector[&0;&0;s]) IN k /\
            vector[&0;&0;s] IN ball(vec 0:real^3,&1) /\
            norm((th:real^N->real^2)(G(vector[&0;&0;s]))) = &1 /\
            dist(th(G(vector[&0;&0;s])),th(G(vector[&0;&0;s0]))) < &1 / &2`
  (LABEL_TAC "near") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs s < &1 /\ abs(s - s0) < r1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s s'. abs(s - s0) < r0 /\ abs(s' - s0) < r0 /\ s < s'
           ==> ~(moi_lc1_cross ((th:real^N->real^2)((G:real^3->real^N)(vector[&0;&0;s])))
                               (th(G(vector[&0;&0;s']))) = &0)`
  (LABEL_TAC "nz") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_lc1_cross] THEN DISCH_TAC THEN
    USE_THEN "near" (MP_TAC o C MATCH_MP (ASSUME `abs(s - s0) < r0`)) THEN
    USE_THEN "near" (MP_TAC o C MATCH_MP (ASSUME `abs(s' - s0) < r0`)) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(th:real^N->real^2)((G:real^3->real^N)(vector[&0;&0;s])) =
                  th(G(vector[&0;&0;s']))` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_LC1_UNIT_CROSS THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `dist((th:real^N->real^2)((G:real^3->real^N)(vector[&0;&0;s])),
                        th(G(vector[&0;&0;s0]))) < &1 / &2` THEN
      UNDISCH_TAC `dist((th:real^N->real^2)((G:real^3->real^N)(vector[&0;&0;s'])),
                        th(G(vector[&0;&0;s0]))) < &1 / &2` THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    SUBGOAL_THEN `(G:real^3->real^N)(vector[&0;&0;s]) = G(vector[&0;&0;s'])`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME `!y z. y IN k /\ z IN k /\ (th:real^N->real^2) y = th z
                                ==> y = z`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `vector[&0;&0;s]:real^3 = vector[&0;&0;s']` MP_TAC THENL
     [MATCH_MP_TAC(ASSUME `!y z. y IN ball(vec 0,&1) /\ z IN ball(vec 0,&1) /\
                                (G:real^3->real^N) y = G z ==> y = z`) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. v$3`) THEN REWRITE_TAC[VECTOR_3] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `dl = {w:real^2 | w$1 < s0 + r0} INTER {w | w$1 > s0 - r0} INTER
                   {w | w$2 < s0 + r0} INTER {w | w$2 > s0 - r0} INTER
                   {w | (basis 1 - basis 2) dot w < &0}` THEN
  SUBGOAL_THEN `!w:real^2. w IN dl <=> abs(w$1 - s0) < r0 /\ abs(w$2 - s0) < r0 /\
                                      w$1 < w$2`
  ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN
    SIMP_TAC[IN_INTER; IN_ELIM_THM; DOT_LSUB; DOT_BASIS; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex(dl:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LT; CONVEX_HALFSPACE_COMPONENT_GT;
                CONVEX_HALFSPACE_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\w:real^2. moi_lc1_cross ((th:real^N->real^2)((G:real^3->real^N)(vector[&0;&0;w$1])))
                              (th(G(vector[&0;&0;w$2])))`; `dl:real^2->bool`]
   MOI_LC1_CONNECTED_SIGN) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CONNECTED];
      SUBGOAL_THEN
       `lift o (\w:real^2. moi_lc1_cross ((th:real^N->real^2)((G:real^3->real^N)
                                           (vector[&0;&0;w$1])))
                                         (th(G(vector[&0;&0;w$2])))) =
        (\w. (\a b. lift(moi_lc1_cross a b))
             (((al:real^1->real^2) o (\w:real^2. lift(w$1))) w)
             (((al:real^1->real^2) o (\w:real^2. lift(w$2))) w))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC BILINEAR_CONTINUOUS_ON_COMPOSE THEN
      REWRITE_TAC[MOI_LC1_CROSS_BILINEAR; ETA_AX] THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_LIFT_COMPONENT] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{v:real^1 | abs(drop v) < &1}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; LIFT_DROP] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `abs s0 + r0 < &1` THEN REAL_ARITH_TAC;
      REWRITE_TAC[] THEN X_GEN_TAC `w:real^2` THEN
      DISCH_THEN(MP_TAC o REWRITE_RULE[ASSUME `!w:real^2. w IN dl <=>
          abs(w$1 - s0) < r0 /\ abs(w$2 - s0) < r0 /\ w$1 < w$2`]) THEN
      STRIP_TAC THEN USE_THEN "nz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN (LABEL_TAC "sgn")) THENL
   [EXISTS_TAC `&1` THEN EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
    (MAP_EVERY X_GEN_TAC [`s:real`; `s':real`] THEN STRIP_TAC THEN
     REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG; REAL_NEG_GT0] THEN
     ASM_CASES_TAC `s:real = s'` THENL
      [ASM_REWRITE_TAC[REAL_LT_REFL; CONJUNCT2(SPEC_ALL MOI_LC1_CROSS_ANTI)];
       ALL_TAC] THEN
     ASM_CASES_TAC `s < s':real` THEN ASM_REWRITE_TAC[] THENL
      [USE_THEN "sgn" (MP_TAC o SPEC `vector[s;s']:real^2`) THEN REWRITE_TAC[VECTOR_2] THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
       SUBGOAL_THEN `s' < s:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       USE_THEN "sgn" (MP_TAC o SPEC `vector[s';s]:real^2`) THEN REWRITE_TAC[VECTOR_2] THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       MP_TAC(ISPECL [`(th:real^N->real^2)((G:real^3->real^N)(vector[&0;&0;s']))`;
                      `(th:real^N->real^2)((G:real^3->real^N)(vector[&0;&0;s]))`]
         MOI_LC1_CROSS_ANTI) THEN
       REAL_ARITH_TAC]);
    EXISTS_TAC `-- &1` THEN EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
    (MAP_EVERY X_GEN_TAC [`s:real`; `s':real`] THEN STRIP_TAC THEN
     REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG; REAL_NEG_GT0] THEN
     ASM_CASES_TAC `s:real = s'` THENL
      [ASM_REWRITE_TAC[REAL_LT_REFL; CONJUNCT2(SPEC_ALL MOI_LC1_CROSS_ANTI)];
       ALL_TAC] THEN
     ASM_CASES_TAC `s < s':real` THEN ASM_REWRITE_TAC[] THENL
      [USE_THEN "sgn" (MP_TAC o SPEC `vector[s;s']:real^2`) THEN REWRITE_TAC[VECTOR_2] THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
       SUBGOAL_THEN `s' < s:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       USE_THEN "sgn" (MP_TAC o SPEC `vector[s';s]:real^2`) THEN REWRITE_TAC[VECTOR_2] THEN
       ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       MP_TAC(ISPECL [`(th:real^N->real^2)((G:real^3->real^N)(vector[&0;&0;s']))`;
                      `(th:real^N->real^2)((G:real^3->real^N)(vector[&0;&0;s]))`]
         MOI_LC1_CROSS_ANTI) THEN
       REAL_ARITH_TAC])]);;

(* ------------------------------------------------------------------------- *)
(* B3g. Signed permutations normalizing a crossing chart, and the facts of  *)
(* a crossing chart in the interior used to build normalized charts.        *)
(* ------------------------------------------------------------------------- *)

let moi_lc1_sp = new_definition
 `moi_lc1_sp a b t (z:real^3) = vector[b * z$2; a * z$1; t * z$3]:real^3`;;
let MOI_LC1_SP_COMPONENTS = prove
 (`!a b t z:real^3. (moi_lc1_sp a b t z)$1 = b * z$2 /\
                    (moi_lc1_sp a b t z)$2 = a * z$1 /\
                    (moi_lc1_sp a b t z)$3 = t * z$3`,
  REWRITE_TAC[moi_lc1_sp; VECTOR_3]);;

let MOI_LC1_SP_INV = prove
 (`!a b t z:real^3.
     (a = &1 \/ a = -- &1) /\ (b = &1 \/ b = -- &1) /\ (t = &1 \/ t = -- &1)
     ==> moi_lc1_sp b a t (moi_lc1_sp a b t z) = z /\
         moi_lc1_sp a b t (moi_lc1_sp b a t z) = z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MOI_LC1_SP_COMPONENTS] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_LC1_SP_LINEAR = prove
 (`!a b t. linear(moi_lc1_sp a b t)`,
  REWRITE_TAC[linear] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MOI_LC1_SP_COMPONENTS;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_LC1_SP_NORM = prove
 (`!a b t z:real^3.
     (a = &1 \/ a = -- &1) /\ (b = &1 \/ b = -- &1) /\ (t = &1 \/ t = -- &1)
     ==> norm(moi_lc1_sp a b t z) = norm z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[vector_norm; DOT_3; MOI_LC1_SP_COMPONENTS] THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_LC1_SP_BALL = prove
 (`!a b t.
     (a = &1 \/ a = -- &1) /\ (b = &1 \/ b = -- &1) /\ (t = &1 \/ t = -- &1)
     ==> IMAGE (moi_lc1_sp a b t) (ball(vec 0,&1)) = ball(vec 0,&1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `w:real^3` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[MOI_LC1_SP_NORM];
    DISCH_TAC THEN EXISTS_TAC `moi_lc1_sp b a t w` THEN
    ASM_SIMP_TAC[MOI_LC1_SP_INV; MOI_LC1_SP_NORM] THEN
    MP_TAC(ISPECL [`b:real`; `a:real`; `t:real`; `w:real^3`] MOI_LC1_SP_NORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_LC1_PL_MAP_ON_LINEAR = prove
 (`!(l:real^M->real^N) s. locally_polyhedral s /\ linear l ==> pl_map_on s l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `l = (\x. (l:real^M->real^N) x + vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_RID];
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[]]);;

let MOI_LC1_SP_PL_HOMEO = prove
 (`!a b t.
     (a = &1 \/ a = -- &1) /\ (b = &1 \/ b = -- &1) /\ (t = &1 \/ t = -- &1)
     ==> pl_homeomorphism (ball(vec 0:real^3,&1),ball(vec 0,&1))
                          (moi_lc1_sp a b t,moi_lc1_sp b a t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(b = &1 \/ b = -- &1) /\ (a = &1 \/ a = -- &1) /\ (t = &1 \/ t = -- &1)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
  ASM_SIMP_TAC[MOI_LC1_SP_BALL; MOI_LC1_SP_INV; LINEAR_CONTINUOUS_ON; MOI_LC1_SP_LINEAR;
               MOI_LC1_PL_MAP_ON_LINEAR; LOCALLY_POLYHEDRAL_OPEN; OPEN_BALL]);;
let MOI_LC1_OPEN_IN_INTERIOR = prove
 (`!s n:real^N->bool.
     open_in (subtopology euclidean s) n /\ n SUBSET interior s ==> open n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  SUBGOAL_THEN `n = interior s INTER (t:real^N->bool)` SUBST1_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR]]);;

let MOI_LC1_SHEET_INJ = prove
 (`!c (f:real^2->real^N) u (h:real^N->real^3) h' na nb.
     moi_lt_singular_disk c f /\
     (!y. y IN u ==> h'(h y) = y) /\
     DISJOINT na nb /\ na SUBSET std_triangle /\ nb SUBSET std_triangle /\
     (!y. y IN na ==> f y IN u) /\ (!y. y IN nb ==> f y IN u) /\
     (!y. y IN moi_lt_double_image f INTER u ==> h y IN IMAGE (h o f) nb)
     ==> !y z. y IN na /\ z IN na /\ (h o f) y = (h o f) z ==> y = z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`y:real^2`; `z:real^2`] THEN REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^2) IN std_triangle /\ (f:real^2->real^N) y IN u /\
                (z:real^2) IN std_triangle /\ f z IN u`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) y = f z` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP (ASSUME `!y. y IN u ==> (h':real^3->real^N)((h:real^N->real^3) y) = y`)
      (ASSUME `(f:real^2->real^N) z IN u`)) THEN
    MP_TAC(MATCH_MP (ASSUME `!y. y IN u ==> (h':real^3->real^N)((h:real^N->real^3) y) = y`)
      (ASSUME `(f:real^2->real^N) y IN u`)) THEN
    REWRITE_TAC[ASSUME `(h:real^N->real^3)((f:real^2->real^N) y) = h(f z)`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:real^2->real^N) y IN moi_lt_double_image f` ASSUME_TAC THENL
   [REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`y:real^2`; `z:real^2`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^2. w IN nb /\ (h:real^N->real^3)((f:real^2->real^N) w) = h(f y)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^N->real^3)((f:real^2->real^N) y) IN IMAGE (h o f) nb` MP_TAC
    THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[IN_IMAGE; o_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^2) IN std_triangle /\ (f:real^2->real^N) w IN u` STRIP_ASSUME_TAC
  THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) w = f y` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP (ASSUME `!y. y IN u ==> (h':real^3->real^N)((h:real^N->real^3) y) = y`)
      (ASSUME `(f:real^2->real^N) w IN u`)) THEN
    MP_TAC(MATCH_MP (ASSUME `!y. y IN u ==> (h':real^3->real^N)((h:real^N->real^3) y) = y`)
      (ASSUME `(f:real^2->real^N) y IN u`)) THEN
    REWRITE_TAC[ASSUME `(h:real^N->real^3)((f:real^2->real^N) w) = h(f y)`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `y:real^2`]
    MOI_LCC_FIBER_TWO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fib"))))) THEN
  SUBGOAL_THEN `(z:real^2) = v` ASSUME_TAC THENL
   [USE_THEN "fib" (MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^2) = v` ASSUME_TAC THENL
   [USE_THEN "fib" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(w:real^2) IN std_triangle`)
      (TRANS (ASSUME `(f:real^2->real^N) w = f y`) (ASSUME `(f:real^2->real^N) y = f z`)))) THEN
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (na:real^2->bool) nb` THEN UNDISCH_TAC `(y:real^2) IN na` THEN
    UNDISCH_TAC `(w:real^2) IN nb` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (na:real^2->bool) nb` THEN UNDISCH_TAC `(z:real^2) IN na` THEN
  UNDISCH_TAC `(w:real^2) IN nb` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_LC1_SHEET_J = prove
 (`!(f:real^2->real^N) k J u (h:real^N->real^3) h' na i.
     J = {x | x IN std_triangle /\ f x IN k} /\
     (!y. y IN u ==> h'(h y) = y) /\
     moi_lt_double_image f INTER u SUBSET k /\ k SUBSET moi_lt_double_image f /\
     na SUBSET std_triangle /\ (!y. y IN na ==> f y IN u) /\
     (!y. y IN na ==> ((h o f) y IN IMAGE h (moi_lt_double_image f INTER u) <=>
                       ((h o f) y)$i = &0))
     ==> !y. y IN na ==> (y IN J <=> ((h o f) y)$i = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP th
    (ASSUME `(y:real^2) IN na`))]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
  SUBGOAL_THEN `(y:real^2) IN std_triangle /\ (f:real^2->real^N) y IN u`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(f:real^2->real^N) y = d` (fun th -> ASM SET_TAC[th]) THEN
    ASM_MESON_TAC[]]);;

let MOI_LC1_CHART_FACTS = prove
 (`!c (f:real^2->real^N) k J u (h:real^N->real^3) h' n1 n2 x.
     moi_lt_singular_disk c f /\ k IN components (moi_lt_double_image f) /\
     J = {x | x IN std_triangle /\ f x IN k} /\
     open_in (subtopology euclidean (UNIONS c)) u /\
     pl_homeomorphism (u,IMAGE h u) (h,h') /\
     u INTER complex_boundary c = {} /\ IMAGE h u = ball(vec 0,&1) /\
     {x | x IN std_triangle /\ f x IN u} = n1 UNION n2 /\ DISJOINT n1 n2 /\
     IMAGE (h o f) n1 = IMAGE h u INTER {z:real^3 | z$1 = &0} /\
     IMAGE (h o f) n2 = IMAGE h u INTER {z:real^3 | z$2 = &0} /\
     IMAGE h (moi_lt_double_image f INTER u) =
     IMAGE h u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0} /\
     open_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n1 /\
     open_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n2 /\
     x IN J /\ f x IN u
     ==> open n1 /\ open n2 /\ n1 SUBSET std_triangle /\ n2 SUBSET std_triangle /\
         (h o f) continuous_on (n1 UNION n2) /\
         (!y z. y IN n1 /\ z IN n1 /\ (h o f) y = (h o f) z ==> y = z) /\
         (!y z. y IN n2 /\ z IN n2 /\ (h o f) y = (h o f) z ==> y = z) /\
         (!y. y IN n1 ==> (y IN J <=> ((h o f) y)$2 = &0)) /\
         (!y. y IN n2 ==> (y IN J <=> ((h o f) y)$1 = &0)) /\
         (!s. abs s < &1 ==> h'(vector[&0;&0;s]) IN k) /\
         moi_lt_double_image f INTER u SUBSET k`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN
   `(!y. y IN u ==> (h':real^3->real^N)((h:real^N->real^3) y) = y) /\
    h continuous_on u /\
    (!z. z IN ball(vec 0,&1) ==> h(h' z) = z) /\
    IMAGE h' (ball(vec 0,&1)) = u /\ h' continuous_on ball(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (u,IMAGE (h:real^N->real^3) u) (h,h')` THEN
    ASM_REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) continuous_on std_triangle /\
                IMAGE f std_triangle SUBSET UNIONS c /\
                {x | x IN std_triangle /\ f x IN complex_boundary c} =
                relative_frontier std_triangle`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_singular_disk; PL_MAP_ON_IMP_CONTINUOUS_ON]; ALL_TAC] THEN
  ABBREV_TAC `Q = {x | x IN std_triangle /\ (f:real^2->real^N) x IN u}` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean std_triangle) (Q:real^2->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `UNIONS c:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q:real^2->bool) SUBSET interior std_triangle` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_LC1_OPEN_TRIANGLE] THEN EXPAND_TAC "Q" THEN
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN complex_boundary c} =
                 relative_frontier std_triangle` THEN
    UNDISCH_TAC `u INTER complex_boundary c = ({}:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `n1 SUBSET (Q:real^2->bool) /\ n2 SUBSET Q` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `Q = (n1:real^2->bool) UNION n2` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open(n1:real^2->bool) /\ open(n2:real^2->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LC1_OPEN_IN_INTERIOR THEN
    EXISTS_TAC `std_triangle` THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `Q:real^2->bool` THEN
       ASM_REWRITE_TAC[];
       ASM SET_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q:real^2->bool) SUBSET std_triangle` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. y IN Q ==> y IN std_triangle /\ (f:real^2->real^N) y IN u`
  ASSUME_TAC THENL [EXPAND_TAC "Q" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `((h:real^N->real^3) o (f:real^2->real^N)) continuous_on (n1 UNION n2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `Q = (n1:real^2->bool) UNION n2` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `!y:real^2. y IN Q ==> y IN std_triangle /\ (f:real^2->real^N) y IN u` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. abs s < &1 ==> vector[&0;&0;s] IN ball(vec 0:real^3,&1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN
    SIMP_TAC[vector_norm; DOT_3; VECTOR_3] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
    SUBGOAL_THEN `sqrt(s * s) = abs s` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_2; POW_2_SQRT_ABS]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) x IN k /\ x IN std_triangle` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN J` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET moi_lt_double_image f` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_lt_double_image (f:real^2->real^N) INTER u =
                IMAGE (h':real^3->real^N)
                      (ball(vec 0,&1) INTER {z:real^3 | z$1 = &0 /\ z$2 = &0})`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (h:real^N->real^3) (moi_lt_double_image f INTER u) =
                 IMAGE h u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0}` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `!y. y IN u ==> (h':real^3->real^N)((h:real^N->real^3) y) = y` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_lt_double_image f INTER u SUBSET (k:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `moi_lt_double_image (f:real^2->real^N)` THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&1)` THEN
        ASM_REWRITE_TAC[INTER_SUBSET];
        MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[CONVEX_BALL] THEN
        REWRITE_TAC[SET_RULE `{z:real^3 | P z /\ Q z} = {z | P z} INTER {z | Q z}`] THEN
        MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`basis 1:real^3`; `&0`] CONVEX_HYPERPLANE);
          MP_TAC(ISPECL [`basis 2:real^3`; `&0`] CONVEX_HYPERPLANE)] THEN
        SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]];
      UNDISCH_TAC `moi_lt_double_image (f:real^2->real^N) INTER u =
                   IMAGE (h':real^3->real^N)
                         (ball(vec 0,&1) INTER {z:real^3 | z$1 = &0 /\ z$2 = &0})` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(f:real^2->real^N) x` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. abs s < &1 ==> (h':real^3->real^N)(vector[&0;&0;s]) IN k`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h':real^3->real^N)(vector[&0;&0;s]) IN
                  moi_lt_double_image (f:real^2->real^N) INTER u` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_SIMP_TAC[IN_INTER; IN_ELIM_THM; VECTOR_3];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!y:real^2. y IN n1 ==> (f:real^2->real^N) y IN u) /\
                (!y:real^2. y IN n2 ==> (f:real^2->real^N) y IN u) /\
                n1 SUBSET std_triangle /\ n2 SUBSET std_triangle`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `!y:real^2. y IN Q ==> y IN std_triangle /\ (f:real^2->real^N) y IN u` THEN
    UNDISCH_TAC `n1 SUBSET (Q:real^2->bool)` THEN UNDISCH_TAC `n2 SUBSET (Q:real^2->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y:real^2. y IN n1 ==> ((h:real^N->real^3) o (f:real^2->real^N)) y IN
                            ball(vec 0,&1) INTER {z | z$1 = &0}) /\
    (!y:real^2. y IN n2 ==> ((h:real^N->real^3) o (f:real^2->real^N)) y IN
                            ball(vec 0,&1) INTER {z | z$2 = &0}) /\
    IMAGE (h:real^N->real^3) (moi_lt_double_image f INTER u) =
    ball(vec 0,&1) INTER {z:real^3 | z$1 = &0 /\ z$2 = &0} /\
    IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n1 = ball(vec 0,&1) INTER {z | z$1 = &0} /\
    IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n2 = ball(vec 0,&1) INTER {z | z$2 = &0}`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n1 =
                 IMAGE h u INTER {z:real^3 | z$1 = &0}` THEN
    UNDISCH_TAC `IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n2 =
                 IMAGE h u INTER {z:real^3 | z$2 = &0}` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^N. y IN moi_lt_double_image f INTER u
               ==> (h:real^N->real^3) y IN IMAGE (h o (f:real^2->real^N)) n1 /\
                   h y IN IMAGE (h o f) n2`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^N->real^3) y IN
                  ball(vec 0,&1) INTER {z:real^3 | z$1 = &0 /\ z$2 = &0}` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (h:real^N->real^3) (moi_lt_double_image f INTER u) =
                   ball(vec 0,&1) INTER {z:real^3 | z$1 = &0 /\ z$2 = &0}` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_INTER; IN_ELIM_THM]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `n1:real^2->bool`;
                 `n2:real^2->bool`] MOI_LC1_SHEET_INJ) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `n2:real^2->bool`;
                 `n1:real^2->bool`] MOI_LC1_SHEET_INJ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `k:real^N->bool`; `J:real^2->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `n1:real^2->bool`; `2`] MOI_LC1_SHEET_J) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `!y:real^2. y IN n1 ==> ((h:real^N->real^3) o (f:real^2->real^N)) y IN
                            ball(vec 0,&1) INTER {z | z$1 = &0}` THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[IN_INTER; IN_ELIM_THM];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `k:real^N->bool`; `J:real^2->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `n2:real^2->bool`; `1`] MOI_LC1_SHEET_J) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `!y:real^2. y IN n2 ==> ((h:real^N->real^3) o (f:real^2->real^N)) y IN
                            ball(vec 0,&1) INTER {z | z$2 = &0}` THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* B3h. Normalized charts from interior crossing2 charts.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_LC1_SHEET_GERM = prove
 (`!(f:real^2->real^N) (h:real^N->real^3) h' u na nb xa xb e rho d0 q i.
     (!y. y IN u ==> h'(h y) = y) /\ (!z. z IN ball(vec 0,&1) ==> h(h' z) = z) /\
     (!y. y IN na ==> f y IN u) /\ na SUBSET std_triangle /\ DISJOINT na nb /\
     IMAGE (h o f) na = ball(vec 0,&1) INTER {z | z$i = &0} /\
     (!y. y IN std_triangle /\ dist(f y,f xa) < d0
          ==> dist(xa,y) < e \/ dist(xb,y) < e) /\
     (!y. y IN std_triangle /\ dist(xa,y) < e ==> y IN na) /\
     (!y. y IN std_triangle /\ dist(xb,y) < e ==> y IN nb) /\
     e <= rho /\ &2 * rho <= dist(xa,xb) /\
     q IN ball(vec 0,&1) /\ dist(h' q,f xa) < d0
     ==> (q$i = &0 ==> ?y. y IN na /\ dist(xa,y) < e /\ f y = h' q /\ (h o f) y = q) /\
         (!y. y IN std_triangle /\ dist(xa,y) < rho /\ f y = h' q
              ==> y IN na /\ (h o f) y = q /\ q$i = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(q:real^3) IN IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) na`
    MP_TAC THENL [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `y:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
    SUBGOAL_THEN `(h:real^N->real^3)((f:real^2->real^N) y) = q` ASSUME_TAC THENL
     [ASM_MESON_TAC[o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^2->real^N) y = h' (q:real^3)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^2) IN std_triangle` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `dist(xa:real^2,y) < e \/ dist(xb,y) < e` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `d0:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^2) IN nb` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `nb:real^2->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `dist(xa:real^2,y) < e` ASSUME_TAC THENL
   [SUBGOAL_THEN `dist(xa:real^2,y) < e \/ dist(xb,y) < e` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `d0:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
      UNDISCH_TAC `dist(xa:real^2,y) < rho` THEN UNDISCH_TAC `e <= rho` THEN
      UNDISCH_TAC `&2 * rho <= dist(xa:real^2,xb)` THEN CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^2) IN na` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `na:real^2->bool`)) (concl th) &&
      not (can (find_term (fun t -> t = `u:real^N->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((h:real^N->real^3) o (f:real^2->real^N)) y = q` ASSUME_TAC THENL
   [REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(q:real^3) IN IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) na` MP_TAC
  THENL
   [UNDISCH_TAC `((h:real^N->real^3) o (f:real^2->real^N)) y = q` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_INTER; IN_ELIM_THM]]);;
let MOI_LC1_NCHART_FROM_CHART = prove
 (`!c (f:real^2->real^N) k J th u (h:real^N->real^3) h' n1 n2 x x' rho.
     moi_lt_singular_disk c f /\ k IN components (moi_lt_double_image f) /\
     J = {x | x IN std_triangle /\ f x IN k} /\
     (?gam:real^1->real^2. simple_path gam /\ pathfinish gam = pathstart gam /\
                           path_image gam = J) /\
     th continuous_on k /\ (!y z. y IN k /\ z IN k /\ th y = th z ==> y = z) /\
     (!y. y IN k ==> norm(th y) = &1) /\
     open_in (subtopology euclidean (UNIONS c)) u /\
     pl_homeomorphism (u,IMAGE h u) (h,h') /\
     u INTER complex_boundary c = {} /\ IMAGE h u = ball(vec 0,&1) /\
     {x | x IN std_triangle /\ f x IN u} = n1 UNION n2 /\ DISJOINT n1 n2 /\
     IMAGE (h o f) n1 = IMAGE h u INTER {z:real^3 | z$1 = &0} /\
     IMAGE (h o f) n2 = IMAGE h u INTER {z:real^3 | z$2 = &0} /\
     IMAGE h (moi_lt_double_image f INTER u) =
     IMAGE h u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0} /\
     open_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n1 /\
     open_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n2 /\
     x IN J /\ x IN n1 /\ x' IN n2 /\ f x' = f x /\
     (!z. z IN std_triangle /\ f z = f x ==> z = x \/ z = x') /\
     &0 < rho /\ &2 * rho <= dist(x,x')
     ==> ?g p r. moi_lc1_nchart c f J th rho x x' g p r`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `(f:real^2->real^N) x IN u` ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN u} = n1 UNION n2` THEN
    UNDISCH_TAC `(x:real^2) IN n1` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `J:real^2->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                 `h':real^3->real^N`; `n1:real^2->bool`; `n2:real^2->bool`; `x:real^2`]
    MOI_LC1_CHART_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `(!y. y IN u ==> (h':real^3->real^N)((h:real^N->real^3) y) = y) /\
    h continuous_on u /\
    (!z. z IN ball(vec 0,&1) ==> h(h' z) = z) /\
    IMAGE h' (ball(vec 0,&1)) = u /\ h' continuous_on ball(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (u,IMAGE (h:real^N->real^3) u) (h,h')` THEN
    ASM_REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) continuous_on std_triangle /\
                (x:real^2) IN std_triangle /\ (x':real^2) IN std_triangle /\
                (x':real^2) IN J /\ inside J SUBSET std_triangle`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[moi_lt_singular_disk; PL_MAP_ON_IMP_CONTINUOUS_ON]; ALL_TAC] THEN
    SUBGOAL_THEN `(J:real^2->bool) SUBSET std_triangle` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[];
      UNDISCH_TAC `(x:real^2) IN J` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MP_TAC(ISPEC `J:real^2->bool` MOI_LA1_INSIDE_TRIANGLE) THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `J = {x | x IN std_triangle /\ (f:real^2->real^N) x IN k}` THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n1 =
                ball(vec 0,&1) INTER {z | z$1 = &0} /\
                IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n2 =
                ball(vec 0,&1) INTER {z | z$2 = &0} /\
                (h o f) continuous_on n1 /\ (h o f) continuous_on n2`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `n1 UNION n2:real^2->bool` THEN ASM_REWRITE_TAC[SUBSET_UNION];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`J:real^2->bool`; `n1:real^2->bool`;
                 `(h:real^N->real^3) o (f:real^2->real^N)`; `2`; `1`; `x:real^2`]
    MOI_LC1_SHEET_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH];
    DISCH_THEN(X_CHOOSE_THEN `a:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sa")))] THEN
  MP_TAC(ISPECL [`J:real^2->bool`; `n2:real^2->bool`;
                 `(h:real^N->real^3) o (f:real^2->real^N)`; `1`; `2`; `x':real^2`]
    MOI_LC1_SHEET_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH];
    DISCH_THEN(X_CHOOSE_THEN `b:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sb")))] THEN
  SUBGOAL_THEN `(h:real^N->real^3)((f:real^2->real^N) x) IN ball(vec 0,&1)` ASSUME_TAC
  THENL
   [UNDISCH_TAC `IMAGE (h:real^N->real^3) u = ball(vec 0,&1)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  ABBREV_TAC `s0 = ((h:real^N->real^3)((f:real^2->real^N) x))$3` THEN
  MP_TAC(ISPECL [`h':real^3->real^N`; `th:real^N->real^2`; `k:real^N->bool`; `s0:real`]
    MOI_LC1_AXIS_DIR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MESON_TAC[ASSUME `!z. z IN ball(vec 0,&1)
                          ==> (h:real^N->real^3)((h':real^3->real^N) z) = z`];
      EXPAND_TAC "s0" THEN
      MP_TAC(ISPECL [`(h:real^N->real^3)((f:real^2->real^N) x)`; `3`] COMPONENT_LE_NORM) THEN
      UNDISCH_TAC `(h:real^N->real^3)((f:real^2->real^N) x) IN ball(vec 0,&1)` THEN
      REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `r0:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ax"))))))] THEN
  SUBGOAL_THEN `a * a = &1 /\ b * b = &1 /\ t * t = &1 /\ ~(a = &0) /\ ~(b = &0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`a = &1 \/ a = -- &1`; `b = &1 \/ b = -- &1`;
                           `t = &1 \/ t = -- &1`] THEN
    REPEAT(DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC)) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = moi_lc1_sp a b t` THEN ABBREV_TAC `L' = moi_lc1_sp b a t` THEN
  SUBGOAL_THEN
   `(!z. (L':real^3->real^3)((L:real^3->real^3) z) = z) /\ (!z. L(L' z) = z) /\
    (!z. norm(L z) = norm z) /\ (!z. norm(L' z) = norm z) /\
    (!z:real^3. (L z)$1 = b * z$2 /\ (L z)$2 = a * z$1 /\ (L z)$3 = t * z$3) /\
    (!z:real^3. (L' z)$1 = a * z$2 /\ (L' z)$2 = b * z$1 /\ (L' z)$3 = t * z$3) /\
    pl_homeomorphism (ball(vec 0,&1),ball(vec 0,&1)) (L,L') /\
    (!z. z IN ball(vec 0,&1) ==> L z IN ball(vec 0,&1))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "L'"] THEN
    ASM_SIMP_TAC[MOI_LC1_SP_INV; MOI_LC1_SP_NORM; MOI_LC1_SP_COMPONENTS;
                 MOI_LC1_SP_PL_HOMEO; IN_BALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `((h:real^N->real^3)((f:real^2->real^N) x))$1 = &0 /\ (h(f x))$2 = &0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `((h:real^N->real^3) o (f:real^2->real^N)) x IN
                    ball(vec 0,&1) INTER {z | z$1 = &0}` MP_TAC THENL
       [UNDISCH_TAC `IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) n1 =
                     ball(vec 0,&1) INTER {z | z$1 = &0}` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
        SIMP_TAC[IN_INTER; IN_ELIM_THM; o_THM]];
      MP_TAC(MATCH_MP (ASSUME `!y. y IN n1 ==> (y IN J <=>
               (((h:real^N->real^3) o (f:real^2->real^N)) y)$2 = &0)`)
        (ASSUME `(x:real^2) IN n1`)) THEN
      ASM_REWRITE_TAC[o_THM]];
    ALL_TAC] THEN
  ABBREV_TAC `p = (L':real^3->real^3)((h:real^N->real^3)((f:real^2->real^N) x))` THEN
  SUBGOAL_THEN `(p:real^3)$1 = &0 /\ p$2 = &0 /\ p$3 = t * s0 /\
                (L:real^3->real^3) p = (h:real^N->real^3)((f:real^2->real^N) x) /\
                norm p < &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
    UNDISCH_TAC `(h:real^N->real^3)((f:real^2->real^N) x) IN ball(vec 0,&1)` THEN
    REWRITE_TAC[IN_BALL_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `g = (h':real^3->real^N) o (L:real^3->real^3)` THEN
  SUBGOAL_THEN `pl_homeomorphism (ball(vec 0,&1),u)
                  (g,(L':real^3->real^3) o (h:real^N->real^3))`
  ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `ball(vec 0:real^3,&1)` THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
      UNDISCH_TAC `pl_homeomorphism (u,IMAGE (h:real^N->real^3) u) (h,h')` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^N) (ball(vec 0,&1)) = u /\
                g continuous_on ball(vec 0,&1) /\ (g:real^3->real^N) p = f(x:real^2) /\
                (!z. g z = (h':real^3->real^N)((L:real^3->real^3) z))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[o_THM] THEN
    REWRITE_TAC[ASSUME `(L:real^3->real^3) p = (h:real^N->real^3)((f:real^2->real^N) x)`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e1. &0 < e1 /\ !y. dist(x:real^2,y) < e1 ==> y IN n1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(n1:real^2->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e2. &0 < e2 /\ !y. dist(x':real^2,y) < e2 ==> y IN n2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(n2:real^2->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x':real^2`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `e = min (min rho e1) e2` THEN
  SUBGOAL_THEN `&0 < e /\ e <= rho /\ e <= e1 /\ e <= e2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `x:real^2`; `x':real^2`; `e:real`]
    MOI_LC1_LOCAL_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lp"))) THEN
  SUBGOAL_THEN
   `(!y. y IN std_triangle /\ dist((f:real^2->real^N) y,f x') < d0
         ==> dist(x':real^2,y) < e \/ dist(x,y) < e) /\
    (!y. y IN std_triangle /\ dist(x:real^2,y) < e ==> y IN n1) /\
    (!y. y IN std_triangle /\ dist(x':real^2,y) < e ==> y IN n2) /\
    (!y:real^2. y IN n1 ==> (f:real^2->real^N) y IN u) /\
    (!y:real^2. y IN n2 ==> (f:real^2->real^N) y IN u)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
      USE_THEN "lp" (MP_TAC o SPEC `y:real^2`) THEN
      REWRITE_TAC[ASSUME `(y:real^2) IN std_triangle`] THEN
      UNDISCH_TAC `dist((f:real^2->real^N) y,f x') < d0` THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `e1:real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `e2:real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN u} = n1 UNION n2` THEN
      SET_TAC[];
      UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN u} = n1 UNION n2` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?r1. &0 < r1 /\ !z. z IN ball(vec 0,&1) /\ dist(z,p) < r1
                        ==> dist((g:real^3->real^N) z,f(x:real^2)) < d0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `(g:real^3->real^N) continuous_on ball(vec 0,&1)`) THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN
    ASM_REWRITE_TAC[IN_BALL_0] THEN DISCH_THEN(MP_TAC o SPEC `d0:real`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r = min (min r1 r0) (&1 - norm(p:real^3))` THEN
  SUBGOAL_THEN `&0 < r /\ r <= r1 /\ r <= r0 /\ r <= &1 - norm(p:real^3)`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ball(p:real^3,r) SUBSET ball(vec 0,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; IN_BALL_0] THEN X_GEN_TAC `z:real^3` THEN
    UNDISCH_TAC `r <= &1 - norm(p:real^3)` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`g:real^3->real^N`; `p:real^3`; `r:real`] THEN
  REWRITE_TAC[moi_lc1_nchart] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `(L':real^3->real^3) o (h:real^N->real^3)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(z:real^3) IN ball(vec 0,&1) /\ (L:real^3->real^3) z IN ball(vec 0,&1) /\
    dist((h':real^3->real^N)(L z),f(x:real^2)) < d0 /\
    dist((h':real^3->real^N)(L z),f(x':real^2)) < d0 /\
    abs(z$3 - (p:real^3)$3) < r0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(z:real^3) IN ball(vec 0,&1)` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(p:real^3,r) SUBSET ball(vec 0,&1)` THEN
      UNDISCH_TAC `(z:real^3) IN ball(p,r)` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `dist(z:real^3,p) < r` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(p,r)` THEN REWRITE_TAC[IN_BALL] THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    SUBGOAL_THEN `dist((g:real^3->real^N) z,f(x:real^2)) < d0` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `r1:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`z - p:real^3`; `3`] COMPONENT_LE_NORM) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
    UNDISCH_TAC `dist(z:real^3,p) < r` THEN UNDISCH_TAC `r <= r0` THEN
    REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `u:real^N->bool`; `n1:real^2->bool`; `n2:real^2->bool`; `x:real^2`;
                 `x':real^2`; `e:real`; `rho:real`; `d0:real`; `(L:real^3->real^3) z`; `1`]
    MOI_LC1_SHEET_GERM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g1a") (LABEL_TAC "g1b"))] THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `u:real^N->bool`; `n2:real^2->bool`; `n1:real^2->bool`; `x':real^2`;
                 `x:real^2`; `e:real`; `rho:real`; `d0:real`; `(L:real^3->real^3) z`; `2`]
    MOI_LC1_SHEET_GERM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g2a") (LABEL_TAC "g2b"))] THEN
  SUBGOAL_THEN `((L:real^3->real^3) z)$1 = b * z$2 /\ (L z)$2 = a * z$1 /\
                (L z)$3 = t * z$3`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. y IN inside J ==> y IN std_triangle /\ ~(y IN J) /\
                           ~(y IN outside J)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `J:real^2->bool` INSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `J:real^2->bool` INSIDE_OUTSIDE) THEN
    UNDISCH_TAC `inside J SUBSET std_triangle` THEN
    UNDISCH_TAC `(y:real^2) IN inside J` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_INTER; IN_BALL] THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `((L:real^3->real^3) z)$1 = &0` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_MUL_RZERO]; ALL_TAC] THEN
      USE_THEN "g1a" (MP_TAC o C MATCH_MP (ASSUME `((L:real^3->real^3) z)$1 = &0`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `n1 SUBSET std_triangle` THEN UNDISCH_TAC `(y:real^2) IN n1` THEN
        SET_TAC[];
        UNDISCH_TAC `dist(x:real^2,y) < e` THEN UNDISCH_TAC `e <= rho` THEN
        REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      USE_THEN "g1b" (MP_TAC o SPEC `y:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      UNDISCH_TAC `((L:real^3->real^3) z)$1 = &0` THEN ASM_REWRITE_TAC[REAL_ENTIRE]];
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_BALL] THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `((L:real^3->real^3) z)$2 = &0` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_MUL_RZERO]; ALL_TAC] THEN
      USE_THEN "g2a" (MP_TAC o C MATCH_MP (ASSUME `((L:real^3->real^3) z)$2 = &0`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `n2 SUBSET std_triangle` THEN UNDISCH_TAC `(y:real^2) IN n2` THEN
        SET_TAC[];
        UNDISCH_TAC `dist(x':real^2,y) < e` THEN UNDISCH_TAC `e <= rho` THEN
        REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      USE_THEN "g2b" (MP_TAC o SPEC `y:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      UNDISCH_TAC `((L:real^3->real^3) z)$2 = &0` THEN ASM_REWRITE_TAC[REAL_ENTIRE]];
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_BALL] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `((L:real^3->real^3) z)$1 = &0` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_MUL_RZERO]; ALL_TAC] THEN
      USE_THEN "g1a" (MP_TAC o C MATCH_MP (ASSUME `((L:real^3->real^3) z)$1 = &0`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "sa" (MP_TAC o C MATCH_MP (ASSUME `(y:real^2) IN n1`)) THEN
        ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID] THEN SIMP_TAC[];
        UNDISCH_TAC `dist(x:real^2,y) < e` THEN UNDISCH_TAC `e <= rho` THEN
        REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^2) IN std_triangle /\ ~(y IN J) /\ ~(y IN outside J)`
      STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC(ASSUME `!y:real^2. y IN inside J
                               ==> y IN std_triangle /\ ~(y IN J) /\ ~(y IN outside J)`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "g1b" (MP_TAC o SPEC `y:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `((L:real^3->real^3) z)$1 = &0` THEN ASM_REWRITE_TAC[REAL_ENTIRE];
        ALL_TAC] THEN
      MP_TAC(MATCH_MP (ASSUME `!y. y IN n1 ==> (y IN J <=>
               (((h:real^N->real^3) o (f:real^2->real^N)) y)$2 = &0)`)
        (ASSUME `(y:real^2) IN n1`)) THEN
      USE_THEN "sa" (MP_TAC o C MATCH_MP (ASSUME `(y:real^2) IN n1`)) THEN
      ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID; REAL_ENTIRE] THEN REAL_ARITH_TAC];
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_BALL] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `((L:real^3->real^3) z)$2 = &0` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_MUL_RZERO]; ALL_TAC] THEN
      USE_THEN "g2a" (MP_TAC o C MATCH_MP (ASSUME `((L:real^3->real^3) z)$2 = &0`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "sb" (MP_TAC o C MATCH_MP (ASSUME `(y:real^2) IN n2`)) THEN
        ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID] THEN SIMP_TAC[];
        UNDISCH_TAC `dist(x':real^2,y) < e` THEN UNDISCH_TAC `e <= rho` THEN
        REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^2) IN std_triangle /\ ~(y IN J) /\ ~(y IN outside J)`
      STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC(ASSUME `!y:real^2. y IN inside J
                               ==> y IN std_triangle /\ ~(y IN J) /\ ~(y IN outside J)`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "g2b" (MP_TAC o SPEC `y:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `((L:real^3->real^3) z)$2 = &0` THEN ASM_REWRITE_TAC[REAL_ENTIRE];
        ALL_TAC] THEN
      MP_TAC(MATCH_MP (ASSUME `!y. y IN n2 ==> (y IN J <=>
               (((h:real^N->real^3) o (f:real^2->real^N)) y)$1 = &0)`)
        (ASSUME `(y:real^2) IN n2`)) THEN
      USE_THEN "sb" (MP_TAC o C MATCH_MP (ASSUME `(y:real^2) IN n2`)) THEN
      ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID; REAL_ENTIRE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `z':real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs((z':real^3)$3 - (p:real^3)$3) < r0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`z' - p:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
    UNDISCH_TAC `(z':real^3) IN ball(p,r)` THEN UNDISCH_TAC `r <= r0` THEN
    REWRITE_TAC[IN_BALL; dist] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `(L:real^3->real^3) z = vector[&0;&0;t * z$3] /\
                L z' = vector[&0;&0;t * (z':real^3)$3]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(t * (z:real^3)$3 - s0) < r0 /\ abs(t * (z':real^3)$3 - s0) < r0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `abs((z:real^3)$3 - (p:real^3)$3) < r0` THEN
    UNDISCH_TAC `abs((z':real^3)$3 - (p:real^3)$3) < r0` THEN
    UNDISCH_TAC `(p:real^3)$3 = t * s0` THEN
    UNDISCH_TAC `t = &1 \/ t = -- &1` THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `t = &1 \/ t = -- &1` THEN STRIP_TAC THENL
   [USE_THEN "ax" (MP_TAC o SPECL [`t * (z:real^3)$3`; `t * (z':real^3)$3`]) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_LID];
    USE_THEN "ax" (MP_TAC o SPECL [`t * (z':real^3)$3`; `t * (z:real^3)$3`]) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`(th:real^N->real^2)((h':real^3->real^N)(vector[&0;&0;t * (z':real^3)$3]))`;
      `(th:real^N->real^2)((h':real^3->real^N)(vector[&0;&0;t * (z:real^3)$3]))`]
     MOI_LC1_CROSS_ANTI) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* B3i. Interior crossing charts along a closed double component k; k is a *)
(* PL circle (line charts, MOI_S4L_LINE_CHART_CIRCLES).                     *)
(* ------------------------------------------------------------------------- *)

let MOI_LC1_INTERIOR_CHART = prove
 (`!c (f:real^2->real^N) k y.
     moi_lt_normal2_disk c f /\ k IN components (moi_lt_double_image f) /\
     k INTER complex_boundary c = {} /\ y IN k
     ==> ?u (h:real^N->real^3) h' n1 n2.
           open_in (subtopology euclidean (UNIONS c)) u /\ y IN u /\
           pl_homeomorphism (u,IMAGE h u) (h,h') /\ h y = vec 0 /\
           u INTER complex_boundary c = {} /\ IMAGE h u = ball(vec 0,&1) /\
           {x | x IN std_triangle /\ f x IN u} = n1 UNION n2 /\ DISJOINT n1 n2 /\
           IMAGE (h o f) n1 = IMAGE h u INTER {z:real^3 | z$1 = &0} /\
           IMAGE (h o f) n2 = IMAGE h u INTER {z:real^3 | z$2 = &0} /\
           IMAGE h (moi_lt_double_image f INTER u) =
           IMAGE h u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0} /\
           open_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n1 /\
           open_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN moi_lt_double_image f` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^N) IN complex_boundary c)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `moi_lt_normal2_disk c (f:real^2->real^N)` THEN
  REWRITE_TAC[moi_lt_normal2_disk] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_lt_crossing2_at] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_LC1_NORM_AXIS = prove
 (`!s. norm(vector[&0;&0;s]:real^3) = abs s`,
  REWRITE_TAC[vector_norm; DOT_3; VECTOR_3] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; GSYM REAL_POW_2; POW_2_SQRT_ABS]);;

let MOI_LC1_K_LINE_CHARTS = prove
 (`!c (f:real^2->real^N) k.
     moi_lt_normal2_disk c f /\ k IN components (moi_lt_double_image f) /\
     k INTER complex_boundary c = {}
     ==> moi_s4l_line_charts k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s4l_line_charts] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N) /\
                (k:real^N->bool) SUBSET moi_lt_double_image f /\
                moi_lt_double_image f SUBSET UNIONS c`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_lt_normal2_disk c (f:real^2->real^N)` THEN
      SIMP_TAC[moi_lt_normal2_disk; moi_lt_normal_disk];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (f:real^2->real^N) std_triangle SUBSET UNIONS c` MP_TAC THENL
     [UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
      SIMP_TAC[moi_lt_singular_disk];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; moi_lt_double_image; IN_ELIM_THM; FORALL_IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^2. x IN std_triangle /\ (f:real^2->real^N) x = y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^N->bool) SUBSET moi_lt_double_image f` THEN
    UNDISCH_TAC `(y:real^N) IN k` THEN
    REWRITE_TAC[SUBSET; moi_lt_double_image; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `y:real^N`] MOI_LC1_INTERIOR_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
    (X_CHOOSE_THEN `h':real^3->real^N` (X_CHOOSE_THEN `n1:real^2->bool`
    (X_CHOOSE_THEN `n2:real^2->bool` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k}`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `n1:real^2->bool`;
                 `n2:real^2->bool`; `x:real^2`] MOI_LC1_CHART_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `(!y. y IN u ==> (h':real^3->real^N)((h:real^N->real^3) y) = y) /\
    h continuous_on u /\
    (!z. z IN ball(vec 0,&1) ==> h(h' z) = z) /\
    h' continuous_on ball(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (u,IMAGE (h:real^N->real^3) u) (h,h')` THEN
    ASM_REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `open_in (subtopology euclidean (UNIONS c)) (u:real^N->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `(k:real^N->bool) INTER U = moi_lt_double_image f INTER u` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`moi_lt_double_image f INTER u SUBSET (k:real^N->bool)`;
      `(k:real^N->bool) SUBSET moi_lt_double_image f`;
      `moi_lt_double_image (f:real^2->real^N) SUBSET UNIONS c`;
      `UNIONS c INTER U = u:real^N->bool`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^N. w IN moi_lt_double_image f INTER u
               ==> (h:real^N->real^3) w IN ball(vec 0,&1) /\ (h w)$1 = &0 /\ (h w)$2 = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^N->real^3) w IN IMAGE h (moi_lt_double_image f INTER u)` MP_TAC
    THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`U:real^N->bool`; `\w:real^N. lift(((h:real^N->real^3) w)$3)`;
    `\v:real^1. (h':real^3->real^N)(vector[&0;&0;drop v])`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:real^N) IN U` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS c INTER U = u:real^N->bool` THEN
    UNDISCH_TAC `(y:real^N) IN u` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!v:real^1. v IN ball(vec 0,&1) ==> vector[&0;&0;drop v] IN ball(vec 0:real^3,&1) /\
               (h':real^3->real^N)(vector[&0;&0;drop v]) IN moi_lt_double_image f INTER u /\
               (h:real^N->real^3)(h'(vector[&0;&0;drop v])) = vector[&0;&0;drop v]`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `vector[&0;&0;drop v] IN ball(vec 0:real^3,&1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL_0; MOI_LC1_NORM_AXIS] THEN
      UNDISCH_TAC `(v:real^1) IN ball(vec 0,&1)` THEN
      REWRITE_TAC[IN_BALL_0; NORM_REAL; GSYM drop];
      ALL_TAC] THEN
    SUBGOAL_THEN `?w:real^N. w IN moi_lt_double_image f INTER u /\
                             (h:real^N->real^3) w = vector[&0;&0;drop v]`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `vector[&0;&0;drop v]:real^3 IN
                    IMAGE (h:real^N->real^3) (moi_lt_double_image f INTER u)` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; VECTOR_3];
        REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^N) IN u` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h':real^3->real^N)(vector[&0;&0;drop v]) = w` ASSUME_TAC THENL
     [UNDISCH_TAC `(h:real^N->real^3) w = vector[&0;&0;drop v]` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^N. w IN moi_lt_double_image f INTER u
               ==> vector[&0;&0;((h:real^N->real^3) w)$3] = h w /\
                   lift((h w)$3) IN ball(vec 0,&1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `(w:real^N) IN moi_lt_double_image f INTER u`) o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `(h:real^N->real^3) w$1`)) (concl(SPEC `w:real^N` th)))) THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_BALL_0; NORM_LIFT] THEN
      MP_TAC(ISPECL [`(h:real^N->real^3) w`; `3`] COMPONENT_LE_NORM) THEN
      UNDISCH_TAC `(h:real^N->real^3) w IN ball(vec 0,&1)` THEN
      REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\w:real^N. lift(((h:real^N->real^3) w)$3)) (moi_lt_double_image f INTER u) =
    ball(vec 0:real^1,&1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `v:real^1` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `(h':real^3->real^N)(vector[&0;&0;drop v])` THEN
      ASM_SIMP_TAC[VECTOR_3; LIFT_DROP]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[OPEN_BALL; homeomorphism] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(w:real^N) IN u` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN ASM_SIMP_TAC[VECTOR_3; LIFT_DROP];
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `w:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `v:real^1` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN EXISTS_TAC `lift(((h:real^N->real^3) w)$3)` THEN
      ASM_SIMP_TAC[LIFT_DROP] THEN
      SUBGOAL_THEN `(w:real^N) IN u` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    SUBGOAL_THEN `(\v:real^1. (h':real^3->real^N)(vector[&0;&0;drop v])) =
                  h' o (\v:real^1. vector[&0;&0;drop v]:real^3)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[linear] THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT; DROP_ADD; DROP_CMUL] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&1)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[]]]);;

let MOI_LC1_K_CIRCLE = prove
 (`!c (f:real^2->real^N) k.
     moi_lt_normal2_disk c f /\ k IN components (moi_lt_double_image f) /\
     k INTER complex_boundary c = {} /\ 2 <= dimindex(:N)
     ==> pl_sphere 1 k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?s. FINITE s /\ combinatorial_manifold_with_boundary 1 s /\
                    UNIONS s = moi_lt_double_image (f:real^2->real^N)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lt_normal2_disk c (f:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_normal2_disk; moi_lt_normal_disk] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET moi_lt_double_image f /\ connected k /\ ~(k = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; IN_COMPONENTS_CONNECTED; IN_COMPONENTS_NONEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^N->bool. e IN s ==> ?n. n simplex e` ASSUME_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold_with_boundary 1 (s:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_S4L_LINE_CHART_CIRCLES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[pl_polyhedron] THEN
      EXISTS_TAC `{e:real^N->bool | e IN s /\ e SUBSET k}` THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
        MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
        GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(w:real^N) IN UNIONS s` MP_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
        EXISTS_TAC `moi_lt_double_image (f:real^2->real^N)` THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
          ASM SET_TAC[];
          ASM SET_TAC[]]];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`]
        MOI_LC1_K_LINE_CHARTS) THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[IN_COMPONENTS_SELF]]);;

(* ------------------------------------------------------------------------- *)
(* B3j. Existence of normalized charts at every point of J.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_LC1_NCHART_EXISTS = prove
 (`!c (f:real^2->real^N) k J th x x' rho.
     moi_lt_normal2_disk c f /\ k IN components (moi_lt_double_image f) /\
     k INTER complex_boundary c = {} /\
     J = {x | x IN std_triangle /\ f x IN k} /\
     (?gam:real^1->real^2. simple_path gam /\ pathfinish gam = pathstart gam /\
                           path_image gam = J) /\
     th continuous_on k /\ (!y z. y IN k /\ z IN k /\ th y = th z ==> y = z) /\
     (!y. y IN k ==> norm(th y) = &1) /\
     x IN J /\ x' IN std_triangle /\ ~(x' = x) /\ f x' = f x /\
     (!z. z IN std_triangle /\ f z = f x ==> z = x \/ z = x') /\
     &0 < rho /\ &2 * rho <= dist(x,x')
     ==> ?g p r. moi_lc1_nchart c f J th rho x x' g p r`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lt_normal2_disk c (f:real^2->real^N)` THEN
    SIMP_TAC[moi_lt_normal2_disk; moi_lt_normal_disk];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) x IN k /\ x IN std_triangle /\ (x':real^2) IN J`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN J` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `(f:real^2->real^N) x`] MOI_LC1_INTERIOR_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
    (X_CHOOSE_THEN `h':real^3->real^N` (X_CHOOSE_THEN `n1:real^2->bool`
    (X_CHOOSE_THEN `n2:real^2->bool` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `J:real^2->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                 `h':real^3->real^N`; `n1:real^2->bool`; `n2:real^2->bool`; `x:real^2`]
    MOI_LC1_CHART_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN n1 UNION n2 /\ (x':real^2) IN n1 UNION n2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN u} = n1 UNION n2` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((h:real^N->real^3) o (f:real^2->real^N)) x' = (h o f) x` ASSUME_TAC
  THENL [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(!z:real^2. z IN std_triangle /\ (f:real^2->real^N) z = f x'
                            ==> z = x' \/ z = x) /\ &2 * rho <= dist(x',x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ASM_MESON_TAC[DIST_SYM]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^2) IN n1` THENL
   [SUBGOAL_THEN `(x':real^2) IN n2` ASSUME_TAC THENL
     [UNDISCH_TAC `(x':real^2) IN n1 UNION n2` THEN REWRITE_TAC[IN_UNION] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `x':real^2 = x` (fun th -> ASM_MESON_TAC[th]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `n1:real^2->bool`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 2)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                   `J:real^2->bool`; `th:real^N->real^2`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `n1:real^2->bool`;
                   `n2:real^2->bool`; `x:real^2`; `x':real^2`; `rho:real`]
      MOI_LC1_NCHART_FROM_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN n2 /\ (x':real^2) IN n1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^2) IN n1 UNION n2` THEN ASM_REWRITE_TAC[IN_UNION];
      ALL_TAC] THEN
    UNDISCH_TAC `(x':real^2) IN n1 UNION n2` THEN REWRITE_TAC[IN_UNION] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `x':real^2 = x` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `n2:real^2->bool`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^2) IN n1 UNION n2` THEN ASM_REWRITE_TAC[IN_UNION];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `J:real^2->bool`; `th:real^N->real^2`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `n1:real^2->bool`;
                 `n2:real^2->bool`; `x':real^2`; `x:real^2`; `rho:real`]
    MOI_LC1_NCHART_FROM_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^N` (X_CHOOSE_THEN `p:real^3`
    (X_CHOOSE_TAC `r:real`))) THEN
  MAP_EVERY EXISTS_TAC [`(g:real^3->real^N) o moi_lc1_swap`; `moi_lc1_swap p`;
                        `r:real`] THEN
  MATCH_MP_TAC MOI_LC1_NCHART_SWAP THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* B3k. The sign of a point x of J: some normalized chart at x (with the    *)
(* other preimage x') has orientation sign v.                               *)
(* ------------------------------------------------------------------------- *)

let moi_lc1_sig = new_definition
 `moi_lc1_sig (c:(real^N->bool)->bool) sg (f:real^2->real^N) J th x v <=>
    ?x' rho (g:real^3->real^N) p r.
       x' IN std_triangle /\ ~(x' = x) /\ f x' = f x /\
       (!z. z IN std_triangle /\ f z = f x ==> z = x \/ z = x') /\
       &0 < rho /\ &2 * rho <= dist(x,x') /\
       moi_lc1_nchart c f J th rho x x' g p r /\
       moi_lc1_osign c sg g (ball(vec 0,&1)) v`;;
let MOI_LC1_NCHART_VALID = prove
 (`!c (f:real^2->real^N) J th rho x x' g p r.
     moi_lc1_nchart c f J th rho x x' g p r
     ==> pl_map_on (ball(vec 0,&1)) g /\
         (!y z. y IN ball(vec 0,&1) /\ z IN ball(vec 0,&1) /\ g y = g z ==> y = z) /\
         IMAGE g (ball(vec 0,&1)) SUBSET UNIONS c /\
         IMAGE g (ball(vec 0,&1)) SUBSET UNIONS c DIFF complex_boundary c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lc1_nchart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `g':real^N->real^3`)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^N) (ball(vec 0,&1)) SUBSET UNIONS c` ASSUME_TAC
  THENL [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (ball(vec 0,&1),IMAGE (g:real^3->real^N)
                                     (ball(vec 0,&1))) (g,g')` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN MESON_TAC[];
    ASM SET_TAC[]]);;

let MOI_LC1_SIG_SWAP = prove
 (`!c sg (f:real^2->real^N) J th x v.
     FINITE c /\ lf_simplicial_complex c /\ (!t. t IN c ==> aff_dim t <= &3) /\
     (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
                ==> (sg a b d e = &1 \/ sg a b d e = -- &1)) /\
     (!g:real^3->real^N.
        pl_map_on (ball(vec 0,&1)) g /\
        (!x y. x IN ball(vec 0,&1) /\ y IN ball(vec 0,&1) /\ g x = g y ==> x = y) /\
        IMAGE g (ball(vec 0,&1)) SUBSET UNIONS c DIFF complex_boundary c
        ==> ?s. (s = &1 \/ s = -- &1) /\ moi_lc1_osign c sg g (ball(vec 0,&1)) s) /\
     (v = &1 \/ v = -- &1) /\ x IN std_triangle /\ moi_lc1_sig c sg f J th x v
     ==> ?x'. x' IN std_triangle /\ ~(x' = x) /\ f x' = f x /\
              moi_lc1_sig c sg f J th x' (--v)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  UNDISCH_TAC `moi_lc1_sig c sg (f:real^2->real^N) J th x v` THEN
  REWRITE_TAC[moi_lc1_sig] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^2` (X_CHOOSE_THEN `rho:real`
    (X_CHOOSE_THEN `g:real^3->real^N` (X_CHOOSE_THEN `p:real^3`
    (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))))) THEN
  EXISTS_TAC `x':real^2` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `J:real^2->bool`;
                 `th:real^N->real^2`; `rho:real`; `x:real^2`; `x':real^2`;
                 `g:real^3->real^N`; `p:real^3`; `r:real`] MOI_LC1_NCHART_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `J:real^2->bool`;
                 `th:real^N->real^2`; `rho:real`; `x:real^2`; `x':real^2`;
                 `g:real^3->real^N`; `p:real^3`; `r:real`] MOI_LC1_NCHART_VALID) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `J:real^2->bool`;
                 `th:real^N->real^2`; `rho:real`; `x':real^2`; `x:real^2`;
                 `(g:real^3->real^N) o moi_lc1_swap`; `moi_lc1_swap p`; `r:real`]
    MOI_LC1_NCHART_VALID) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^3->real^N) o moi_lc1_swap` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_lc1_osign"))
        (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `s' = --v` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LC1_OSIGN_SWAP THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`;
                          `sg:real^N->real^N->real^N->real^N->real`; `g:real^3->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`x:real^2`; `rho:real`; `(g:real^3->real^N) o moi_lc1_swap`;
                        `moi_lc1_swap p`; `r:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[DIST_SYM]);;

let MOI_LC1_SIG_LOCAL = prove
 (`!c sg (f:real^2->real^N) J th x v.
     moi_lt_singular_disk c f /\ J SUBSET std_triangle /\ x IN std_triangle /\
     moi_lc1_sig c sg f J th x v
     ==> ?e. &0 < e /\
             !x1. x1 IN std_triangle /\ f x1 IN moi_lt_double_image f /\ dist(x,x1) < e
                  ==> moi_lc1_sig c sg f J th x1 v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lc1_sig] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^2` (X_CHOOSE_THEN `rho:real`
    (X_CHOOSE_THEN `g:real^3->real^N` (X_CHOOSE_THEN `p:real^3`
    (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `J:real^2->bool`;
                 `th:real^N->real^2`; `rho:real`; `x:real^2`; `x':real^2`;
                 `g:real^3->real^N`; `p:real^3`; `r:real`] MOI_LC1_NCHART_LOCAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x1:real^2` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `x1:real^2`]
    MOI_LCC_FIBER_TWO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1':real^2` STRIP_ASSUME_TAC) THEN
  USE_THEN "loc" (MP_TAC o SPECL [`x1:real^2`; `x1':real^2`; `dist(x1:real^2,x1') / &2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < dist(x1:real^2,x1')` MP_TAC THENL
     [ASM_MESON_TAC[DIST_POS_LT]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^3` (X_CHOOSE_TAC `r1:real`)) THEN
  MAP_EVERY EXISTS_TAC [`x1':real^2`; `dist(x1:real^2,x1') / &2`; `g:real^3->real^N`;
                        `p1:real^3`; `r1:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < dist(x1:real^2,x1')` MP_TAC THENL
   [ASM_MESON_TAC[DIST_POS_LT]; REAL_ARITH_TAC]);;

let MOI_LC1_SIG_UNIQUE = prove
 (`!c sg (f:real^2->real^N) J th x.
     FINITE c /\ lf_simplicial_complex c /\ (!t. t IN c ==> aff_dim t <= &3) /\
     (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
                ==> (sg a b d e = &1 \/ sg a b d e = -- &1)) /\
     moi_lt_singular_disk c f /\ J SUBSET std_triangle /\ x IN std_triangle /\
     moi_lc1_sig c sg f J th x (&1) /\ moi_lc1_sig c sg f J th x (-- &1)
     ==> F`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lc1_sig] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC MP_TAC)))))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `x2:real^2` (X_CHOOSE_THEN `rho2:real`
    (X_CHOOSE_THEN `g2:real^3->real^N` (X_CHOOSE_THEN `p2:real^3`
    (X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^2` (X_CHOOSE_THEN `rho1:real`
    (X_CHOOSE_THEN `g1:real^3->real^N` (X_CHOOSE_THEN `p1:real^3`
    (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `x2:real^2 = x1` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `J:real^2->bool`;
                 `th:real^N->real^2`; `rho1:real`; `x:real^2`; `x1:real^2`;
                 `g1:real^3->real^N`; `p1:real^3`; `r1:real`] MOI_LC1_NCHART_LOCAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
  USE_THEN "loc" (MP_TAC o SPECL [`x:real^2`; `x1:real^2`; `rho2:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[DIST_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p3:real^3` (X_CHOOSE_TAC `r3:real`)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real^N->real`;
                 `f:real^2->real^N`; `J:real^2->bool`; `th:real^N->real^2`; `rho2:real`;
                 `x:real^2`; `x1:real^2`; `g1:real^3->real^N`; `p3:real^3`; `r3:real`;
                 `g2:real^3->real^N`; `p2:real^3`; `r2:real`; `&1`; `-- &1`]
    MOI_LC1_CHART_INDEP) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_LC1_SIG_EXISTS = prove
 (`!c sg (f:real^2->real^N) k J th x.
     (!g:real^3->real^N.
        pl_map_on (ball(vec 0,&1)) g /\
        (!x y. x IN ball(vec 0,&1) /\ y IN ball(vec 0,&1) /\ g x = g y ==> x = y) /\
        IMAGE g (ball(vec 0,&1)) SUBSET UNIONS c DIFF complex_boundary c
        ==> ?s. (s = &1 \/ s = -- &1) /\ moi_lc1_osign c sg g (ball(vec 0,&1)) s) /\
     moi_lt_normal2_disk c f /\ k IN components (moi_lt_double_image f) /\
     k INTER complex_boundary c = {} /\
     J = {x | x IN std_triangle /\ f x IN k} /\
     (?gam:real^1->real^2. simple_path gam /\ pathfinish gam = pathstart gam /\
                           path_image gam = J) /\
     th continuous_on k /\ (!y z. y IN k /\ z IN k /\ th y = th z ==> y = z) /\
     (!y. y IN k ==> norm(th y) = &1) /\ x IN J
     ==> moi_lc1_sig c sg f J th x (&1) \/ moi_lc1_sig c sg f J th x (-- &1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lt_normal2_disk c (f:real^2->real^N)` THEN
    SIMP_TAC[moi_lt_normal2_disk; moi_lt_normal_disk];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN std_triangle /\
                (f:real^2->real^N) x IN moi_lt_double_image f`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN J` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `x:real^2`]
    MOI_LCC_FIBER_TWO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < dist(x:real^2,x')` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIST_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                 `J:real^2->bool`; `th:real^N->real^2`; `x:real^2`; `x':real^2`;
                 `dist(x:real^2,x') / &2`] MOI_LC1_NCHART_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^N` (X_CHOOSE_THEN `p:real^3`
    (X_CHOOSE_TAC `r:real`))) THEN
  UNDISCH_TAC `J = {x | x IN std_triangle /\ (f:real^2->real^N) x IN k}` THEN
  DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `J:real^2->bool`;
                 `th:real^N->real^2`; `dist(x:real^2,x') / &2`; `x:real^2`; `x':real^2`;
                 `g:real^3->real^N`; `p:real^3`; `r:real`] MOI_LC1_NCHART_VALID) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `g:real^3->real^N` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_lc1_osign"))
        (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `moi_lc1_sig c sg (f:real^2->real^N) J th x s` MP_TAC THENL
   [REWRITE_TAC[moi_lc1_sig] THEN
    MAP_EVERY EXISTS_TAC [`x':real^2`; `dist(x:real^2,x') / &2`; `g:real^3->real^N`;
                          `p:real^3`; `r:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `s = &1 \/ s = -- &1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* B3l. Case 1 is excluded: the sign of J is locally constant, takes both   *)
(* values (swap of the two preimages) and J is connected.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_LC1_CASE1_MAIN = prove
 (`!(c:(real^N->bool)->bool) sg (f:real^2->real^N) k.
     FINITE c /\ lf_simplicial_complex c /\ (!t. t IN c ==> aff_dim t <= &3) /\
     (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
                ==> (sg a b d e = &1 \/ sg a b d e = -- &1)) /\
     (!g:real^3->real^N.
        pl_map_on (ball(vec 0,&1)) g /\
        (!x y. x IN ball(vec 0,&1) /\ y IN ball(vec 0,&1) /\ g x = g y ==> x = y) /\
        IMAGE g (ball(vec 0,&1)) SUBSET UNIONS c DIFF complex_boundary c
        ==> ?s. (s = &1 \/ s = -- &1) /\ moi_lc1_osign c sg g (ball(vec 0,&1)) s) /\
     moi_lt_normal2_disk c f /\ k IN components (moi_lt_double_image f) /\
     k INTER complex_boundary c = {}
     ==> ~connected {x | x IN std_triangle /\ f x IN k}`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N) /\ moi_lt_normal_disk c f`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lt_normal2_disk c (f:real^2->real^N)` THEN
    SIMP_TAC[moi_lt_normal2_disk; moi_lt_normal_disk];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^N->bool) SUBSET moi_lt_double_image f /\ ~(k = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; IN_COMPONENTS_NONEMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `?x0:real^2. x0 IN std_triangle /\ (f:real^2->real^N) x0 IN k`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(k:real^N->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    UNDISCH_TAC `(k:real^N->bool) SUBSET moi_lt_double_image f` THEN
    REWRITE_TAC[SUBSET; moi_lt_double_image; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k} IN
    components {x | x IN std_triangle /\ f x IN moi_lt_double_image f}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`]
      MOI_LA1_SK_UNION) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o SYM)] THEN
    SUBGOAL_THEN
     `?C. C IN components {x | x IN std_triangle /\
                               (f:real^2->real^N) x IN moi_lt_double_image f} /\
          IMAGE f C = k /\ (x0:real^2) IN C`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
       `(x0:real^2) IN UNIONS {C | C IN components {x | x IN std_triangle /\
                                  (f:real^2->real^N) x IN moi_lt_double_image f} /\
                                  IMAGE f C = k}`
      MP_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k} = C` SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
        EXISTS_TAC `{x | x IN std_triangle /\
                         (f:real^2->real^N) x IN moi_lt_double_image f}` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x0:real^2` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM];
        SUBGOAL_THEN `(C:real^2->bool) SUBSET
                      {x | x IN std_triangle /\ (f:real^2->real^N) x IN moi_lt_double_image f}`
        MP_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
        UNDISCH_TAC `IMAGE (f:real^2->real^N) C = k` THEN SET_TAC[]];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k} INTER
                relative_frontier std_triangle = {}` ASSUME_TAC THENL
   [SUBGOAL_THEN `{x | x IN std_triangle /\ (f:real^2->real^N) x IN complex_boundary c} =
                  relative_frontier std_triangle` MP_TAC THENL
     [UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
      SIMP_TAC[moi_lt_singular_disk];
      ALL_TAC] THEN
    UNDISCH_TAC `k INTER complex_boundary c = {}:real^N->bool` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?gam:real^1->real^2. simple_path gam /\ pathfinish gam = pathstart gam /\
                         path_image gam = {x | x IN std_triangle /\ (f:real^2->real^N) x IN k}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{x | x IN std_triangle /\ (f:real^2->real^N) x IN k}`;
                   `vec 0:real^2`; `&1`] HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE_EQ) THEN
    REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_LC1_PL_SPHERE1_CIRCLE THEN MATCH_MP_TAC MOI_LA1_POLYGON_COMPONENT THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`;
                   `(f:real^2->real^N) x0`] MOI_LC1_INTERIOR_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
      (X_CHOOSE_THEN `h':real^3->real^N` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`h':real^3->real^N`; `ball(vec 0:real^3,&1)`]
      INVARIANCE_OF_DIMENSION) THEN
    REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY; DIMINDEX_3] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `pl_homeomorphism (u,IMAGE (h:real^N->real^3) u) (h,h')` THEN
      ASM_REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ASM_MESON_TAC[]];
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?th:real^N->real^2. th continuous_on k /\
                        (!y z. y IN k /\ z IN k /\ th y = th z ==> y = z) /\
                        (!y. y IN k ==> norm(th y) = &1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`]
      MOI_LC1_K_CIRCLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_LC1_PL_SPHERE1_CIRCLE) THEN
    REWRITE_TAC[homeomorphic; homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `th:real^N->real^2` (X_CHOOSE_THEN `th':real^2->real^N`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `th:real^N->real^2` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(th:real^N->real^2) y IN sphere(vec 0,&1)` MP_TAC THENL
       [UNDISCH_TAC `IMAGE (th:real^N->real^2) k = sphere(vec 0,&1)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
        REWRITE_TAC[IN_SPHERE_0]]];
    ALL_TAC] THEN
  ABBREV_TAC `J = {x | x IN std_triangle /\ (f:real^2->real^N) x IN k}` THEN
  SUBGOAL_THEN `(!x. x IN J <=> x IN std_triangle /\ (f:real^2->real^N) x IN k) /\
                J SUBSET std_triangle /\ (x0:real^2) IN J /\
                (!x:real^2. x IN J ==> x IN std_triangle /\
                                       (f:real^2->real^N) x IN moi_lt_double_image f)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN
    REWRITE_TAC[IN_ELIM_THM; ASSUME `(x0:real^2) IN std_triangle`;
                ASSUME `(f:real^2->real^N) x0 IN k`] THEN
    UNDISCH_TAC `(k:real^N->bool) SUBSET moi_lt_double_image f` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN k} = J` THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN
   `!x. x IN J ==> moi_lc1_sig c sg (f:real^2->real^N) J th x (&1) \/
                   moi_lc1_sig c sg f J th x (-- &1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_LC1_SIG_EXISTS THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN J ==> ~(moi_lc1_sig c sg (f:real^2->real^N) J th x (&1) /\
                     moi_lc1_sig c sg f J th x (-- &1))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_LC1_SIG_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`;
                          `sg:real^N->real^N->real^N->real^N->real`;
                          `f:real^2->real^N`; `J:real^2->bool`; `th:real^N->real^2`;
                          `x:real^2`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v x. (v = &1 \/ v = -- &1) /\ x IN J /\ moi_lc1_sig c sg (f:real^2->real^N) J th x v
          ==> ?x'. x' IN J /\ moi_lc1_sig c sg f J th x' (--v)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real^N->real`;
                   `f:real^2->real^N`; `J:real^2->bool`; `th:real^N->real^2`;
                   `x:real^2`; `v:real`] MOI_LC1_SIG_SWAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x':real^2` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^2) IN J` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `!x:real^2. x IN J <=> x IN std_triangle /\ (f:real^2->real^N) x IN k` THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN
   `!v. (v = &1 \/ v = -- &1)
        ==> open_in (subtopology euclidean J)
                    {x | x IN J /\ moi_lc1_sig c sg (f:real^2->real^N) J th x v}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real^N->real`;
                   `f:real^2->real^N`; `J:real^2->bool`; `th:real^N->real^2`;
                   `x:real^2`; `v:real`] MOI_LC1_SIG_LOCAL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc")) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_ELIM_THM] THEN
    X_GEN_TAC `x1:real^2` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "loc" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?x1 x2. x1 IN J /\ moi_lc1_sig c sg (f:real^2->real^N) J th x1 (&1) /\
            x2 IN J /\ moi_lc1_sig c sg f J th x2 (-- &1)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o C MATCH_MP (ASSUME `(x0:real^2) IN J`) o check (fun th ->
      is_forall(concl th) && is_disj(snd(dest_imp(snd(dest_forall(concl th))))))) THENL
     [MP_TAC(SPECL [`&1`; `x0:real^2`] (ASSUME
       `!v x. (v = &1 \/ v = -- &1) /\ x IN J /\
              moi_lc1_sig c sg (f:real^2->real^N) J th x v
              ==> ?x'. x' IN J /\ moi_lc1_sig c sg f J th x' (--v)`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x2:real^2` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`x0:real^2`; `x2:real^2`] THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`-- &1`; `x0:real^2`] (ASSUME
       `!v x. (v = &1 \/ v = -- &1) /\ x IN J /\
              moi_lc1_sig c sg (f:real^2->real^N) J th x v
              ==> ?x'. x' IN J /\ moi_lc1_sig c sg f J th x' (--v)`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_NEG_NEG] THEN
      DISCH_THEN(X_CHOOSE_THEN `x1:real^2` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`x1:real^2`; `x0:real^2`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `connected (J:real^2->bool)` THEN
  REWRITE_TAC[CONNECTED_OPEN_IN; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`{x | x IN J /\ moi_lc1_sig c sg (f:real^2->real^N) J th x (&1)}`;
    `{x | x IN J /\ moi_lc1_sig c sg (f:real^2->real^N) J th x (-- &1)}`]) THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> F`) THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;
(* ------------------------------------------------------------------------- *)
(* The main theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

let CASE1_FROM_ORIENT = prove
 (MOI_LT3_CASE1_FROM_ORIENT,
  DISCH_THEN(LABEL_TAC "os") THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `k:real^N->bool`] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `orientable_complex (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[MOI_LT3D_ORIENT_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^N->real^N->real^N->real^N->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "c2"))) THEN
  MATCH_MP_TAC MOI_LC1_CASE1_MAIN THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`;
                        `sg:real^N->real^N->real^N->real^N->real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    MATCH_MP_TAC CM_WB_DIM THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] THEN
    STRIP_TAC THEN
    USE_THEN "c1" (MP_TAC o C MATCH_MP (CONJ
      (ASSUME `convex hull {a:real^N,b,d,e} IN c`)
      (ASSUME `aff_dim(convex hull {a:real^N,b,d,e}) = &3`))) THEN
    SIMP_TAC[];
    X_GEN_TAC `g:real^3->real^N` THEN STRIP_TAC THEN
    USE_THEN "os" (MP_TAC o SPECL [`c:(real^N->bool)->bool`;
      `sg:real^N->real^N->real^N->real^N->real`; `g:real^3->real^N`;
      `ball(vec 0:real^3,&1)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_BALL; CONNECTED_BALL]; REWRITE_TAC[moi_lc1_osign]]]);;


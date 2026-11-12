(* ========================================================================= *)
(* Unit pc_p2b_x2 (Part 2B, MT Prop 9.39 with Cor 9.52): the route X2,       *)
(*   P2BX2_CYL_ROUTE |- !w. P2B_CYL_AT_INFINITY_ROUTE_STATEMENT w.           *)
(* X0 gives the based limit (top',atlas',g',xl) on s <= 0 with a global     *)
(* parallel unit field.  The limit is in the class p2b_ancflow0 on s < 0    *)
(* (non-flat by P2BX0_SCALAR_POS_ALL), p2b_lorient passes to it             *)
(* (P2B_KSEP_LIMIT_DIRECT), and SPLIT_ROUND gives the cylinder model of     *)
(* every shift g'(t + s0), s0 < 0.  The model of g' itself (time 0         *)
(* included): a cylinder family is affine in t and the pullback by a local *)
(* parametrization is a congruence by an invertible matrix, so             *)
(* t |-> g'(t)(x) is affine on every (-inf,s0], hence on (-inf,0] by left  *)
(* continuity at 0 (rfs_flow_upto); the s0 = -1 model then holds for all   *)
(* t <= 0, and a radial power map corrects the line factor.                *)
(* ========================================================================= *)

needs "src/pc_p2b_x0.ml";;
needs "src/pc_smt_radial.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Matrix algebra.  Cylinder-type fields p2bx2_cab A B z = (2/|z|^2) (A P_t  *)
(* + B P_r) (P_r the radial projector, P_t = I - P_r), affine families of    *)
(* matrices, congruences, and the pullback of a cylinder-type field by the   *)
(* radial power map of pc_rf_basic.                                          *)
(* ========================================================================= *)

let p2bx2_cab = new_definition
 `p2bx2_cab (A:real) (B:real) (z:real^3) =
    (&2 / norm z pow 2) %%
    (A %% mat 1 + ((B - A) / norm z pow 2) %% ((lambda i j. z$i * z$j):real^3^3))`;;

(* The model slices: lam cyl(u / lam) has A = lam - u and B = lam. *)

let P2BX2_CAB_CYL = prove
 (`!lam u z:real^3.
     ~(lam = &0) ==> lam %% cylinder_flow (u / lam) z = p2bx2_cab (lam - u) lam z`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; cylinder_flow; p2bx2_cab; MATRIX_CMUL_COMPONENT;
           MATRIX_ADD_COMPONENT; MAT_COMPONENT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  UNDISCH_TAC `~(lam = &0)` THEN CONV_TAC REAL_FIELD);;

(* Affine dependence on the first parameter. *)

let P2BX2_CAB_SUB = prove
 (`!a b t z:real^3.
     p2bx2_cab (a - t) b z = p2bx2_cab a b z + t %% p2bx2_cab (--(&1)) (&0) z`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; p2bx2_cab; MATRIX_CMUL_COMPONENT;
           MATRIX_ADD_COMPONENT; MAT_COMPONENT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[real_div] THEN
  CONV_TAC REAL_RING);;

(* The quadratic form of a cylinder-type field on vectors orthogonal to z. *)

let P2BX2_CAB_TANGENT = prove
 (`!A B z v:real^3.
     z dot v = &0 ==> v dot (p2bx2_cab A B z ** v) = &2 / norm z pow 2 * A * (v dot v)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[p2bx2_cab; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              MATRIX_VECTOR_MUL_LID; RFB_OUTER_MUL] THEN
  ASM_REWRITE_TAC[DOT_RMUL; DOT_RADD; VECTOR_MUL_LZERO; DOT_RZERO] THEN
  REAL_ARITH_TAC);;

(* Two affine families that agree on a half-line have equal coefficients. *)

let P2BX2_AFFINE_UNIQUE = prove
 (`!(H0:real^N^N) H1 K0 K1 s.
     (!t. t <= s ==> H0 + t %% H1 = K0 + t %% K1) ==> H0 = K0 /\ H1 = K1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i j. (H0:real^N^N)$i$j = (K0:real^N^N)$i$j /\ (H1:real^N^N)$i$j = (K1:real^N^N)$i$j`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(AP_TERM `\M:real^N^N. M$i$j` (MP (SPEC `s:real` th) (SPEC `s:real` REAL_LE_REFL))) THEN
      MP_TAC(AP_TERM `\M:real^N^N. M$i$j` (MP (SPEC `s - &1` th) (REAL_ARITH `s - &1 <= s`)))) THEN
    REWRITE_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN CONV_TAC REAL_RING;
    ASM_REWRITE_TAC[CART_EQ]]);;

(* Congruence by an invertible matrix is undone by its inverse; congruence  *)
(* preserves affine families.                                                *)

let P2BX2_CONGR_INV = prove
 (`!(J:real^N^N) (H:real^N^N) (M:real^N^N).
     invertible J /\ transp J ** H ** J = M
     ==> H = transp(matrix_inv J) ** M ** matrix_inv J`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
  ASM_REWRITE_TAC[TRANSP_MAT; MATRIX_MUL_LID] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_MUL_RID]);;

let P2BX2_CONGR_AFFINE = prove
 (`!(Q:real^N^N) C0 C1 t.
     transp Q ** (C0 + t %% C1) ** Q = transp Q ** C0 ** Q + t %% (transp Q ** C1 ** Q)`,
  REWRITE_TAC[MATRIX_ADD_LDISTRIB; MATRIX_ADD_RDISTRIB; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

(* A function continuous at 0 that is affine on t < 0 takes the affine     *)
(* value at 0.                                                               *)

let P2BX2_LEFT_LIMIT = prove
 (`!f a b. f real_continuous atreal (&0) /\ (!t. t < &0 ==> f t = a + t * b)
           ==> f(&0) = a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\t. f t - (a + t * b)) real_continuous atreal (&0)` MP_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_RMUL THEN REWRITE_TAC[REAL_CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < abs(x - a)) ==> x = a`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `abs(f(&0) - a)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--(d / &2)`) THEN
  SUBGOAL_THEN `(f:real->real)(--(d / &2)) = a + --(d / &2) * b` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* A matrix family affine on every (-inf,s], s < 0, with entries continuous *)
(* at 0 from the left is affine on (-inf,0].                                 *)

let P2BX2_AFFINE_EXTEND = prove
 (`!H:real->real^3^3.
     (!s. s < &0 ==> ?H0 H1. !t. t <= s ==> H t = H0 + t %% H1) /\
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
            ==> ?f. f real_continuous atreal (&0) /\ !t. t <= &0 ==> f t = H t$i$j)
     ==> ?H0 H1. !t. t <= &0 ==> H t = H0 + t %% H1`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "aff") (LABEL_TAC "cont")) THEN
  USE_THEN "aff" (MP_TAC o SPEC `--(&1)`) THEN REWRITE_TAC[REAL_ARITH `--(&1) < &0`] THEN
  DISCH_THEN(X_CHOOSE_THEN `H0:real^3^3` (X_CHOOSE_THEN `H1:real^3^3` (LABEL_TAC "m1"))) THEN
  MAP_EVERY EXISTS_TAC [`H0:real^3^3`; `H1:real^3^3`] THEN
  SUBGOAL_THEN `!t. t < &0 ==> (H:real->real^3^3) t = H0 + t %% H1` (LABEL_TAC "neg") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `t <= --(&1)` THENL
     [USE_THEN "m1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "aff" (MP_TAC o C MATCH_MP (ASSUME `t < &0`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `K0:real^3^3` (X_CHOOSE_THEN `K1:real^3^3` (LABEL_TAC "mt"))) THEN
    MP_TAC(ISPECL [`H0:real^3^3`; `H1:real^3^3`; `K0:real^3^3`; `K1:real^3^3`; `--(&1)`]
                  P2BX2_AFFINE_UNIQUE) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
      USE_THEN "m1" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `u <= --(&1)`))]) THEN
      USE_THEN "mt" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "mt" MATCH_MP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `t < &0` THENL [USE_THEN "neg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t = &0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  USE_THEN "cont" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real->real`; `(H0:real^3^3)$i$j`; `(H1:real^3^3)$i$j`] P2BX2_LEFT_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real->real) u = (H:real->real^3^3) u$i$j` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "neg" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `u < &0`)]) THEN
    REWRITE_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real)(&0) = (H:real->real^3^3)(&0)$i$j` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* The radial power map z |-> (|z|^2)^e z pulls a cylinder-type field back  *)
(* to one with the line coefficient multiplied by (2e + 1)^2.               *)

let P2BX2_PW_PULLBACK_CAB = prove
 (`!e A B y:real^3.
     ~(y = vec 0)
     ==> mpullback (\z:real^3. ((norm z pow 2) rpow e) % z) (p2bx2_cab A B) y =
         p2bx2_cab A ((&2 * e + &1) pow 2 * B) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real`; `y:real^3`] RFB_PW_FRECHET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFB_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  ASM_SIMP_TAC[LRG_MPULLBACK_DOT] THEN
  ASM_REWRITE_TAC[p2bx2_cab; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
                  MATRIX_VECTOR_MUL_LID; RFB_OUTER_MUL] THEN
  REWRITE_TAC[DOT_RMUL; DOT_LMUL; DOT_RADD; DOT_LADD; NORM_POW_2] THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[RPOW_SUB; RPOW_POW; REAL_POW_1] THEN
  SUBGOAL_THEN `&0 < ((y:real^3) dot y) rpow e` MP_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < (y:real^3) dot y` THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

(* The power map commutes with the twist y |-> -y/|y|^2. *)

let P2BX2_TWIST_NONZERO = prove
 (`!y:real^3. ~(y = vec 0) ==> ~(rfs_twist y = vec 0)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `rfs_twist (y:real^3) = vec 0` THEN
  REWRITE_TAC[rfs_twist; VECTOR_NEG_EQ_0; VECTOR_MUL_EQ_0; REAL_INV_EQ_0] THEN
  ASM_REWRITE_TAC[REAL_POW_EQ_0; NORM_EQ_0] THEN ARITH_TAC);;

let P2BX2_PW_TWIST = prove
 (`!e y:real^3.
     ~(y = vec 0)
     ==> ((norm(rfs_twist y) pow 2) rpow e) % rfs_twist y =
         rfs_twist(((norm y pow 2) rpow e) % y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LRG_CYL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(rfs_twist (y:real^3)) pow 2 = inv(norm y pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[rfs_twist; NORM_NEG; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    UNDISCH_TAC `&0 < norm(y:real^3) pow 2` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[rfs_twist] THEN ASM_SIMP_TAC[RFB_PW_NORM2] THEN
  REWRITE_TAC[VECTOR_MUL_RNEG; VECTOR_MUL_ASSOC; VECTOR_EQ_NEG2] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[RPOW_INV; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `(norm(y:real^3) pow 2) rpow (&2 * e + &1) =
                (norm y pow 2) rpow e * (norm y pow 2) rpow e * norm y pow 2`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM RPOW_ADD; REAL_ARITH `&2 * e + &1 = e + e + &1`] THEN
    ASM_SIMP_TAC[RPOW_ADD; RPOW_POW; REAL_POW_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (norm(y:real^3) pow 2) rpow e` MP_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < norm(y:real^3) pow 2` THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The pullback by a local parametrization at a point is a congruence by an  *)
(* invertible matrix that does not depend on the metric; left continuity in  *)
(* time of the metric at a point (rfs_flow_upto); the shifted models make t  *)
(* |-> g(t)(x) affine on (-inf,0], so one model holds for all t <= 0.        *)
(* ========================================================================= *)

let P2BX2_PULL_AT = prove
 (`!top atlas s (e:real^3->B) y.
     smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\ y IN s
     ==> e y IN topspace top /\
         invertible(matrix(frechet_derivative (SND(chart_at atlas (e y)) o e) (at y))) /\
         !G:B->real^3^3.
           rfs_pullback atlas e G y =
           transp(matrix(frechet_derivative (SND(chart_at atlas (e y)) o e) (at y))) **
           G(e y) **
           matrix(frechet_derivative (SND(chart_at atlas (e y)) o e) (at y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->B`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:B->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^3->B) y IN topspace top` ASSUME_TAC THENL
   [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(e:real^3->B) y`]
                  CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`chart_at (atlas:((B->bool)#(B->real^3))->bool) ((e:real^3->B) y)`,
             `ch:(B->bool)#(B->real^3)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`V:B->bool`; `psi:B->real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `s:real^3->bool`;
                   `e:real^3->B`; `V:B->bool`; `psi:B->real^3`] APX_PARAM_CHART_REP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e2:B->real^3` (ASSUME_TAC o CONJUNCT1)) THEN
    MATCH_MP_TAC LRG_DIFFEO_JACOBIAN_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (psi:B->real^3) (V INTER IMAGE (e:real^3->B) s)`;
                          `{z:real^3 | z IN s /\ (e:real^3->B) z IN V}`;
                          `(e2:B->real^3) o chart_inv (V:B->bool,psi:B->real^3)`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    GEN_TAC THEN REWRITE_TAC[rfs_pullback; mpullback; o_THM] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `G:B->real^3^3`;
                   `(e:real^3->B) y`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

(* Entries of the metric at a point are continuous at time 0 from the left. *)

let P2BX2_UPTO_ENTRY_CONT = prove
 (`!top atlas a (g:real->B->real^3^3) x i j.
     rfs_flow_upto (top,atlas) a (&0) g /\ x IN topspace top /\
     1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
     ==> ?f. f real_continuous atreal (&0) /\ !t. t <= &0 ==> f t = g t x$i$j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfs_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `x:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `a:real`; `&0`;
                 `g:real->B->real^3^3`; `chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)`;
                 `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x`] RFA_UPTO_BOX) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `Gb:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\t. (Gb:real->real^3->real^3^3) t
                    (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x)$i$j` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`ball(SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x,d)`;
                   `&0 - d`; `&0 + d`;
                   `\t z. (Gb:real->real^3->real^3^3) t z$i$j`; `&0`;
                   `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x`]
                  P2BX0_LSMOOTH_TCONT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[CENTRE_IN_BALL; OPEN_BALL] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MP_TAC(ISPECL [`interval(lift(&0 - d),lift(&0 + d)) PCROSS
                    ball(SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x,d)`;
                   `\z:real^(1,3)finite_sum.
                       (Gb:real->real^3->real^3^3) (drop(fstcart z)) (sndcart z)`]
                  LRG_SMOOTH_VECTORIZE) THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ANTS_TAC THENL
     [UNDISCH_TAC `lrg_lsmooth (ball(SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x,d))
                     (&0 - d) (&0 + d) (Gb:real->real^3->real^3^3)` THEN
      REWRITE_TAC[lrg_lsmooth; o_DEF] THEN SIMP_TAC[];
      DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ASM_REWRITE_TAC[DIMINDEX_3]];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Gb:real->real^3->real^3^3) t =
                  metric_local atlas (chart_at atlas (x:B)) ((g:real->B->real^3^3) t)`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) t`; `x:B`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

(* The model of a shift g(t + s0) makes t |-> g(t)(x) affine on (-inf,s0]. *)

let P2BX2_AFFINE_POINT = prove
 (`!top atlas (g:real->B->real^3^3) s0 x.
     smooth_manifold_atlas top atlas /\
     p2b_cyl_model (top,atlas) (\t. g(t + s0)) /\ x IN topspace top
     ==> ?H0 H1. !t. t <= s0 ==> g t x = H0 + t %% H1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_cyl_model] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->B` (X_CHOOSE_THEN `lam:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "loc")
      (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "pull"))))))) THEN
  SUBGOAL_THEN `?z:real^3. ~(z = vec 0) /\ (p:real^3->B) z = x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (p:real^3->B) {y | ~(y = vec 0)} = topspace top` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:B`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `~(z:real^3 = vec 0)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `ball(z:real^3,r)`; `p:real^3->B`; `z:real^3`] P2BX2_PULL_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
  ABBREV_TAC `J = matrix(frechet_derivative
                   (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) z)) o p)
                   (at z))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pt"))) THEN
  SUBGOAL_THEN
   `!t. t <= s0
        ==> transp J ** (g:real->B->real^3^3) t x ** J =
            p2bx2_cab (lam + s0) lam z + t %% p2bx2_cab (--(&1)) (&0) z`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "pull" (MP_TAC o SPECL [`t - s0`; `z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_ADD] THEN
    USE_THEN "pt" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[P2BX2_CAB_CYL; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[REAL_ARITH `lam - (t - s0) = (lam + s0) - t`] THEN REWRITE_TAC[P2BX2_CAB_SUB];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`transp(matrix_inv J) ** p2bx2_cab (lam + s0) lam z ** matrix_inv(J:real^3^3)`;
    `transp(matrix_inv J) ** p2bx2_cab (--(&1)) (&0) z ** matrix_inv(J:real^3^3)`] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM P2BX2_CONGR_AFFINE] THEN MATCH_MP_TAC P2BX2_CONGR_INV THEN
  ASM_SIMP_TAC[]);;

(* One model (at the shift -1) holds for all t <= 0. *)

let P2BX2_MODEL_EXTEND = prove
 (`!top atlas (g:real->B->real^3^3) (p:real^3->B) lam.
     (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
     (!s0. s0 < &0 ==> p2b_cyl_model (top,atlas) (\t. g(t + s0))) /\
     ~(lam = &0) /\
     IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top /\
     (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
     (!t y. t <= &0 /\ ~(y = vec 0)
            ==> rfs_pullback atlas p (g(t + --(&1))) y = lam %% cylinder_flow (t / lam) y)
     ==> !t y. t <= &0 /\ ~(y = vec 0)
               ==> rfs_pullback atlas p (g t) y = p2bx2_cab (lam - (t + &1)) lam y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "upto") (CONJUNCTS_THEN2 (LABEL_TAC "mod")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "loc") (LABEL_TAC "pull")))))) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [USE_THEN "upto" (MP_TAC o SPEC `--(&1)`) THEN
    REWRITE_TAC[REAL_ARITH `--(&1) < &0`; rfs_flow_upto; ricci_flow_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `~(y:real^3 = vec 0)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `ball(y:real^3,r)`; `p:real^3->B`; `y:real^3`] P2BX2_PULL_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
  ABBREV_TAC `J = matrix(frechet_derivative
                   (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) y)) o p)
                   (at y))` THEN
  ABBREV_TAC `x = (p:real^3->B) y` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pt"))) THEN
  SUBGOAL_THEN `?H0 H1. !u. u <= &0 ==> (g:real->B->real^3^3) u x = H0 + u %% H1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `\u. (g:real->B->real^3^3) u x` P2BX2_AFFINE_EXTEND) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC P2BX2_AFFINE_POINT THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "mod" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX2_UPTO_ENTRY_CONT THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `--(&1)`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "upto" MATCH_MP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`transp J ** (H0:real^3^3) ** (J:real^3^3)`;
                 `transp J ** (H1:real^3^3) ** (J:real^3^3)`;
                 `p2bx2_cab (lam - &1) lam y`; `p2bx2_cab (--(&1)) (&0) y`; `--(&1)`]
                P2BX2_AFFINE_UNIQUE) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM P2BX2_CONGR_AFFINE] THEN
    SUBGOAL_THEN `(H0:real^3^3) + u %% H1 = (g:real->B->real^3^3) u x` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "pt" (fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[ETA_AX] THEN
    USE_THEN "pull" (MP_TAC o SPECL [`u + &1`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(u + &1) + --(&1) = u`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[P2BX2_CAB_CYL] THEN
    REWRITE_TAC[REAL_ARITH `lam - (u + &1) = (lam - &1) - u`] THEN REWRITE_TAC[P2BX2_CAB_SUB];
    ALL_TAC] THEN
  STRIP_TAC THEN
  USE_THEN "pt" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `(g:real->B->real^3^3) t x = H0 + t %% H1` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[P2BX2_CONGR_AFFINE] THEN
  REWRITE_TAC[REAL_ARITH `lam - (t + &1) = (lam - &1) - t`] THEN REWRITE_TAC[P2BX2_CAB_SUB]);;

(* A pullback of a Riemannian metric equal to a cylinder-type field has a  *)
(* positive sphere coefficient.                                              *)

let P2BX2_CAB_POS = prove
 (`!top atlas (G:B->real^3^3) (p:real^3->B) A B y r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\
     ~(y = vec 0) /\ &0 < r /\ mfd_param top atlas (ball(y,r)) p /\
     rfs_pullback atlas p G y = p2bx2_cab A B y
     ==> &0 < A`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `ball(y:real^3,r)`; `p:real^3->B`; `y:real^3`] P2BX2_PULL_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
  ABBREV_TAC `J = matrix(frechet_derivative
                   (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) y)) o p)
                   (at y))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `G:B->real^3^3`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `y:real^3` ORTHOGONAL_TO_VECTOR_EXISTS) THEN
  REWRITE_TAC[DIMINDEX_3; orthogonal; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((J:real^3^3) ** v = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
    UNDISCH_TAC `~(v:real^3 = vec 0)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `v:real^3 = matrix_inv(J:real^3^3) ** J ** v` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (v:real^3) dot (p2bx2_cab A B y ** v)` MP_TAC THENL
   [FIRST_X_ASSUM(fun th -> REWRITE_TAC[check
      (fun th -> lhs(concl th) = `p2bx2_cab A B (y:real^3)`) th]) THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `G:B->real^3^3`;
                   `(p:real^3->B) y`] RIEMANNIAN_METRIC_POS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[P2BX2_CAB_TANGENT] THEN
  SUBGOAL_THEN `&0 < &2 / norm(y:real^3) pow 2 /\ &0 < (v:real^3) dot v` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; LRG_CYL_POS; DOT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `~(A <= &0) ==> &0 < A`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 / norm(y:real^3) pow 2 * A * ((v:real^3) dot v) <= &0` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= c * --A * d ==> c * A * d <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The radial power map corrects the line factor.  With one model p, lam     *)
(* (lam > 1) for all t <= 0, p o h is the cylinder model with parameter lam  *)
(* - 1, where h is the power map with (2e+1)^2 lam = lam - 1.                *)
(* ========================================================================= *)

let P2BX2_SIGMA_EXISTS = prove
 (`!lam. &1 < lam
         ==> ?h h'. diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0) h h' /\
                    (!y. ~(y = vec 0) ==> h(rfs_twist y) = rfs_twist(h y)) /\
                    (!A B y. ~(y = vec 0)
                             ==> mpullback h (p2bx2_cab A B) y =
                                 p2bx2_cab A ((lam - &1) / lam * B) y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `--(inv(lam - &1))` RFB_CYL_EXPONENT) THEN ANTS_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> --x < &1`) THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(&2 * e + &1) pow 2 = (lam - &1) / lam` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(lam - &1 = &0) /\ ~(lam = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(&2 * e + &1) pow 2 * (&1 - --inv (lam - &1)) = &1` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  EXISTS_TAC `\z:real^3. ((norm z pow 2) rpow e) % z` THEN
  EXISTS_TAC `\z:real^3. ((norm z pow 2) rpow (--e / (&2 * e + &1))) % z` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RFB_PW_DIFFEO THEN UNDISCH_TAC `&0 < &2 * e + &1` THEN CONV_TAC REAL_FIELD;
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC P2BX2_PW_TWIST THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[P2BX2_PW_PULLBACK_CAB]]);;

(* The pullback by a parametrization precomposed with a diffeomorphism of   *)
(* open sets.  A copy of APX_RFS_PULLBACK_PRECOMP (pc_apx_chain, which      *)
(* would add about 1 MB to the load closure), with APX_MPULLBACK_CHAIN      *)
(* replaced by the identical P2A_MPULLBACK_COMPOSE (pc_p2a_lgeo2).          *)

let P2BX2_RFS_PULLBACK_PRECOMP = prove
 (`!top atlas (g:A->real^N^N) s (e:real^N->A) t (h:real^N->real^N) h' v.
     smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\
     diffeomorphism_on t s h h' /\ v IN t
     ==> rfs_pullback atlas (e o h) g v = mpullback h (rfs_pullback atlas e g) v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^N) v IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on t s (h:real^N->real^N) h'` THEN
    REWRITE_TAC[diffeomorphism_on] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas t ((e:real^N->A) o (h:real^N->real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `s:real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^N->A)(h(v:real^N)) IN topspace top` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e:real^N->A)(h(v:real^N))`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A)(h(v:real^N)))`,
           `ch:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `t:real^N->bool`; `(e:real^N->A) o (h:real^N->real^N)`; `V:A->bool`;
                 `psi:A->real^N`; `v:real^N`] APX_RFS_PULLBACK_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[o_THM]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `rfs_pullback atlas (e:real^N->A) (g:A->real^N^N) (h(v:real^N)) =
                mpullback (psi o e) (metric_local atlas (V,psi) g) (h v)` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_CHART THEN EXISTS_TAC `top:A topology` THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mpullback (h:real^N->real^N) (rfs_pullback atlas (e:real^N->A) (g:A->real^N^N)) v =
                mpullback h (mpullback (psi o e) (metric_local atlas (V,psi) g)) v`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[mpullback]; ALL_TAC] THEN
  REWRITE_TAC[o_ASSOC] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_MPULLBACK_COMPOSE THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `t:real^N->bool` THEN
    UNDISCH_TAC `diffeomorphism_on t s (h:real^N->real^N) h'` THEN
    REWRITE_TAC[diffeomorphism_on] THEN SIMP_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`; `V:A->bool`; `psi:A->real^N`]
                APX_PARAM_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:A->real^N`
    (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) ASSUME_TAC)) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `{z | z IN s /\ (e:real^N->A) z IN V}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

(* Local facts of p o h at y: a ball parametrization of p at h y and a      *)
(* neighbourhood U of y that h maps diffeomorphically onto that ball.       *)

let P2BX2_SIGMA_LOCAL = prove
 (`!top atlas (p:real^3->B) (h:real^3->real^3) h' y.
     (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
     diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0) h h' /\
     ~(y = vec 0)
     ==> ?r1 U. &0 < r1 /\ mfd_param top atlas (ball(h y,r1)) p /\
                diffeomorphism_on U (ball(h y,r1)) h h' /\ open U /\ y IN U`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "loc") (CONJUNCTS_THEN2 (LABEL_TAC "dif") ASSUME_TAC)) THEN
  USE_THEN "dif" (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) THEN
  SUBGOAL_THEN `~((h:real^3->real^3) y = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (h:real^3->real^3) ((:real^3) DELETE vec 0) = (:real^3) DELETE vec 0` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `~((h:real^3->real^3) y = vec 0)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball((h:real^3->real^3) y,r1) SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; IN_DELETE; IN_UNIV] THEN X_GEN_TAC `w:real^3` THEN
    DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `dist((h:real^3->real^3) y,vec 0) < r1` THEN REWRITE_TAC[DIST_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r1:real`; `IMAGE (h':real^3->real^3) (ball((h:real^3->real^3) y,r1))`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `diffeomorphism_on (IMAGE (h':real^3->real^3) (ball((h:real^3->real^3) y,r1)))
                                  (ball(h y,r1)) h h'` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFEOMORPHISM_ON_SYM THEN MATCH_MP_TAC CMPH_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`(:real^3) DELETE vec 0`; `(:real^3) DELETE vec 0`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC DIFFEOMORPHISM_ON_SYM THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h:real^3->real^3) y` THEN
  ASM_SIMP_TAC[CENTRE_IN_BALL; IN_DELETE; IN_UNIV]);;

(* The model of g from one model with the wrong line factor. *)

let P2BX2_SIGMA_MODEL = prove
 (`!top atlas (g:real->B->real^3^3) (p:real^3->B) lam (h:real^3->real^3) h'.
     smooth_manifold_atlas top atlas /\ &1 < lam /\
     IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top /\
     (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
     ((!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)) \/
      (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y \/ z = rfs_twist y))) /\
     (!t y. t <= &0 /\ ~(y = vec 0)
            ==> rfs_pullback atlas p (g t) y = p2bx2_cab (lam - (t + &1)) lam y) /\
     diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0) h h' /\
     (!y. ~(y = vec 0) ==> h(rfs_twist y) = rfs_twist(h y)) /\
     (!A B y. ~(y = vec 0)
              ==> mpullback h (p2bx2_cab A B) y = p2bx2_cab A ((lam - &1) / lam * B) y)
     ==> p2b_cyl_model (top,atlas) g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "loc")
      (CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 (LABEL_TAC "pull")
        (CONJUNCTS_THEN2 (LABEL_TAC "dif") (CONJUNCTS_THEN2 (LABEL_TAC "tw")
          (LABEL_TAC "pb"))))))))) THEN
  USE_THEN "dif" (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) THEN
  SUBGOAL_THEN `!y:real^3. ~(y = vec 0) ==> ~((h:real^3->real^3) y = vec 0)` (LABEL_TAC "hnz")
  THENL
   [UNDISCH_TAC `IMAGE (h:real^3->real^3) ((:real^3) DELETE vec 0) = (:real^3) DELETE vec 0` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y z:real^3. ~(y = vec 0) /\ ~(z = vec 0)
                             ==> ((h:real^3->real^3) y = h z <=> y = z)` (LABEL_TAC "hinj")
  THENL
   [REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC `z:real^3` (ASSUME
      `!x. x IN (:real^3) DELETE vec 0 ==> (h':real^3->real^3) (h x) = x`)) THEN
    MP_TAC(SPEC `y:real^3` (ASSUME
      `!x. x IN (:real^3) DELETE vec 0 ==> (h':real^3->real^3) (h x) = x`)) THEN
    REWRITE_TAC[IN_DELETE; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(lam = &0) /\ ~(lam - &1 = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2b_cyl_model] THEN
  MAP_EVERY EXISTS_TAC [`(p:real^3->B) o (h:real^3->real^3)`; `lam - &1`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IMAGE_o] THEN
    SUBGOAL_THEN `IMAGE (h:real^3->real^3) {y | ~(y = vec 0)} = {y | ~(y = vec 0)}`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^3) ((:real^3) DELETE vec 0) = (:real^3) DELETE vec 0` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV; IN_ELIM_THM];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `p:real^3->B`;
                   `h:real^3->real^3`; `h':real^3->real^3`; `y:real^3`] P2BX2_SIGMA_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `U:real^3->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `?r0. &0 < r0 /\ ball(y:real^3,r0) SUBSET U` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `open(U:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    EXISTS_TAC `min r0 (norm(y:real^3) / &2)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ball(y:real^3,min r0 (norm y / &2)) SUBSET U` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y:real^3,r0)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`ball((h:real^3->real^3) y,r1)`;
                          `IMAGE (h:real^3->real^3) (ball(y,min r0 (norm y / &2)))`;
                          `h':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPH_DIFFEO_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `ball((h:real^3->real^3) y,r1)`] THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      SUBGOAL_THEN `IMAGE (h:real^3->real^3) U = ball(h y,r1)`
        (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THENL
       [UNDISCH_TAC `diffeomorphism_on U (ball((h:real^3->real^3) y,r1)) h h'` THEN
        SIMP_TAC[diffeomorphism_on];
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]];
    USE_THEN "inj" (DISJ_CASES_THEN (LABEL_TAC "pinj")) THENL
     [DISJ1_TAC THEN MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN STRIP_TAC THEN
      REWRITE_TAC[o_THM] THEN
      USE_THEN "pinj" (MP_TAC o SPECL [`(h:real^3->real^3) y`; `(h:real^3->real^3) z`]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN USE_THEN "hnz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "hinj" (MP_TAC o SPECL [`z:real^3`; `y:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])];
      DISJ2_TAC THEN MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN STRIP_TAC THEN
      REWRITE_TAC[o_THM] THEN
      USE_THEN "pinj" (MP_TAC o SPECL [`(h:real^3->real^3) y`; `(h:real^3->real^3) z`]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN USE_THEN "hnz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "tw" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `~(y:real^3 = vec 0)`))]) THEN
      MP_TAC(ISPEC `y:real^3` P2BX2_TWIST_NONZERO) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      USE_THEN "hinj" (MP_TAC o SPECL [`z:real^3`; `y:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
      USE_THEN "hinj" (MP_TAC o SPECL [`z:real^3`; `rfs_twist(y:real^3)`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])]];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `p:real^3->B`;
                   `h:real^3->real^3`; `h':real^3->real^3`; `y:real^3`] P2BX2_SIGMA_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `U:real^3->bool` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) t`; `ball((h:real^3->real^3) y,r1)`; `p:real^3->B`;
                   `U:real^3->bool`; `h:real^3->real^3`; `h':real^3->real^3`; `y:real^3`]
                  P2BX2_RFS_PULLBACK_PRECOMP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `rfs_pullback atlas (p:real^3->B) ((g:real->B->real^3^3) t) ((h:real^3->real^3) y) =
                  p2bx2_cab (lam - (t + &1)) lam (h y)` ASSUME_TAC THENL
     [USE_THEN "pull" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "hnz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mpullback (h:real^3->real^3)
                    (rfs_pullback atlas (p:real^3->B) ((g:real->B->real^3^3) t)) y =
                  mpullback h (p2bx2_cab (lam - (t + &1)) lam) y` SUBST1_TAC THENL
     [REWRITE_TAC[mpullback] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "pb" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~(y:real^3 = vec 0)`)]) THEN
    MP_TAC(ISPECL [`lam - &1`; `t:real`; `y:real^3`] P2BX2_CAB_CYL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN BINOP_TAC THENL
     [REAL_ARITH_TAC;
      UNDISCH_TAC `~(lam = &0)` THEN CONV_TAC REAL_FIELD]]);;

(* X2.6 The model at time 0 (MT Cor 9.52 for the based limit, whose time    *)
(* interval is closed at 0): from the models of all shifts g(t + s0), s0 < 0. *)

let P2BX2_MODEL_AT_ZERO = prove
 (`!top atlas (g:real->B->real^3^3).
     (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
     (!s0. s0 < &0 ==> p2b_cyl_model (top,atlas) (\t. g(t + s0)))
     ==> p2b_cyl_model (top,atlas) g`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "upto") (LABEL_TAC "mod")) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas ((g:real->B->real^3^3) (&0))` STRIP_ASSUME_TAC THENL
   [USE_THEN "upto" (MP_TAC o SPEC `--(&1)`) THEN
    REWRITE_TAC[REAL_ARITH `--(&1) < &0`; rfs_flow_upto; ricci_flow_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "mod" (MP_TAC o REWRITE_RULE[p2b_cyl_model] o
                  C MATCH_MP (REAL_ARITH `--(&1) < &0`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->B` (X_CHOOSE_THEN `lam:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "loc")
      (CONJUNCTS_THEN2 (LABEL_TAC "inj") (LABEL_TAC "pull"))))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `p:real^3->B`; `lam:real`] P2BX2_MODEL_EXTEND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_SIMP_TAC[REAL_LT_IMP_NZ]);
    DISCH_THEN(LABEL_TAC "ext")] THEN
  SUBGOAL_THEN `&1 < lam` ASSUME_TAC THENL
   [USE_THEN "loc" (MP_TAC o SPEC `basis 1:real^3`) THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (&0)`; `p:real^3->B`; `lam - (&0 + &1)`; `lam:real`;
                   `basis 1:real^3`; `r:real`] P2BX2_CAB_POS) THEN
    ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN ANTS_TAC THENL
     [USE_THEN "ext" MATCH_MP_TAC THEN SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH; REAL_LE_REFL];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `lam:real` P2BX2_SIGMA_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC P2BX2_SIGMA_MODEL THEN
  MAP_EVERY EXISTS_TAC [`p:real^3->B`; `lam:real`; `h:real^3->real^3`; `h':real^3->real^3`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ========================================================================= *)
(* The X0 limit is in the class on s < 0 and has p2b_lorient; SPLIT_ROUND on *)
(* s < 0 and the model at 0 give X2 (P2BX2_CYL_BODY) and the route           *)
(* P2BX2_CYL_ROUTE (FLAT_FORWARD is not needed: P2BX0_SCALAR_POS_ALL uses    *)
(* the proved flat-forward lemma).                                           *)
(* ========================================================================= *)

(* Kappa-noncollapsing of the view on s <= 0 gives it on s < 0. *)

let P2BX2_KNC_VIEW_MONO = prove
 (`!top atlas (g:real->B->real^3^3) kappa r0.
     rfs_kappa_noncollapsed (rfs_flow_view (top,atlas) {s | s <= &0} g) kappa r0
     ==> rfs_kappa_noncollapsed (rfs_flow_view (top,atlas) {s | s < &0} g) kappa r0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[rfs_kappa_noncollapsed; rfs_flow_view; rfs_parabolic_exists; rfs_persists;
              rfs_vball; IN_ELIM_THM] THEN
  DISCH_THEN(LABEL_TAC "knc") THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:B`; `r:real`] THEN
  ASM_CASES_TAC `t < &0` THEN ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "par") (LABEL_TAC "curv"))))) THEN
  REMOVE_THEN "knc" (MP_TAC o SPECL [`t:real`; `x:B`; `r:real`]) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `s <= &0 /\ s < &0` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "par" (MP_TAC o C MATCH_MP
    (CONJ (ASSUME `t - r pow 2 < s`) (ASSUME `s <= t`))) THEN
  ASM_REWRITE_TAC[]);;

(* The X0 limit is in the class on s < 0. *)

let P2BX2_LIMIT_CLASS = prove
 (`!kappa (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
             (real->A->real^3^3)) q t Q (top':B topology) atlas' g' xl W phi.
     &0 < kappa /\
     p2c_flow_limit_with V q t Q {s | s <= &0} (top',atlas') g' xl W phi /\
     connected_space top' /\
     (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
     (!s. s <= &0 ==> mfd_complete (top',atlas') (g' s)) /\
     (!s y u v. s <= &0 /\ y IN topspace top' /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas' (g' s) y u v) /\
     mfd_scalar atlas' (g'(&0)) xl = &1 /\
     (?K. !s y. s <= &0 /\ y IN topspace top' ==> mfd_rm_norm atlas' (g' s) y <= K) /\
     (!r0. rfs_kappa_noncollapsed (rfs_flow_view (top',atlas') {s | s <= &0} g') kappa r0) /\
     (!s y dR. s <= &0 /\ y IN topspace top' /\
               ((\t. mfd_scalar atlas' (g' t) y) has_real_derivative dR) (atreal s)
               ==> &0 <= dR)
     ==> p2b_ancflow0 kappa (top',atlas') g' (&0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lim")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "upto")
      (CONJUNCTS_THEN2 (LABEL_TAC "comp") (CONJUNCTS_THEN2 (LABEL_TAC "sec")
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `K:real`)
          (CONJUNCTS_THEN2 (LABEL_TAC "knc") (LABEL_TAC "drds")))))))))) THEN
  USE_THEN "lim" (STRIP_ASSUME_TAC o REWRITE_RULE[p2c_flow_limit_with]) THEN
  REWRITE_TAC[p2b_ancflow0] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    REPEAT STRIP_TAC THEN
    USE_THEN "upto" (MP_TAC o C MATCH_MP (ASSUME `a < &0`)) THEN SIMP_TAC[rfs_flow_upto];
    REPEAT STRIP_TAC THEN USE_THEN "comp" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `g':real->B->real^3^3`; `xl:B`; `K:real`] P2BX0_SCALAR_POS_ALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`s:real`; `xl:B`]) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
    USE_THEN "upto" (MP_TAC o SPEC `s - &1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[rfs_flow_upto; ricci_flow_on]] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(g':real->B->real^3^3) s`; `xl:B`;
                   `mfd_rm_norm atlas' ((g':real->B->real^3^3) s) xl`]
                  P2BFF_MFD_SCALAR_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN USE_THEN "drds" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:real`; `x:B`] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    GEN_TAC THEN MATCH_MP_TAC P2BX2_KNC_VIEW_MONO THEN USE_THEN "knc" (fun th -> REWRITE_TAC[th])]);;

(* The X0 limit has orientable relatively compact open sets. *)

let P2BX2_LIMIT_LORIENT = prove
 (`!top atlas (g:real->B->real^3^3) b s0 q Q (top':B topology) atlas' g' xl W phi.
     hausdorff_space top /\ p2b_ksep top atlas /\ smooth_manifold_atlas top atlas /\ s0 < b /\
     p2c_flow_limit_with (\k. rfs_flow_view (top,atlas) {s | s < b} g) q (\k. s0) Q
                         {s | s <= &0} (top',atlas') g' xl W phi
     ==> p2b_lorient top' atlas'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. &0 < (Q:num->real) k` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2c_flow_limit_with]; ALL_TAC] THEN
  SUBGOAL_THEN `p2b_ksep (top':B topology) atlas'` MP_TAC THENL
   [MATCH_MP_TAC P2B_KSEP_LIMIT_DIRECT THEN
    MAP_EVERY EXISTS_TAC [`\k:num. top:B topology`;
                          `\k:num. atlas:((B->bool)#(B->real^3))->bool`;
                          `\k:num t. (g:real->B->real^3^3)(t + s0)`; `q:num->B`;
                          `\k:num. &0`; `Q:num->real`; `g':real->B->real^3^3`; `xl:B`;
                          `{s:real | s <= &0}`] THEN
    ASM_REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN
    MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->B`] THEN
    MATCH_MP_TAC P2BX0_FLOW_LIMIT_WITH_CONG THEN
    MAP_EVERY EXISTS_TAC [`\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`;
                          `\k:num. (s0:real)`] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`k:num`; `s:real`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `s / (Q:num->real) k <= &0` ASSUME_TAC THENL
     [REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= --s * i ==> s * i <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[REAL_ADD_LID] THEN
    ASM_SIMP_TAC[REAL_ARITH `x <= &0 /\ s0 < b ==> s0 + x < b`] THEN
    REWRITE_TAC[REAL_ADD_SYM];
    SIMP_TAC[p2b_ksep]]);;

(* X2 from X0 and SPLIT_ROUND. *)

let P2BX2_CYL_BODY = prove
 (`!w:B->bool.
     P2B_SPLIT_AT_INFINITY_STATEMENT w /\ P2B_SPLIT_ROUND_STATEMENT w
     ==> P2B_CYL_AT_INFINITY_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_SPLIT_AT_INFINITY_STATEMENT; P2B_SPLIT_ROUND_STATEMENT;
              P2B_CYL_AT_INFINITY_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "x0") (LABEL_TAC "sr")) THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `b:real`; `s0:real`; `p:B`; `pp:num->B`] THEN
  REWRITE_TAC[p2b_ancflow] THEN STRIP_TAC THEN
  USE_THEN "x0" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                                 `b:real`; `s0:real`; `p:B`; `pp:num->B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `q:num->B`
    (X_CHOOSE_THEN `top':B topology` (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `xl:B`
    (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B`
    (X_CHOOSE_THEN `X:B->real^3` STRIP_ASSUME_TAC))))))))) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `q:num->B`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                        `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `b:real`] P2BX0_ANC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2b_ancflow0 kappa (top':B topology,atlas') g' (&0)` ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:B`,`:A`] P2BX2_LIMIT_CLASS) THEN
    MAP_EVERY EXISTS_TAC [`\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`;
                          `q:num->B`; `\k:num. (s0:real)`;
                          `\k:num. mfd_scalar atlas ((g:real->B->real^3^3) s0) (q k)`;
                          `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `p2b_ancflow0 kappa (top,atlas) (g:real->B->real^3^3) b` THEN
      SIMP_TAC[p2b_ancflow0];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_lorient (top':B topology) atlas'` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX2_LIMIT_LORIENT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:real->B->real^3^3`; `b:real`; `s0:real`; `q:num->B`;
                          `\k:num. mfd_scalar atlas ((g:real->B->real^3^3) s0) (q k)`;
                          `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`;
                          `phi:num->B->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_gsplit (top':B topology,atlas') g' {s | s < &0} X` ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_gsplit (top':B topology,atlas') g' {s | s <= &0} X` THEN
    REWRITE_TAC[p2b_gsplit; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BX2_MODEL_AT_ZERO THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "sr" (MP_TAC o SPECL [`kappa:real`; `top':B topology`;
                                 `atlas':((B->bool)#(B->real^3))->bool`;
                                 `g':real->B->real^3^3`; `&0`; `X:B->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* The route: FLAT_FORWARD is not used. *)

let P2BX2_CYL_ROUTE = prove
 (`!w:B->bool. P2B_CYL_AT_INFINITY_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_CYL_AT_INFINITY_ROUTE_STATEMENT] THEN
  STRIP_TAC THEN MATCH_MP_TAC P2BX2_CYL_BODY THEN ASM_REWRITE_TAC[]);;


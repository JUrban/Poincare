(* ========================================================================= *)
(* Unit pc_cm_lemma122: the chain statement                                 *)
(* CM_CHAIN_CM_LEMMA122_STATEMENT of pc_cm_stmts, i.e. CM Lemma 1.22        *)
(* (Colding-Minicozzi 2008): for a harmonic sphere v in a component U of a  *)
(* closed Riemannian 3-manifold with scalar curvature >= r0 on U,           *)
(*   4 pi + (r0 / 2) Area(v) <= int_v tr(Ric).                              *)
(* Route: stereographic coordinates z on S^2;                               *)
(* the Euler-Lagrange equation in charts from p4_harmonic_sphere; Hopf and  *)
(* Liouville give conformality, the pullback metric is lam |dz|^2; the      *)
(* Bochner identity and a Kato inequality for conformal harmonic maps give  *)
(* Lap lam = B - 2K, |grad lam|^2 <= lam B, B >= 0, with                    *)
(* K = Rm(e,f,f,e) = lam (Ric(e,e) + Ric(f,f)) - lam^2 Scal / 2.  For the   *)
(* smooth metric lam + delta rho1 (rho1 a round factor) Gauss-Bonnet (Green *)
(* on discs, flux at infinity) and delta -> 0 (dominated convergence) give  *)
(* 4 pi <= int_{lam > 0} K / lam + int_{lam = 0} rho1; letting rho1         *)
(* concentrate at a point where lam > 0 (a nonconstant map has one) kills   *)
(* the last term, so no unique continuation is needed.  The S^2 integrals   *)
(* move to the plane by CML_S2_TRANSFER.  Headline theorems (at the end):   *)
(* CML_HARMONIC_SPHERE |- CM_HARMONIC_SPHERE_STATEMENT (:A) and             *)
(* CM_CHAIN_CM_LEMMA122 |- !aa. CM_CHAIN_CM_LEMMA122_STATEMENT aa; the      *)
(* hypothesis WAN_CAUCHY_HOLDER of the chain statement is not used.         *)
(* ========================================================================= *)

needs "src/pc_cm_stmts.ml";;
needs "src/pc_p4_width.ml";;
needs "src/pc_an_beltrami.ml";;
needs "src/pc_cmp_comm.ml";;
needs "src/pc_cm_target.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* A small planar calculus kit for real functions on real^2 (partials in    *)
(* drop form, Laplacian, squared gradient, the round conformal factor, the  *)
(* inversion z |-> z / |z|^2), smoothness of real combinations, and partial *)
(* derivatives computed along lines.                                        *)
(* ========================================================================= *)

let cml_rho = new_definition
 `cml_rho (z:real^2) = &4 / (norm z pow 2 + &1) pow 2`;;

let cml_inv = new_definition
 `cml_inv (z:real^2) = inv(norm z pow 2) % z`;;

let cml_d = new_definition
 `cml_d (i:num) (u:real^2->real) (z:real^2) =
    drop(partial_derivative i (\x. lift(u x)) z)`;;

let cml_lap = new_definition
 `cml_lap (u:real^2->real) (z:real^2) =
    cml_d 1 (cml_d 1 u) z + cml_d 2 (cml_d 2 u) z`;;

let cml_grad2 = new_definition
 `cml_grad2 (u:real^2->real) (z:real^2) = cml_d 1 u z pow 2 + cml_d 2 u z pow 2`;;

(* Smoothness of real combinations.                                          *)

let CML_SM_CONST = prove
 (`!s c. smooth_map_on (s:real^N->bool) (\x. lift c)`,
  REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let CML_SM_ADD = prove
 (`!s (u:real^N->real) w.
        open s /\ smooth_map_on s (\x. lift(u x)) /\ smooth_map_on s (\x. lift(w x))
        ==> smooth_map_on s (\x. lift(u x + w x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(u x)`; `\x:real^N. lift(w x)`]
                SMOOTH_MAP_ON_LIFT_ADD) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let CML_SM_SUB = prove
 (`!s (u:real^N->real) w.
        open s /\ smooth_map_on s (\x. lift(u x)) /\ smooth_map_on s (\x. lift(w x))
        ==> smooth_map_on s (\x. lift(u x - w x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(u x)`; `\x:real^N. lift(w x)`]
                SMOOTH_MAP_ON_LIFT_SUB) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let CML_SM_MUL = prove
 (`!s (u:real^N->real) w.
        open s /\ smooth_map_on s (\x. lift(u x)) /\ smooth_map_on s (\x. lift(w x))
        ==> smooth_map_on s (\x. lift(u x * w x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(u x)`; `\x:real^N. lift(w x)`]
                SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let CML_SM_DIV = prove
 (`!s (u:real^N->real) w.
        open s /\ smooth_map_on s (\x. lift(u x)) /\ smooth_map_on s (\x. lift(w x)) /\
        (!x. x IN s ==> ~(w x = &0))
        ==> smooth_map_on s (\x. lift(u x / w x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(u x)`; `\x:real^N. lift(w x)`]
                SMOOTH_MAP_ON_LIFT_DIV) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

let CML_SM_POW = prove
 (`!s (u:real^N->real) n.
        open s /\ smooth_map_on s (\x. lift(u x))
        ==> smooth_map_on s (\x. lift(u x pow n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(u x)`; `n:num`]
                SMOOTH_MAP_ON_LIFT_POW) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let CML_SM_LOG = prove
 (`!s (u:real^N->real).
        open s /\ smooth_map_on s (\x. lift(u x)) /\ (!x. x IN s ==> &0 < u x)
        ==> smooth_map_on s (\x. lift(log(u x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(u x)`] SMOOTH_MAP_ON_LIFT_LOG) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

let CML_SM_CMUL = prove
 (`!s c (u:real^N->real).
        open s /\ smooth_map_on s (\x. lift(u x))
        ==> smooth_map_on s (\x. lift(c * u x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c:real`; `\x:real^N. lift(u x)`]
                SMOOTH_MAP_ON_LIFT_CMUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let CML_SM_COORD = prove
 (`!s k. open s ==> smooth_map_on (s:real^N->bool) (\x. lift(x$k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. x`; `k:num`] SMOOTH_MAP_ON_LIFT_COMPONENT) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]);;

let CML_SM_NORM2 = prove
 (`!s. open s ==> smooth_map_on (s:real^N->bool) (\x. lift(norm x pow 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. x`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]);;

let CML_SM_DIFF = prove
 (`!s (u:real^N->real) z.
        open s /\ smooth_map_on s (\x. lift(u x)) /\ z IN s
        ==> (\x. lift(u x)) differentiable (at z)`,
  MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE]);;

let CML_D_SMOOTH = prove
 (`!s (u:real^2->real) i.
        open s /\ smooth_map_on s (\x. lift(u x))
        ==> smooth_map_on s (\x. lift(cml_d i u x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_d; LIFT_DROP; ETA_AX] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[]);;

(* Partial derivatives along lines.                                         *)

let CML_LINE_DERIV = prove
 (`!(u:real^2->real) z i.
        (\x. lift(u x)) differentiable (at z)
        ==> ((\t. u(z + t % basis i)) has_real_derivative cml_d i u z) (atreal (&0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  SUBGOAL_THEN
   `(lift o (\t. (u:real^2->real)(z + t % basis i)) o drop) =
    (\x. lift(u x)) o (\x:real^1. z + drop x % basis i)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^1. cml_d i (u:real^2->real) z % x) =
    frechet_derivative (\x. lift(u x)) (at z) o (\x:real^1. drop x % basis i)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `x:real^1` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
    REWRITE_TAC[cml_d; partial_derivative] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:real^1. drop x % basis i:real^2) = (\x. vec 0 + drop x % basis i)`
    SUBST1_TAC THENL [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID; LIFT_NUM] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

let CML_PARTIAL_LINE = prove
 (`!(u:real^2->real) z i d.
        (\x. lift(u x)) differentiable (at z) /\
        ((\t. u(z + t % basis i)) has_real_derivative d) (atreal (&0))
        ==> cml_d i u z = d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\t. (u:real^2->real)(z + t % basis i)`; `&0`] THEN
  ASM_SIMP_TAC[CML_LINE_DERIV]);;

(* ========================================================================= *)
(* Derivative rules for cml_d, the log Laplacian, and the round conformal   *)
(* factor rho = 4 / (|z|^2 + 1)^2: smooth, positive, rho(z / |z|^2) = |z|^4 *)
(* rho(z), and rho Lap rho - |grad rho|^2 = -2 rho^3 (curvature 1).         *)
(* ========================================================================= *)

let CML_D_ADD = prove
 (`!s (u:real^2->real) w z i.
     open s /\ smooth_map_on s (\x. lift(u x)) /\ smooth_map_on s (\x. lift(w x)) /\
     z IN s
     ==> cml_d i (\x. u x + w x) z = cml_d i u z + cml_d i w z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_PARTIAL_LINE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_DIFF THEN EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[CML_SM_ADD];
    REWRITE_TAC[] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC CML_LINE_DERIV THEN ASM_MESON_TAC[CML_SM_DIFF]]);;

let CML_D_SUB = prove
 (`!s (u:real^2->real) w z i.
     open s /\ smooth_map_on s (\x. lift(u x)) /\ smooth_map_on s (\x. lift(w x)) /\
     z IN s
     ==> cml_d i (\x. u x - w x) z = cml_d i u z - cml_d i w z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_PARTIAL_LINE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_DIFF THEN EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[CML_SM_SUB];
    REWRITE_TAC[] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC CML_LINE_DERIV THEN ASM_MESON_TAC[CML_SM_DIFF]]);;

let CML_D_MUL = prove
 (`!s (u:real^2->real) w z i.
     open s /\ smooth_map_on s (\x. lift(u x)) /\ smooth_map_on s (\x. lift(w x)) /\
     z IN s
     ==> cml_d i (\x. u x * w x) z = u z * cml_d i w z + cml_d i u z * w z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_PARTIAL_LINE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_DIFF THEN EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[CML_SM_MUL];
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\t. (u:real^2->real)(z + t % basis i)`; `cml_d i (u:real^2->real) z`;
                   `\t. (w:real^2->real)(z + t % basis i)`; `cml_d i (w:real^2->real) z`;
                   `&0`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC CML_LINE_DERIV THEN ASM_MESON_TAC[CML_SM_DIFF]]);;

let CML_D_CMUL = prove
 (`!s c (u:real^2->real) z i.
     open s /\ smooth_map_on s (\x. lift(u x)) /\ z IN s
     ==> cml_d i (\x. c * u x) z = c * cml_d i u z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_PARTIAL_LINE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_DIFF THEN EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[CML_SM_CMUL];
    REWRITE_TAC[] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    MATCH_MP_TAC CML_LINE_DERIV THEN ASM_MESON_TAC[CML_SM_DIFF]]);;

let CML_D_DIV = prove
 (`!s (u:real^2->real) w z i.
     open s /\ smooth_map_on s (\x. lift(u x)) /\ smooth_map_on s (\x. lift(w x)) /\
     (!x. x IN s ==> ~(w x = &0)) /\ z IN s
     ==> cml_d i (\x. u x / w x) z =
         (cml_d i u z * w z - u z * cml_d i w z) / w z pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_PARTIAL_LINE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_DIFF THEN EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[CML_SM_DIV];
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\t. (u:real^2->real)(z + t % basis i)`; `cml_d i (u:real^2->real) z`;
                   `\t. (w:real^2->real)(z + t % basis i)`; `cml_d i (w:real^2->real) z`;
                   `&0`] HAS_REAL_DERIVATIVE_DIV_ATREAL) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC CML_LINE_DERIV THEN ASM_MESON_TAC[CML_SM_DIFF]]);;

let CML_D_LOG = prove
 (`!s (u:real^2->real) z i.
     open s /\ smooth_map_on s (\x. lift(u x)) /\ (!x. x IN s ==> &0 < u x) /\ z IN s
     ==> cml_d i (\x. log(u x)) z = cml_d i u z / u z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_PARTIAL_LINE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_DIFF THEN EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[CML_SM_LOG];
    REWRITE_TAC[] THEN
    MP_TAC(INST [`inv:real->real`,`g':real->real`; `cml_d i (u:real^2->real) z`,`f':real`]
      (ISPECL [`\x. &0 < x`; `\t. (u:real^2->real)(z + t % basis i)`; `log`]
              HAS_REAL_DERIVATIVE_CHAIN)) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_LOG] THEN
    DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT2) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    ASM_SIMP_TAC[real_div] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC CML_LINE_DERIV THEN ASM_MESON_TAC[CML_SM_DIFF]]);;

let CML_D_CONST = prove
 (`!c z i. cml_d i (\x:real^2. c) z = &0`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CML_PARTIAL_LINE THEN
  REWRITE_TAC[DIFFERENTIABLE_CONST; HAS_REAL_DERIVATIVE_CONST]);;

(* Partial derivatives only see a neighbourhood.                            *)

let CML_D_LOCAL = prove
 (`!s (u:real^2->real) w z i.
     open s /\ z IN s /\ (!x. x IN s ==> u x = w x)
     ==> cml_d i u z = cml_d i w z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_d; partial_derivative] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN REWRITE_TAC[frechet_derivative] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THENL
   [EXISTS_TAC `\x. lift((u:real^2->real) x)`; EXISTS_TAC `\x. lift((w:real^2->real) x)`] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[LIFT_EQ] THEN
  ASM_MESON_TAC[DIST_SYM]);;

(* The Laplacian of log mu.                                                  *)

let CML_LAP_LOG = prove
 (`!s (u:real^2->real) z.
     open s /\ smooth_map_on s (\x. lift(u x)) /\ (!x. x IN s ==> &0 < u x) /\ z IN s
     ==> cml_lap (\x. log(u x)) z = (u z * cml_lap u z - cml_grad2 u z) / u z pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. cml_d i (cml_d i (\x. log((u:real^2->real) x))) z =
                    cml_d i (\x. cml_d i u x / u x) z`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CML_D_LOCAL THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_D_LOG THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. cml_d i (\x. cml_d i (u:real^2->real) x / u x) z =
                    (cml_d i (cml_d i u) z * u z - cml_d i u z * cml_d i u z) / u z pow 2`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `\x. cml_d i (u:real^2->real) x`; `u:real^2->real`;
                   `z:real^2`; `i:num`] CML_D_DIV) THEN
    ASM_SIMP_TAC[CML_D_SMOOTH; REAL_LT_IMP_NZ; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[cml_lap; cml_grad2] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((u:real^2->real) z = &0)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD]);;

(* ========================================================================= *)
(* The round conformal factor rho = 4 / (|z|^2 + 1)^2: smooth, positive,    *)
(* rho(z / |z|^2) = |z|^4 rho(z), its partials, and rho Lap rho - |grad     *)
(* rho|^2 = -2 rho^3.                                                       *)
(* ========================================================================= *)

let CML_NORM2_LINE = prove
 (`!(z:real^2) t i.
     1 <= i /\ i <= 2
     ==> norm(z + t % basis i) pow 2 = norm z pow 2 + &2 * t * z$i + t pow 2 /\
         (z + t % basis i)$i = z$i + t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  ASM_SIMP_TAC[DOT_BASIS; BASIS_COMPONENT; DIMINDEX_2] THEN REAL_ARITH_TAC);;

let CML_NORM2_POS = prove
 (`!z:real^2. &0 < norm z pow 2 + &1`,
  GEN_TAC THEN MP_TAC(SPEC `norm(z:real^2)` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let CML_RHO_SMOOTH = prove
 (`smooth_map_on (:real^2) (\z. lift(cml_rho z))`,
  REWRITE_TAC[cml_rho] THEN MATCH_MP_TAC CML_SM_DIV THEN
  REWRITE_TAC[OPEN_UNIV; CML_SM_CONST; IN_UNIV] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_POW THEN REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC CML_SM_ADD THEN SIMP_TAC[OPEN_UNIV; CML_SM_NORM2; CML_SM_CONST];
    X_GEN_TAC `y:real^2` THEN MATCH_MP_TAC REAL_POW_NZ THEN
    MP_TAC(SPEC `y:real^2` CML_NORM2_POS) THEN REAL_ARITH_TAC]);;

let CML_RHO_POS = prove
 (`!z. &0 < cml_rho z`,
  GEN_TAC THEN REWRITE_TAC[cml_rho] THEN MATCH_MP_TAC REAL_LT_DIV THEN
  SIMP_TAC[REAL_POW_LT; CML_NORM2_POS] THEN REAL_ARITH_TAC);;

let CML_INV_NORM = prove
 (`!z:real^2. ~(z = vec 0) ==> norm(cml_inv z) = inv(norm z) /\ ~(cml_inv z = vec 0) /\
                               cml_inv(cml_inv z) = z`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:real^2)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(cml_inv z) = inv(norm(z:real^2))` ASSUME_TAC THENL
   [REWRITE_TAC[cml_inv; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    UNDISCH_TAC `&0 < norm(z:real^2)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[REAL_INV_EQ_0] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[cml_inv; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM;
                VECTOR_MUL_ASSOC] THEN
    MATCH_MP_TAC(MESON[VECTOR_MUL_LID] `a = &1 ==> a % (z:real^2) = z`) THEN
    UNDISCH_TAC `&0 < norm(z:real^2)` THEN CONV_TAC REAL_FIELD]);;

let CML_RHO_INV = prove
 (`!z:real^2. ~(z = vec 0) ==> cml_rho(cml_inv z) = norm z pow 4 * cml_rho z`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP CML_INV_NORM) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[cml_rho] THEN
  SUBGOAL_THEN `&0 < norm(z:real^2)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm(z:real^2)) pow 2 + &1 = (norm z pow 2 + &1) / norm z pow 2`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < norm(z:real^2)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(SPEC `z:real^2` CML_NORM2_POS) THEN UNDISCH_TAC `&0 < norm(z:real^2)` THEN
  CONV_TAC REAL_FIELD);;

let CML_RHO_D = prove
 (`!z:real^2 i. 1 <= i /\ i <= 2
                ==> cml_d i cml_rho z = --(&16 * z$i) / (norm z pow 2 + &1) pow 3`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_PARTIAL_LINE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_DIFF THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV; CML_RHO_SMOOTH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[cml_rho; CML_NORM2_LINE] THEN
  MP_TAC(SPEC `z:real^2` CML_NORM2_POS) THEN DISCH_TAC THEN
  REAL_DIFF_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_ADD_RID] THEN
  UNDISCH_TAC `&0 < norm(z:real^2) pow 2 + &1` THEN CONV_TAC REAL_FIELD);;

let CML_RHO_DD = prove
 (`!z:real^2 i.
     1 <= i /\ i <= 2
     ==> cml_d i (cml_d i cml_rho) z =
         (--(&16) * (norm z pow 2 + &1) + &96 * z$i pow 2) / (norm z pow 2 + &1) pow 4`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_PARTIAL_LINE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_DIFF THEN EXISTS_TAC `(:real^2)` THEN
    SIMP_TAC[OPEN_UNIV; IN_UNIV; CML_RHO_SMOOTH; CML_D_SMOOTH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CML_RHO_D; CML_NORM2_LINE] THEN
  MP_TAC(SPEC `z:real^2` CML_NORM2_POS) THEN DISCH_TAC THEN
  REAL_DIFF_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_ADD_RID] THEN
  UNDISCH_TAC `&0 < norm(z:real^2) pow 2 + &1` THEN CONV_TAC REAL_FIELD);;

let CML_RHO_IDENT = prove
 (`!z:real^2. cml_rho z * cml_lap cml_rho z - cml_grad2 cml_rho z = --(&2) * cml_rho z pow 3`,
  GEN_TAC THEN REWRITE_TAC[cml_lap; cml_grad2] THEN
  SIMP_TAC[CML_RHO_D; CML_RHO_DD; ARITH] THEN REWRITE_TAC[cml_rho] THEN
  SUBGOAL_THEN `norm(z:real^2) pow 2 = z$1 pow 2 + z$2 pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `z:real^2` CML_NORM2_POS) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The pointwise inequality for the regularized factor lam + delta rho,     *)
(* components of Frechet derivatives, and the Green formula on discs:       *)
(* int_B(0,R) Lap u = flux of grad u through the circle (from               *)
(* GREEN_THEOREM_CURL of 100/green.ml).                                     *)
(* ========================================================================= *)

(* The pointwise algebra.  With B >= 0, Lap lam = B - 2K,                   *)
(* |grad lam|^2 <= lam B and rho Lap rho - |grad rho|^2 = -2 rho^3, the     *)
(* factor mu = lam + delta rho satisfies                                     *)
(* mu Lap mu - |grad mu|^2 >= -2 mu (K + delta rho^2).                       *)

let CML_PT_ALG = prove
 (`!lam rho dl1 dl2 dr1 dr2 lapr K B delta.
     &0 <= lam /\ &0 < rho /\ &0 < delta /\ &0 <= B /\
     dl1 pow 2 + dl2 pow 2 <= lam * B /\
     rho * lapr - (dr1 pow 2 + dr2 pow 2) = --(&2) * rho pow 3
     ==> --(&2) * (lam + delta * rho) * (K + delta * rho pow 2)
         <= (lam + delta * rho) * ((B - &2 * K) + delta * lapr) -
            ((dl1 + delta * dr1) pow 2 + (dl2 + delta * dr2) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= rho pow 2 * B + lam * (dr1 pow 2 + dr2 pow 2) -
                     &2 * rho * (dl1 * dr1 + dl2 * dr2)`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `lam = &0` THENL
     [SUBGOAL_THEN `dl1 pow 2 = &0 /\ dl2 pow 2 = &0` MP_TAC THENL
       [MP_TAC(SPEC `dl1:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `dl2:real` REAL_LE_POW_2) THEN
        UNDISCH_TAC `dl1 pow 2 + dl2 pow 2 <= lam * B` THEN
        ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ] THEN STRIP_TAC] THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID; REAL_SUB_RZERO] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[GSYM(MATCH_MP (CONJUNCT1 REAL_LE_MUL_EQ) (ASSUME `&0 < lam`))] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(rho * dl1 - lam * dr1) pow 2 + (rho * dl2 - lam * dr2) pow 2` THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
      SUBGOAL_THEN `rho pow 2 * (dl1 pow 2 + dl2 pow 2) <= rho pow 2 * (lam * B)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho * (lam * lapr + rho * B - &2 * (dl1 * dr1 + dl2 * dr2) +
                       &2 * lam * rho pow 2) =
                rho pow 2 * B + lam * (dr1 pow 2 + dr2 pow 2) -
                &2 * rho * (dl1 * dr1 + dl2 * dr2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `lam * (rho * lapr - (dr1 pow 2 + dr2 pow 2)) = lam * (--(&2) * rho pow 3)`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= delta * (lam * lapr + rho * B - &2 * (dl1 * dr1 + dl2 * dr2) +
                               &2 * lam * rho pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM(MATCH_MP (CONJUNCT1 REAL_LE_MUL_EQ) (ASSUME `&0 < rho`))] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `delta pow 2 * (rho * lapr - (dr1 pow 2 + dr2 pow 2) + &2 * rho pow 3) = &0`
  MP_TAC THENL
   [SUBGOAL_THEN `rho * lapr - (dr1 pow 2 + dr2 pow 2) + &2 * rho pow 3 = &0`
    (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
    UNDISCH_TAC `rho * lapr - (dr1 pow 2 + dr2 pow 2) = --(&2) * rho pow 3` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&0 <= delta * (lam * lapr + rho * B - &2 * (dl1 * dr1 + dl2 * dr2) +
                              &2 * lam * rho pow 2)` THEN
  UNDISCH_TAC `dl1 pow 2 + dl2 pow 2 <= lam * B` THEN
  REAL_ARITH_TAC);;

(* Components of Frechet derivatives.                                      *)

let CML_FRECHET_COMPONENT = prove
 (`!(f:real^2->real^N) z h k.
     1 <= k /\ k <= dimindex(:N) /\ f differentiable (at z)
     ==> (frechet_derivative f (at z) h)$k =
         drop(frechet_derivative (\x. lift(f x$k)) (at z) h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_DERIVATIVE_COMPONENTWISE_AT] o
              GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
  DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[LIFT_DROP]);;

let CML_SM_NEG = prove
 (`!s (u:real^N->real).
        open s /\ smooth_map_on s (\x. lift(u x))
        ==> smooth_map_on s (\x. lift(--(u x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `--(&1)`; `u:real^N->real`] CML_SM_CMUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID]);;

let CML_D_NEG = prove
 (`!s (u:real^2->real) z i.
     open s /\ smooth_map_on s (\x. lift(u x)) /\ z IN s
     ==> cml_d i (\x. --(u x)) z = --(cml_d i u z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `--(&1)`; `u:real^2->real`; `z:real^2`; `i:num`]
                CML_D_CMUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID]);;

(* The flux integrand of grad u through the circle of radius R.            *)

let cml_flux = new_definition
 `cml_flux (u:real^2->real) R =
    drop(integral (interval[vec 0,vec 1])
           (\t. lift(cml_d 1 u (circlepath(vec 0,R) t) *
                     vector_derivative (circlepath(vec 0,R)) (at t)$2 -
                     cml_d 2 u (circlepath(vec 0,R) t) *
                     vector_derivative (circlepath(vec 0,R)) (at t)$1)))`;;

let CML_GREEN_DISC = prove
 (`!(u:real^2->real) R.
     &0 < R /\ smooth_map_on (:real^2) (\z. lift(u z))
     ==> (\z. lift(cml_lap u z)) integrable_on ball(vec 0,R) /\
         drop(integral (ball(vec 0,R)) (\z. lift(cml_lap u z))) = cml_flux u R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `f = \z:real^2. vector[cml_d 1 u z; --(cml_d 2 u z)]:real^2` THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (f:real^2->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN
    GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE OPEN_UNIV] THEN
    REWRITE_TAC[DIMINDEX_2] THEN
    REWRITE_TAC[ARITH_RULE `1 <= k /\ k <= 2 <=> k = 1 \/ k = 2`] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_2] THEN
    ASM_SIMP_TAC[CML_SM_NEG; CML_D_SMOOTH; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. (f:real^2->real^2) differentiable (at z)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^2. frechet_derivative (f:real^2->real^2) (at z) (basis 1)$1 -
               frechet_derivative f (at z) (basis 2)$2 = cml_lap u z`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[CML_FRECHET_COMPONENT; DIMINDEX_2; ARITH] THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[VECTOR_2] THEN
    REWRITE_TAC[GSYM partial_derivative; GSYM cml_d] THEN
    MP_TAC(ISPECL [`(:real^2)`; `cml_d 2 (u:real^2->real)`; `z:real^2`; `2`] CML_D_NEG) THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; CML_D_SMOOTH; ETA_AX] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[cml_lap] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^2`; `circlepath(vec 0:real^2,R)`; `(:real^2)`]
                GREEN_THEOREM_CURL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_CONTINUOUS_RECTIFIABLE_VALID_PATH THEN
      REWRITE_TAC[VALID_PATH_CIRCLEPATH; RECTIFIABLE_PATH_CIRCLEPATH];
      REWRITE_TAC[PATHSTART_CIRCLEPATH; PATHFINISH_CIRCLEPATH];
      ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE; INSIDE_SPHERE] THEN
      REWRITE_TAC[IN_BALL; DIST_0] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC WINDING_NUMBER_CIRCLEPATH THEN ASM_REWRITE_TAC[VECTOR_SUB_RZERO];
      REWRITE_TAC[OPEN_UNIV];
      REWRITE_TAC[SUBSET_UNIV];
      REWRITE_TAC[differentiable_on] THEN ASM_MESON_TAC[DIFFERENTIABLE_AT_WITHIN];
      GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE; INSIDE_SPHERE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[cml_flux] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[VECTOR_2] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Directional derivatives, the radial derivative of u(z) = v(z / |z|^2) -  *)
(* 4 log |z|, and the flux of grad u through large circles: |flux_R + 8 pi| *)
(* <= C / R.                                                                *)
(* ========================================================================= *)

let cml_rad = new_definition
 `cml_rad (u:real^2->real) (z:real^2) = cml_d 1 u z * z$1 + cml_d 2 u z * z$2`;;

let CML_BASIS_EXPAND2 = prove
 (`!h:real^2. h = h$1 % basis 1 + h$2 % basis 2`,
  GEN_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC);;

let CML_DIR_DERIV = prove
 (`!(u:real^2->real) z h.
        (\x. lift(u x)) differentiable (at z)
        ==> ((\t. u(z + t % h)) has_real_derivative
             (cml_d 1 u z * h$1 + cml_d 2 u z * h$2)) (atreal (&0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  SUBGOAL_THEN
   `(lift o (\t. (u:real^2->real)(z + t % h)) o drop) =
    (\x. lift(u x)) o (\x:real^1. z + drop x % h)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\x. lift((u:real^2->real) x)) (at z) h =
    lift(cml_d 1 u z * h$1 + cml_d 2 u z * h$2)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CML_BASIS_EXPAND2] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
    REWRITE_TAC[cml_d; partial_derivative] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_ADD; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^1. (cml_d 1 (u:real^2->real) z * h$1 + cml_d 2 u z * h$2) % x) =
    frechet_derivative (\x. lift(u x)) (at z) o (\x:real^1. drop x % h)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `x:real^1` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:real^1. drop x % h:real^2) = (\x. vec 0 + drop x % h)`
    SUBST1_TAC THENL [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID; LIFT_NUM] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

(* A one-point chain rule for real functions.                               *)

let CML_CHAIN_POINT = prove
 (`!(g:real->real) c a d.
        (g has_real_derivative d) (atreal (&0)) /\
        (c has_real_derivative a) (atreal (&0)) /\ c(&0) = &0
        ==> ((\t. g(c t)) has_real_derivative a * d) (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(INST [`(\x:real. d):real->real`,`g':real->real`; `a:real`,`f':real`]
    (ISPECL [`\x:real. x = &0`; `c:real->real`; `g:real->real`]
            HAS_REAL_DERIVATIVE_CHAIN)) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;

(* The radial derivative of u(z) = v(z / |z|^2) - 4 log |z|.               *)

let CML_RADIAL_FORMULA = prove
 (`!(u:real^2->real) v z.
     smooth_map_on (:real^2) (\z. lift(u z)) /\ smooth_map_on (:real^2) (\z. lift(v z)) /\
     (!z. ~(z = vec 0) ==> u z = v(cml_inv z) - &4 * log(norm z)) /\ ~(z = vec 0)
     ==> cml_rad u z = --(&4) - cml_rad v (cml_inv z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_rad] THEN
  SUBGOAL_THEN `&0 < norm(z:real^2)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\t. (u:real^2->real)(z + t % z)`; `&0`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_DIR_DERIV THEN MATCH_MP_TAC CML_SM_DIFF THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\t. (v:real^2->real)(cml_inv z + (inv(&1 + t) - &1) % cml_inv z) -
                  &4 * log((&1 + t) * norm(z:real^2))` THEN
  EXISTS_TAC `&1 / &2` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &1 + t` ASSUME_TAC THENL
     [UNDISCH_TAC `abs(t - &0) < &1 / &2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `z + t % z = (&1 + t) % (z:real^2)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~((&1 + t) % (z:real^2) = vec 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN BINOP_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[cml_inv; NORM_MUL; VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `abs(&1 + t) = &1 + t` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&0 < &1 + t` THEN UNDISCH_TAC `&0 < norm(z:real^2)` THEN
      CONV_TAC REAL_FIELD;
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[NORM_MUL] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&4) - (cml_d 1 v (cml_inv z) * cml_inv z$1 + cml_d 2 v (cml_inv z) * cml_inv z$2) =
                --(&1) * (cml_d 1 (v:real^2->real) (cml_inv z) * cml_inv z$1 +
                          cml_d 2 v (cml_inv z) * cml_inv z$2) - &4`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\s. (v:real^2->real)(cml_inv z + s % cml_inv z)`;
                   `\t. inv(&1 + t) - &1`; `--(&1)`;
                   `cml_d 1 (v:real^2->real) (cml_inv z) * cml_inv z$1 +
                    cml_d 2 v (cml_inv z) * cml_inv z$2`] CML_CHAIN_POINT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CML_DIR_DERIV THEN MATCH_MP_TAC CML_SM_DIFF THEN
      EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      REAL_DIFF_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      CONV_TAC REAL_RAT_REDUCE_CONV];
    REAL_DIFF_TAC THEN REWRITE_TAC[REAL_ADD_RID; REAL_MUL_LID] THEN
    UNDISCH_TAC `&0 < norm(z:real^2)` THEN CONV_TAC REAL_FIELD]);;

(* The flux through the circle of radius R as 2 pi times a mean radial     *)
(* derivative.                                                               *)

let CML_CIRCLE_NORM = prove
 (`!R t. &0 <= R /\ t IN interval[vec 0,vec 1]
         ==> norm(circlepath(vec 0:real^2,R) t) = R`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `R:real`] PATH_IMAGE_CIRCLEPATH) THEN
  ASM_REWRITE_TAC[path_image; EXTENSION; IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(MP_TAC o SPEC `circlepath(vec 0:real^2,R) t`) THEN
  MATCH_MP_TAC(TAUT `p ==> (p <=> q) ==> q`) THEN ASM_MESON_TAC[]);;

let CML_CIRCLE_DERIV = prove
 (`!R t. vector_derivative (circlepath(vec 0:real^2,R)) (at t)$1 =
         --(&2 * pi) * (circlepath(vec 0,R) t)$2 /\
         vector_derivative (circlepath(vec 0:real^2,R)) (at t)$2 =
         (&2 * pi) * (circlepath(vec 0,R) t)$1`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `vector_derivative (circlepath(vec 0:real^2,R)) (at t) =
    Cx(&2 * pi) * (ii * circlepath(vec 0,R) t)`
  SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_DERIVATIVE_CIRCLEPATH; CIRCLEPATH; COMPLEX_VEC_0] THEN
    REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE_MUL_CX; IM_MUL_CX; RE_MUL_II; IM_MUL_II] THEN
  REAL_ARITH_TAC);;

let CML_RAD_SMOOTH = prove
 (`!(u:real^2->real). smooth_map_on (:real^2) (\z. lift(u z))
                      ==> smooth_map_on (:real^2) (\z. lift(cml_rad u z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_rad] THEN
  MATCH_MP_TAC CML_SM_ADD THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THEN
  MATCH_MP_TAC CML_SM_MUL THEN ASM_SIMP_TAC[OPEN_UNIV; CML_D_SMOOTH; CML_SM_COORD]);;

let CML_FLUX_RAD = prove
 (`!(u:real^2->real) R.
     smooth_map_on (:real^2) (\z. lift(u z))
     ==> (\t. lift(cml_rad u (circlepath(vec 0,R) t))) integrable_on interval[vec 0,vec 1] /\
         cml_flux u R =
         (&2 * pi) * drop(integral (interval[vec 0,vec 1])
                           (\t. lift(cml_rad u (circlepath(vec 0,R) t))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\t. lift(cml_rad (u:real^2->real) (circlepath(vec 0,R) t))) integrable_on
                interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    SUBGOAL_THEN `(\t. lift(cml_rad (u:real^2->real) (circlepath(vec 0,R) t))) =
                  (\z. lift(cml_rad u z)) o circlepath(vec 0,R)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM path; PATH_CIRCLEPATH];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON; CML_RAD_SMOOTH]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cml_flux; CML_CIRCLE_DERIV] THEN
  SUBGOAL_THEN
   `(&2 * pi) * drop(integral (interval[vec 0,vec 1])
                     (\t. lift(cml_rad (u:real^2->real) (circlepath(vec 0,R) t)))) =
    drop(integral (interval[vec 0,vec 1])
           (\t. (&2 * pi) % lift(cml_rad u (circlepath(vec 0,R) t))))`
  SUBST1_TAC THENL [ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL]; ALL_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[cml_rad] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

(* The flux of grad u through large circles tends to -8 pi.                 *)

let CML_FLUX_BOUND = prove
 (`!(u:real^2->real) v.
     smooth_map_on (:real^2) (\z. lift(u z)) /\ smooth_map_on (:real^2) (\z. lift(v z)) /\
     (!z. ~(z = vec 0) ==> u z = v(cml_inv z) - &4 * log(norm z))
     ==> ?C. !R. &1 <= R ==> abs(cml_flux u R + &8 * pi) <= C / R`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?Cv. &0 <= Cv /\
                     !w:real^2. norm w <= &1 ==> abs(cml_rad v w) <= Cv * norm w`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\w:real^2. lift(abs(cml_d 1 v w) + abs(cml_d 2 v w))`;
                   `cball(vec 0:real^2,&1)`] COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^2)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
      REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[CML_D_SMOOTH; OPEN_UNIV];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_CBALL_0; NORM_LIFT] THEN
    DISCH_THEN(X_CHOOSE_THEN `Cv:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cvb"))) THEN
    EXISTS_TAC `Cv:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    USE_THEN "cvb" (MP_TAC o SPEC `w:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[cml_rad] THEN
    MP_TAC(ISPECL [`w:real^2`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`w:real^2`; `2`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_2; ARITH] THEN
    ABBREV_TAC `a1 = cml_d 1 (v:real^2->real) w` THEN
    ABBREV_TAC `a2 = cml_d 2 (v:real^2->real) w` THEN
    ABBREV_TAC `n = norm(w:real^2)` THEN
    REPEAT DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs a1 * abs((w:real^2)$1) + abs a2 * abs(w$2)` THEN
    CONJ_TAC THENL [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(abs a1 + abs a2) * n` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; EXPAND_TAC "n" THEN REWRITE_TAC[NORM_POS_LE]]];
    ALL_TAC] THEN
  EXISTS_TAC `&2 * pi * Cv` THEN X_GEN_TAC `R:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u:real^2->real`; `R:real`] CML_FLUX_RAD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN interval[vec 0,vec 1]
        ==> abs(cml_rad (u:real^2->real) (circlepath(vec 0,R) t) + &4) <= Cv / R`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(circlepath(vec 0:real^2,R) t) = R` ASSUME_TAC THENL
     [MATCH_MP_TAC CML_CIRCLE_NORM THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(circlepath(vec 0:real^2,R) t = vec 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`u:real^2->real`; `v:real^2->real`; `circlepath(vec 0:real^2,R) t`]
                  CML_RADIAL_FORMULA) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPEC `circlepath(vec 0:real^2,R) t` CML_INV_NORM) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `cml_inv(circlepath(vec 0:real^2,R) t)`) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cml_flux (u:real^2->real) R + &8 * pi =
    (&2 * pi) * drop(integral (interval[vec 0,vec 1])
                      (\t. lift(cml_rad u (circlepath(vec 0,R) t) + &4)))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[LIFT_ADD] THEN
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_CONST; INTEGRAL_CONST; DROP_ADD] THEN
    REWRITE_TAC[CONTENT_UNIT_1; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * pi * Cv) / R = (&2 * pi) * (Cv / R)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_PI] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_1] THEN
  MP_TAC(ISPECL [`\t. lift(cml_rad (u:real^2->real) (circlepath(vec 0,R) t) + &4)`;
                 `vec 0:real^1`; `vec 1:real^1`;
                 `integral (interval[vec 0:real^1,vec 1])
                    (\t. lift(cml_rad (u:real^2->real) (circlepath(vec 0,R) t) + &4))`;
                 `Cv / R`] HAS_INTEGRAL_BOUND) THEN
  REWRITE_TAC[CONTENT_UNIT_1; REAL_MUL_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN REWRITE_TAC[LIFT_ADD] THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[INTEGRABLE_CONST];
    ASM_SIMP_TAC[NORM_LIFT]]);;

(* ========================================================================= *)
(* Gauss-Bonnet as an inequality for a smooth positive conformal factor mu  *)
(* on the plane with mu(z) = mu'(z / |z|^2) / |z|^4 (a smooth metric on     *)
(* S^2): any absolutely integrable F with -Lap(log mu) / 2 <= F has         *)
(* integral >= 4 pi.                                                        *)
(* ========================================================================= *)

let CML_LOG_REL = prove
 (`!(mu:real^2->real) mu' z.
     (!z. &0 < mu z) /\ (!z. &0 < mu' z) /\
     (!z. ~(z = vec 0) ==> mu z = mu'(cml_inv z) / norm z pow 4) /\ ~(z = vec 0)
     ==> log(mu z) = log(mu'(cml_inv z)) - &4 * log(norm z)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `&0 < norm(z:real^2)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_DIV; REAL_POW_LT; LOG_POW]);;

let CML_BALL_LIMIT = prove
 (`!Gf:real^2->real.
     (\z. lift(Gf z)) absolutely_integrable_on (:real^2)
     ==> (!n. (\z. lift(Gf z)) integrable_on ball(vec 0,&n)) /\
         ((\n. integral (ball(vec 0,&n)) (\z. lift(Gf z))) -->
          integral (:real^2) (\z. lift(Gf z))) sequentially`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\n. integral (ball(vec 0,&n)) (\z. lift((Gf:real^2->real) z))) =
    (\n. integral (:real^2) (\z. if z IN ball(vec 0,&n) then lift(Gf z) else vec 0))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; INTEGRAL_RESTRICT_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\n:num z:real^2. if z IN ball(vec 0,&n) then lift(Gf z) else vec 0`;
                 `\z:real^2. lift(Gf z)`; `\z:real^2. lift(norm(lift(Gf z)))`; `(:real^2)`]
                DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_BALL];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_REFL; NORM_0; NORM_POS_LE];
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(SPEC `norm(z:real^2) + &1` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_BALL_0] THEN
    SUBGOAL_THEN `norm(z:real^2) < &n` (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC]);;

let CML_GB_INEQ = prove
 (`!(mu:real^2->real) mu' Gf.
     smooth_map_on (:real^2) (\z. lift(mu z)) /\ (!z. &0 < mu z) /\
     smooth_map_on (:real^2) (\z. lift(mu' z)) /\ (!z. &0 < mu' z) /\
     (!z. ~(z = vec 0) ==> mu z = mu'(cml_inv z) / norm z pow 4) /\
     (\z. lift(Gf z)) absolutely_integrable_on (:real^2) /\
     (!z. --(cml_lap (\x. log(mu x)) z) / &2 <= Gf z)
     ==> &4 * pi <= drop(integral (:real^2) (\z. lift(Gf z)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\z. lift(log((mu:real^2->real) z))) /\
                smooth_map_on (:real^2) (\z. lift(log((mu':real^2->real) z)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CML_SM_LOG THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. log((mu:real^2->real) x)`; `\x. log((mu':real^2->real) x)`]
                CML_FLUX_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_LOG_REL THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `C:real`)] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_BALL_LIMIT) THEN
  SUBGOAL_THEN
   `!n. 1 <= n
        ==> &4 * pi - C / (&2 * &n) <=
            drop(integral (ball(vec 0,&n)) (\z. lift((Gf:real^2->real) z)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= &n` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\x. log((mu:real^2->real) x)`; `&n`] CML_GREEN_DISC) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&n`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\z. lift(--(cml_lap (\x. log((mu:real^2->real) x)) z) / &2)) =
      (\z. --(inv(&2)) % lift(cml_lap (\x. log(mu x)) z))`
    ASSUME_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL] THEN GEN_TAC THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (ball(vec 0,&n))
                       (\z. lift(--(cml_lap (\x. log((mu:real^2->real) x)) z) / &2)))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN
      SUBGOAL_THEN `C / (&2 * &n) = (C / &n) / &2` SUBST1_TAC THENL
       [SUBGOAL_THEN `&0 < &n` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
        ALL_TAC] THEN
      UNDISCH_TAC `abs (cml_flux (\x. log ((mu:real^2->real) x)) (&n) + &8 * pi) <= C / &n` THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `Iv = drop(integral (:real^2) (\z. lift((Gf:real^2->real) z)))` THEN
  ABBREV_TAC `e = (&4 * pi - Iv) / &2` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\n. integral (ball(vec 0,&n)) (\z. lift((Gf:real^2->real) z))`;
                 `integral (:real^2) (\z. lift((Gf:real^2->real) z))`; `&4 * pi - e`]
                LIM_DROP_LBOUND) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  MATCH_MP_TAC(TAUT `p /\ ~q ==> ~(p ==> q)`) THEN CONJ_TAC THENL
   [ALL_TAC; EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC] THEN
  MP_TAC(SPEC `abs C / (&2 * e) + &1` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= &n /\ abs C / (&2 * e) + &1 <= &n` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= abs C / (&2 * e)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `abs C / (&2 * e) + &1 <= &N` THEN UNDISCH_TAC `N:num <= n` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LE]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= e ==> p - b <= x ==> p - e <= x`) THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &2`] THEN
  MATCH_MP_TAC(REAL_ARITH `abs c <= x ==> c <= x`) THEN
  SUBGOAL_THEN `(&2 * e) * (abs C / (&2 * e)) = abs C` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * e` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * e) * (abs C / (&2 * e)) <= (&2 * e) * &n` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The regularized factor lam + delta rho, integrability of rho, and the    *)
(* planar core of Lemma 1.22:                                               *)
(*   4 pi <= int K / lam  (over lam > 0)                                     *)
(* for lam >= 0 smooth on the plane and at infinity, with a Bochner-Kato    *)
(* structure Lap lam = B - 2K, |grad lam|^2 <= lam B, B >= 0, and a          *)
(* negligible zero set.                                                      *)
(* ========================================================================= *)

let CML_D_LIN = prove
 (`!(lam:real^2->real) rho delta i.
     smooth_map_on (:real^2) (\z. lift(lam z)) /\ smooth_map_on (:real^2) (\z. lift(rho z))
     ==> cml_d i (\x. lam x + delta * rho x) =
         (\x. cml_d i lam x + delta * cml_d i rho x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^2` THEN
  MP_TAC(ISPECL [`(:real^2)`; `lam:real^2->real`; `\x. delta * (rho:real^2->real) x`;
                 `z:real^2`; `i:num`] CML_D_ADD) THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; CML_SM_CMUL] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CML_D_CMUL THEN EXISTS_TAC `(:real^2)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let CML_LAP_LIN = prove
 (`!(lam:real^2->real) rho delta z.
     smooth_map_on (:real^2) (\z. lift(lam z)) /\ smooth_map_on (:real^2) (\z. lift(rho z))
     ==> cml_lap (\x. lam x + delta * rho x) z = cml_lap lam z + delta * cml_lap rho z /\
         cml_grad2 (\x. lam x + delta * rho x) z =
         (cml_d 1 lam z + delta * cml_d 1 rho z) pow 2 +
         (cml_d 2 lam z + delta * cml_d 2 rho z) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[cml_lap; cml_grad2; CML_D_LIN] THEN
  SUBGOAL_THEN `!i. cml_d i (\x. cml_d i (lam:real^2->real) x + delta * cml_d i rho x) z =
                    cml_d i (cml_d i lam) z + delta * cml_d i (cml_d i rho) z`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`cml_d i (lam:real^2->real)`; `cml_d i (rho:real^2->real)`; `delta:real`;
                   `i:num`] CML_D_LIN) THEN
    ASM_SIMP_TAC[CML_D_SMOOTH; OPEN_UNIV; ETA_AX];
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* -Lap(log rho)/2 = rho, and rho is integrable on the plane.               *)

let CML_RHO_LAPLOG = prove
 (`!z. --(cml_lap (\x. log(cml_rho x)) z) / &2 = cml_rho z`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`(:real^2)`; `cml_rho`; `z:real^2`] CML_LAP_LOG) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; CML_RHO_SMOOTH; CML_RHO_POS; ETA_AX] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CML_RHO_IDENT] THEN
  MP_TAC(SPEC `z:real^2` CML_RHO_POS) THEN CONV_TAC REAL_FIELD);;

let CML_RHO_NONNEG = prove
 (`!z. &0 <= cml_rho z`,
  SIMP_TAC[CML_RHO_POS; REAL_LT_IMP_LE]);;

let CML_RHO_REL = prove
 (`!z:real^2. ~(z = vec 0) ==> cml_rho z = cml_rho(cml_inv z) / norm z pow 4`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CML_RHO_INV] THEN
  SUBGOAL_THEN `&0 < norm(z:real^2)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let CML_RHO_INTEGRABLE = prove
 (`(\z. lift(cml_rho z)) absolutely_integrable_on (:real^2)`,
  MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
  SIMP_TAC[IN_UNIV; DIMINDEX_1; FORALL_1; GSYM drop; LIFT_DROP; CML_RHO_POS; REAL_LT_IMP_LE] THEN
  MP_TAC(ISPECL [`\x. log(cml_rho x)`; `\x. log(cml_rho x)`] CML_FLUX_BOUND) THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\z. lift(log(cml_rho z)))` ASSUME_TAC THENL
   [MATCH_MP_TAC CML_SM_LOG THEN REWRITE_TAC[OPEN_UNIV; CML_RHO_SMOOTH; CML_RHO_POS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_LOG_REL THEN
    ASM_SIMP_TAC[CML_RHO_POS; CML_RHO_REL];
    DISCH_THEN(X_CHOOSE_TAC `C:real`)] THEN
  SUBGOAL_THEN `!n. 1 <= n ==> drop(integral (ball(vec 0,&n)) (\z. lift(cml_rho z))) <=
                               &4 * pi + C / (&2 * &n) /\
                               (\z. lift(cml_rho z)) integrable_on ball(vec 0,&n)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= &n` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\x. log(cml_rho x)`; `&n`] CML_GREEN_DISC) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&n`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\z. lift(cml_rho z)) =
                  (\z. --(inv(&2)) % lift(cml_lap (\x. log(cml_rho x)) z))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL] THEN X_GEN_TAC `y:real^2` THEN AP_TERM_TAC THEN
      MP_TAC(SPEC `y:real^2` CML_RHO_LAPLOG) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL; INTEGRABLE_CMUL] THEN
    SUBGOAL_THEN `C / (&2 * &n) = (C / &n) / &2` SUBST1_TAC THENL
     [SUBGOAL_THEN `&0 < &n` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    UNDISCH_TAC `abs (cml_flux (\x. log (cml_rho x)) (&n) + &8 * pi) <= C / &n` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n:num z:real^2. if z IN ball(vec 0,&n + &1) then lift(cml_rho z) else vec 0`;
                 `\z:real^2. lift(cml_rho z)`; `(:real^2)`] MONOTONE_CONVERGENCE_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k + 1`) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN SIMP_TAC[ARITH_RULE `1 <= k + 1`];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REPEAT(COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP; DROP_VEC; REAL_LE_REFL;
                                            CML_RHO_NONNEG]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_BALL_0; GSYM REAL_OF_NUM_SUC]) THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(SPEC `norm(z:real^2)` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_BALL_0] THEN
    SUBGOAL_THEN `norm(z:real^2) < &n + &1` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `N:num <= n` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[bounded; FORALL_IN_GSPEC; IN_UNIV; INTEGRAL_RESTRICT_UNIV] THEN
    EXISTS_TAC `&4 * pi + abs C` THEN X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k + 1`) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; ARITH_RULE `1 <= k + 1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= drop(integral (ball(vec 0,&k + &1)) (\z. lift(cml_rho z)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_SIMP_TAC[LIFT_DROP; CML_RHO_POS; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `C / (&2 * (&k + &1)) <= abs C` MP_TAC THENL
     [SUBGOAL_THEN `&0 < &2 * (&k + &1)` ASSUME_TAC THENL
       [MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MP_TAC(SPECL [`abs C`; `&2 * &k + &1`] REAL_LE_MUL) THEN
      MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[NORM_1] THEN ASM_REAL_ARITH_TAC]);;

(* The regularized pointwise inequality.                                    *)

let CML_DIV_FINAL = prove
 (`!m A Q. &0 < m /\ --(&2) * m * Q <= A ==> --(A / m pow 2) / &2 <= Q / m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Q / m - --(A / m pow 2) / &2 = (&2 * m * Q + A) / (&2 * m pow 2)` MP_TAC THENL
   [UNDISCH_TAC `&0 < m` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2 * m * Q + A) / (&2 * m pow 2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let CML_REG_PT = prove
 (`!(lam:real^2->real) K B delta z.
     smooth_map_on (:real^2) (\z. lift(lam z)) /\ (!z. &0 <= lam z) /\
     &0 < delta /\ &0 <= B z /\ cml_lap lam z = B z - &2 * K z /\
     cml_grad2 lam z <= lam z * B z
     ==> --(cml_lap (\x. log(lam x + delta * cml_rho x)) z) / &2
         <= (K z + delta * cml_rho z pow 2) / (lam z + delta * cml_rho z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\z. lift((lam:real^2->real) z + delta * cml_rho z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CML_SM_ADD THEN ASM_SIMP_TAC[OPEN_UNIV; CML_SM_CMUL; CML_RHO_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. &0 < (lam:real^2->real) z + delta * cml_rho z` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; CML_RHO_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `\x. (lam:real^2->real) x + delta * cml_rho x`; `z:real^2`]
                CML_LAP_LOG) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`lam:real^2->real`; `cml_rho`; `delta:real`; `z:real^2`] CML_LAP_LIN) THEN
  ASM_REWRITE_TAC[CML_RHO_SMOOTH; ETA_AX] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CML_DIV_FINAL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CML_PT_ALG THEN ASM_REWRITE_TAC[CML_RHO_POS] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `cml_grad2 lam z <= (lam:real^2->real) z * B z` THEN REWRITE_TAC[cml_grad2];
    MP_TAC(SPEC `z:real^2` CML_RHO_IDENT) THEN REWRITE_TAC[cml_grad2]]);;

(* The dominating bound for the regularized integrands.                     *)

let CML_FD_BOUND = prove
 (`!l r d k.
     &0 <= l /\ &0 < r /\ &0 < d /\ (l = &0 ==> k = &0)
     ==> abs((k + d * r pow 2) / (l + d * r)) <= abs(if l = &0 then &0 else k / l) + r`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `l = &0` THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(&0 + d * r pow 2) / (&0 + d * r) = r` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < l + d * r` ASSUME_TAC THENL
   [MP_TAC(SPECL [`d:real`; `r:real`] REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(abs k + d * r pow 2) / (l + d * r)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    SUBGOAL_THEN `&0 <= d * r pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs k / l + r - (abs k + d * r pow 2) / (l + d * r) =
                (abs k * d * r + r * l pow 2) / (l * (l + d * r))` MP_TAC THENL
   [UNDISCH_TAC `&0 < l` THEN UNDISCH_TAC `&0 < l + d * r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (abs k * d * r + r * l pow 2) / (l * (l + d * r))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* The planar core of CM Lemma 1.22.                                        *)

let CML_CORE = prove
 (`!(lam:real^2->real) lamq K B.
     smooth_map_on (:real^2) (\z. lift(lam z)) /\ (!z. &0 <= lam z) /\
     smooth_map_on (:real^2) (\z. lift(lamq z)) /\ (!z. &0 <= lamq z) /\
     (!z. ~(z = vec 0) ==> lam z = lamq(cml_inv z) / norm z pow 4) /\
     (\z. lift(K z)) continuous_on (:real^2) /\
     (!z. &0 <= B z /\ cml_lap lam z = B z - &2 * K z /\ cml_grad2 lam z <= lam z * B z) /\
     (!z. lam z = &0 ==> K z = &0) /\
     negligible {z | lam z = &0} /\
     (\z. lift(if lam z = &0 then &0 else K z / lam z)) absolutely_integrable_on (:real^2)
     ==> &4 * pi <= drop(integral (:real^2)
                           (\z. lift(if lam z = &0 then &0 else K z / lam z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Fd = \delta z. ((K:real^2->real) z + delta * cml_rho z pow 2) /
                             ((lam:real^2->real) z + delta * cml_rho z)` THEN
  ABBREV_TAC `H = \z. abs(if (lam:real^2->real) z = &0 then &0 else K z / lam z) + cml_rho z` THEN
  SUBGOAL_THEN `(\z. lift((H:real^2->real) z)) integrable_on (:real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THENL
     [REWRITE_TAC[GSYM NORM_LIFT] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[CML_RHO_INTEGRABLE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!delta. &0 < delta
            ==> (\z. lift((Fd:real->real^2->real) delta z)) integrable_on (:real^2) /\
                (!z. abs(Fd delta z) <= (H:real^2->real) z) /\
                &4 * pi <= drop(integral (:real^2) (\z. lift(Fd delta z)))`
  (LABEL_TAC "reg") THENL
   [X_GEN_TAC `delta:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!z. &0 < (lam:real^2->real) z + delta * cml_rho z` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
      ASM_SIMP_TAC[REAL_LT_MUL; CML_RHO_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `!z. abs((Fd:real->real^2->real) delta z) <= (H:real^2->real) z`
    ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "Fd" THEN EXPAND_TAC "H" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC CML_FD_BOUND THEN ASM_SIMP_TAC[CML_RHO_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\z. lift((Fd:real->real^2->real) delta z)) absolutely_integrable_on (:real^2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
      EXISTS_TAC `\z. lift((H:real^2->real) z)` THEN
      ASM_REWRITE_TAC[NORM_LIFT; LIFT_DROP; IN_UNIV] THEN
      EXPAND_TAC "Fd" THEN REWRITE_TAC[] THEN MATCH_MP_TAC MEASURABLE_ON_LIFT_DIV THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
        REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        REWRITE_TAC[CML_RHO_SMOOTH];
        MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        MATCH_MP_TAC CML_SM_ADD THEN ASM_SIMP_TAC[OPEN_UNIV; CML_SM_CMUL; CML_RHO_SMOOTH];
        MATCH_MP_TAC(MESON[NEGLIGIBLE_EMPTY] `(s:real^2->bool) = {} ==> negligible s`) THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNIV] THEN
        ASM_MESON_TAC[REAL_LT_IMP_NZ]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC CML_GB_INEQ THEN
    MAP_EVERY EXISTS_TAC [`\x. (lam:real^2->real) x + delta * cml_rho x`;
                          `\x. (lamq:real^2->real) x + delta * cml_rho x`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CML_SM_ADD THEN ASM_SIMP_TAC[OPEN_UNIV; CML_SM_CMUL; CML_RHO_SMOOTH];
      MATCH_MP_TAC CML_SM_ADD THEN ASM_SIMP_TAC[OPEN_UNIV; CML_SM_CMUL; CML_RHO_SMOOTH];
      GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
      ASM_SIMP_TAC[REAL_LT_MUL; CML_RHO_POS];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `cml_rho z = cml_rho(cml_inv z) / norm(z:real^2) pow 4` SUBST1_TAC THENL
       [ASM_SIMP_TAC[CML_RHO_REL]; ALL_TAC] THEN
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      X_GEN_TAC `z:real^2` THEN EXPAND_TAC "Fd" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC CML_REG_PT THEN EXISTS_TAC `B:real^2->real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 < inv(&n + &1)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN MP_TAC(SPEC `n:num` REAL_POS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n:num z:real^2. lift((Fd:real->real^2->real) (inv(&n + &1)) z)`;
                 `\z:real^2. lift(if (lam:real^2->real) z = &0 then cml_rho z else K z / lam z)`;
                 `\z:real^2. lift((H:real^2->real) z)`; `(:real^2)`] DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN USE_THEN "reg" (MP_TAC o SPEC `inv(&k + &1)`) THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
      USE_THEN "reg" (MP_TAC o SPEC `inv(&k + &1)`) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN EXPAND_TAC "Fd" THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC `(lam:real^2->real) z = &0` THEN ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
        EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN AP_TERM_TAC THEN
        SUBGOAL_THEN `(K:real^2->real) z = &0` SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        MP_TAC(SPEC `z:real^2` CML_RHO_POS) THEN
        FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> t = `inv`)) (concl th))) THEN
        CONV_TAC REAL_FIELD;
        SUBGOAL_THEN
         `((\n. ((K:real^2->real) z + inv(&n + &1) * cml_rho z pow 2) /
                ((lam:real^2->real) z + inv(&n + &1) * cml_rho z)) ---> K z / lam z)
          sequentially`
        MP_TAC THENL
         [SUBGOAL_THEN `(K:real^2->real) z / (lam:real^2->real) z =
                        (K z + &0 * cml_rho z pow 2) / (lam z + &0 * cml_rho z)`
          SUBST1_TAC THENL [REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
          MATCH_MP_TAC REALLIM_DIV THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
            MATCH_MP_TAC REALLIM_RMUL THEN REWRITE_TAC[REALLIM_1_OVER_N_OFFSET];
            MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
            MATCH_MP_TAC REALLIM_RMUL THEN REWRITE_TAC[REALLIM_1_OVER_N_OFFSET];
            ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID]];
          REWRITE_TAC[TENDSTO_REAL; o_DEF]]]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `integral (:real^2) (\z. lift(if (lam:real^2->real) z = &0 then &0 else K z / lam z)) =
    integral (:real^2) (\z. lift(if lam z = &0 then cml_rho z else K z / lam z))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `{z | (lam:real^2->real) z = &0}` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
  EXISTS_TAC `\n. integral (:real^2) (\z. lift((Fd:real->real^2->real) (inv(&n + &1)) z))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "reg" (MP_TAC o SPEC `inv(&n + &1)`) THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The transfer of S^2 integrals (p4_s2_integral, through the radial        *)
(* extension on the unit ball) to the stereographic plane:  p4_s2_integral  *)
(* f = int_R^2 f(P z) rho(z) dz. Change of variables x = r P(z) on (0,1) x  *)
(* R^2 (Jacobian r^2 rho(z)), a coordinate twizzle real^3 ->                *)
(* real^(1,2)finite_sum, and Fubini.                                        *)
(* ========================================================================= *)

let cml_v23 = new_definition
 `cml_v23 (t:real^3) = vector[t$2; t$3]:real^2`;;

let cml_cv = new_definition
 `cml_cv (t:real^3) = t$1 % stereo2_n_inv(cml_v23 t)`;;

let CML_V23_LINEAR = prove
 (`linear cml_v23`,
  REWRITE_TAC[linear; cml_v23; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT]);;

let CML_V23_BASIS = prove
 (`cml_v23(basis 1) = vec 0 /\ cml_v23(basis 2) = basis 1 /\ cml_v23(basis 3) = basis 2`,
  SIMP_TAC[cml_v23; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; BASIS_COMPONENT; VEC_COMPONENT;
           DIMINDEX_3; ARITH]);;

let CML_CV_DERIV = prove
 (`!t:real^3.
     (cml_cv has_derivative
      (\h. t$1 % bel_dP (cml_v23 t) (cml_v23 h) + h$1 % stereo2_n_inv(cml_v23 t))) (at t)`,
  GEN_TAC THEN
  SUBGOAL_THEN `cml_cv = (\x. (\y:real^3. y$1) x % (stereo2_n_inv o cml_v23) x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; cml_cv; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:real^3. y$1`; `\y:real^3. y$1`; `stereo2_n_inv o cml_v23`;
                 `bel_dP (cml_v23 t) o cml_v23`; `t:real^3`] HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[o_DEF] THEN
      REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[BEL_P_HAS_DERIVATIVE] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[CML_V23_LINEAR]];
    REWRITE_TAC[o_THM; ETA_AX]]);;

let CML_GRAM_MATRIX = prove
 (`!f:real^N->real^N i j.
     linear f /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> (transp(matrix f) ** matrix f)$i$j = f(basis i) dot f(basis j)`,
  SIMP_TAC[matrix_mul; transp; matrix; LAMBDA_BETA; dot]);;

let CML_CV_DET = prove
 (`!t:real^3.
     abs(det(matrix(\h. t$1 % bel_dP (cml_v23 t) (cml_v23 h) +
                        h$1 % stereo2_n_inv(cml_v23 t)))) =
     t$1 pow 2 * cml_rho(cml_v23 t)`,
  GEN_TAC THEN
  ABBREV_TAC `L = \h:real^3. t$1 % bel_dP (cml_v23 t) (cml_v23 h) +
                             h$1 % stereo2_n_inv(cml_v23 t)` THEN
  ABBREV_TAC `z = cml_v23 t` THEN
  SUBGOAL_THEN `linear(L:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
      SUBGOAL_THEN `(\h:real^3. bel_dP z (cml_v23 h)) = bel_dP z o cml_v23` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC LINEAR_COMPOSE THEN REWRITE_TAC[CML_V23_LINEAR; BEL_DP_LINEAR];
      MATCH_MP_TAC LINEAR_VMUL_COMPONENT THEN REWRITE_TAC[LINEAR_ID; DIMINDEX_3; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L:real^3->real^3)(basis 1) = stereo2_n_inv z /\
                L(basis 2) = (t:real^3)$1 % bel_dP z (basis 1) /\
                L(basis 3) = t$1 % bel_dP z (basis 2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[CML_V23_BASIS] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    MP_TAC(SPEC `z:real^2` BEL_DP_LINEAR) THEN DISCH_THEN(fun th ->
      REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID;
                VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `det(transp(matrix(L:real^3->real^3)) ** matrix L) =
                ((t:real^3)$1 pow 2 * cml_rho z) pow 2`
  MP_TAC THENL
   [REWRITE_TAC[DET_3] THEN
    ASM_SIMP_TAC[CML_GRAM_MATRIX; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[DOT_LMUL; DOT_RMUL; BEL_P_NORM; BEL_P_TANG; BEL_P_CONF] THEN
    ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[BEL_P_TANG; BEL_P_CONF] THEN
    SIMP_TAC[DOT_BASIS; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[cml_rho] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DET_MUL; DET_TRANSP; GSYM REAL_POW_2] THEN
  REWRITE_TAC[GSYM REAL_EQ_SQUARE_ABS] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2; CML_RHO_NONNEG]);;

let CML_P_NORM = prove
 (`!z. norm(stereo2_n_inv z) = &1`,
  GEN_TAC THEN REWRITE_TAC[NORM_EQ_1; BEL_P_NORM]);;

let CML_CV_NORM = prove
 (`!t:real^3. &0 <= t$1 ==> norm(cml_cv t) = t$1 /\
                            (&0 < t$1 ==> inv(t$1) % cml_cv t = stereo2_n_inv(cml_v23 t))`,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[cml_cv; NORM_MUL; CML_P_NORM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[cml_cv; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]);;

let CML_CV_INJ = prove
 (`!t t':real^3. &0 < t$1 /\ &0 < t'$1 /\ cml_cv t = cml_cv t' ==> t = t'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^3)$1 = (t':real^3)$1` ASSUME_TAC THENL
   [ASM_MESON_TAC[CML_CV_NORM; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `cml_v23 t = cml_v23 t'` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM STEX_STEREO2_N_RIGHT] THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[CML_CV_NORM; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[cml_v23; CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; VECTOR_2] THEN
  ASM_SIMP_TAC[]);;

let CML_S3 = new_definition
 `CML_S3 = {t:real^3 | &0 < t$1 /\ t$1 < &1}`;;

let CML_S3_OPEN = prove
 (`open CML_S3`,
  REWRITE_TAC[CML_S3; SET_RULE `{x:real^3 | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN
  SUBGOAL_THEN `{t:real^3 | &0 < t$1} = {x | x$1 > &0}` SUBST1_TAC THENL
   [REWRITE_TAC[real_gt]; REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT]]);;

let CML_CV_IMAGE = prove
 (`IMAGE cml_cv CML_S3 =
   {x:real^3 | x IN ball(vec 0,&1) /\ ~(x = vec 0) /\ ~(inv(norm x) % x = basis 3)}`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; CML_S3; IN_BALL_0] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `t:real^3` CML_CV_NORM) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[BEL_P_NE_N; GSYM NORM_EQ_0] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    EXISTS_TAC `vector[norm(x:real^3); stereo2_n(inv(norm x) % x)$1;
                       stereo2_n(inv(norm x) % x)$2]:real^3` THEN
    REWRITE_TAC[VECTOR_3] THEN ASM_REWRITE_TAC[NORM_POS_LT] THEN
    REWRITE_TAC[cml_cv; cml_v23; VECTOR_3] THEN
    SUBGOAL_THEN `vector[stereo2_n(inv(norm x) % x)$1; stereo2_n(inv(norm(x:real^3)) % x)$2]:real^2 =
                  stereo2_n(inv(norm x) % x)` SUBST1_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]; ALL_TAC] THEN
    SUBGOAL_THEN `stereo2_n_inv(stereo2_n(inv(norm x) % x)) = inv(norm(x:real^3)) % x`
    SUBST1_TAC THENL
     [MATCH_MP_TAC STEX_STEREO2_N_LEFT THEN ASM_REWRITE_TAC[IN_DELETE; IN_SPHERE_0] THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID]]);;

let CML_BALL_SPIKE = prove
 (`negligible(ball(vec 0:real^3,&1) DIFF IMAGE cml_cv CML_S3 UNION
              IMAGE cml_cv CML_S3 DIFF ball(vec 0,&1))`,
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `segment[vec 0:real^3,basis 3]` THEN
  REWRITE_TAC[NEGLIGIBLE_SEGMENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[CML_CV_IMAGE; SUBSET; IN_UNION; IN_DIFF; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[TAUT `(a /\ ~(a /\ b /\ c)) \/ ((a /\ b /\ c) /\ ~a) <=> a /\ (~b \/ ~c)`] THEN
  STRIP_TAC THENL [ASM_REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  REWRITE_TAC[segment; IN_ELIM_THM] THEN EXISTS_TAC `norm(x:real^3)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_BALL_0]) THEN
  ASM_REWRITE_TAC[NORM_POS_LE; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_LZERO] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID]);;

(* The change of variables x = cml_cv t on CML_S3.                           *)

let CML_CV_COV = prove
 (`!f:real^3->real.
     (\x. lift(f(inv(norm x) % x))) absolutely_integrable_on ball(vec 0,&1)
     ==> (\t. lift(t$1 pow 2 * (cml_rho(cml_v23 t) * f(stereo2_n_inv(cml_v23 t)))))
           absolutely_integrable_on CML_S3 /\
         integral CML_S3
           (\t. lift(t$1 pow 2 * (cml_rho(cml_v23 t) * f(stereo2_n_inv(cml_v23 t))))) =
         integral (ball(vec 0,&1)) (\x. lift(f(inv(norm x) % x)))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x. lift((f:real^3->real)(inv(norm x) % x))`; `cml_cv`;
                 `\t:real^3 h:real^3. t$1 % bel_dP (cml_v23 t) (cml_v23 h) +
                                       h$1 % stereo2_n_inv(cml_v23 t)`;
                 `CML_S3`;
                 `integral (ball(vec 0,&1)) (\x. lift((f:real^3->real)(inv(norm x) % x)))`]
                HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN REWRITE_TAC[CML_S3_OPEN];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[CML_CV_DERIV];
      REWRITE_TAC[CML_S3; IN_ELIM_THM] THEN MESON_TAC[CML_CV_INJ]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE_SET) THEN
      EXISTS_TAC `ball(vec 0:real^3,&1)` THEN ASM_REWRITE_TAC[CML_BALL_SPIKE];
      MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN ONCE_REWRITE_TAC[UNION_COMM] THEN
      REWRITE_TAC[CML_BALL_SPIKE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN CML_S3
        ==> abs(det(matrix(\h:real^3. t$1 % bel_dP (cml_v23 t) (cml_v23 h) +
                                       h$1 % stereo2_n_inv(cml_v23 t)))) %
            lift((f:real^3->real)(inv(norm(cml_cv t)) % cml_cv t)) =
            lift(t$1 pow 2 * (cml_rho(cml_v23 t) * f(stereo2_n_inv(cml_v23 t))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^3` THEN REWRITE_TAC[CML_S3; IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[CML_CV_DET; GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
    MP_TAC(SPEC `t:real^3` CML_CV_NORM) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
    EXISTS_TAC `\t:real^3. abs(det(matrix(\h:real^3. t$1 % bel_dP (cml_v23 t) (cml_v23 h) +
                                                     h$1 % stereo2_n_inv(cml_v23 t)))) %
                           lift((f:real^3->real)(inv(norm(cml_cv t)) % cml_cv t))` THEN
    ASM_SIMP_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    ASM_SIMP_TAC[]]);;

(* The radial integral int_0^1 r^2 dr = 1/3.                                *)

let CML_R2_INTEGRAL = prove
 (`((\r:real^1. lift(drop r pow 2)) has_integral lift(&1 / &3)) (interval(vec 0,vec 1))`,
  REWRITE_TAC[HAS_INTEGRAL_OPEN_INTERVAL] THEN
  MP_TAC(ISPECL [`\x:real. x pow 3 / &3`; `\x:real. x pow 2`; `&0`; `&1`]
                REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    REWRITE_TAC[HAS_REAL_INTEGRAL; o_DEF; LIFT_NUM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[GSYM LIFT_NUM]]);;

(* Coordinates of the twizzle real^(1,2)finite_sum -> real^3.               *)

let CML_TW_PASTE = prove
 (`!(r:real^1) (z:real^2).
     ((lambda i. (pastecart r z:real^(1,2)finite_sum)$I i):real^3)$1 = drop r /\
     cml_v23((lambda i. (pastecart r z:real^(1,2)finite_sum)$I i):real^3) = z`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH; I_THM; cml_v23] THEN
  SIMP_TAC[PASTECART_COMPONENT; DIMINDEX_1; DIMINDEX_2; ARITH; drop] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

let CML_TW_IMAGE = prove
 (`IMAGE (\x:real^(1,2)finite_sum. (lambda i. x$I i):real^3)
         {x | &0 < x$1 /\ x$1 < &1} = CML_S3`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; CML_S3; I_THM] THEN
  X_GEN_TAC `t:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^(1,2)finite_sum` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH];
    DISCH_TAC THEN EXISTS_TAC `(lambda i. (t:real^3)$i):real^(1,2)finite_sum` THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_3; DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_2;
             ARITH] THEN
    ASM_REWRITE_TAC[]]);;

let CML_S3_FUBINI = prove
 (`!g:real^2->real.
     (\t:real^3. lift(t$1 pow 2 * g(cml_v23 t))) absolutely_integrable_on CML_S3
     ==> (\z. lift(g z)) absolutely_integrable_on (:real^2) /\
         &3 * drop(integral CML_S3 (\t:real^3. lift(t$1 pow 2 * g(cml_v23 t)))) =
         drop(integral (:real^2) (\z. lift(g z)))`,
  GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `Sp = {x:real^(1,2)finite_sum | &0 < x$1 /\ x$1 < &1}` THEN
  MP_TAC(ISPECL [`\t:real^3. lift(t$1 pow 2 * g(cml_v23 t))`;
                 `Sp:real^(1,2)finite_sum->bool`; `I:num->num`]
                ABSOLUTELY_INTEGRABLE_TWIZZLE_EQ) THEN
  MP_TAC(ISPECL [`\t:real^3. lift(t$1 pow 2 * g(cml_v23 t))`;
                 `Sp:real^(1,2)finite_sum->bool`; `I:num->num`] INTEGRAL_TWIZZLE_EQ) THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_2; DIMINDEX_3; ARITH; PERMUTES_I] THEN
  EXPAND_TAC "Sp" THEN REWRITE_TAC[CML_TW_IMAGE] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  ABBREV_TAC `Hf = \x:real^(1,2)finite_sum.
                     if x IN Sp then lift(((lambda i. x$I i):real^3)$1 pow 2 *
                                          g(cml_v23((lambda i. x$I i):real^3)))
                     else vec 0` THEN
  SUBGOAL_THEN `(Hf:real^(1,2)finite_sum->real^1) absolutely_integrable_on (:real^(1,2)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Hf" THEN REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    EXPAND_TAC "Sp" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r z. (Hf:real^(1,2)finite_sum->real^1) (pastecart r z) =
          if &0 < drop r /\ drop r < &1 then lift(drop r pow 2 * g z) else vec 0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "Hf" THEN EXPAND_TAC "Sp" THEN
    REWRITE_TAC[IN_ELIM_THM; CML_TW_PASTE] THEN
    SIMP_TAC[PASTECART_COMPONENT; DIMINDEX_1; ARITH; drop];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bad") (LABEL_TAC "fub")) THEN
  SUBGOAL_THEN
   `?r0:real^1. &0 < drop r0 /\ drop r0 < &1 /\
                (\y. lift(drop r0 pow 2 * (g:real^2->real) y)) absolutely_integrable_on (:real^2)`
  STRIP_ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    USE_THEN "bad" (MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] NEGLIGIBLE_SUBSET)) THEN
    DISCH_THEN(MP_TAC o SPEC `interval(vec 0:real^1,vec 1)`) THEN
    REWRITE_TAC[NEGLIGIBLE_INTERVAL; INTERVAL_NE_EMPTY_1; DROP_VEC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; DROP_VEC; NOT_IMP] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      REWRITE_TAC[INTERVAL_NE_EMPTY_1; DROP_VEC] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift((g:real^2->real) z)) absolutely_integrable_on (:real^2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\z. lift((g:real^2->real) z)) =
                  (\z. inv(drop r0 pow 2) % lift(drop r0 pow 2 * g z))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; LIFT_EQ; REAL_MUL_ASSOC] THEN GEN_TAC THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_POW_NZ; REAL_LT_IMP_NZ; REAL_MUL_LID];
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `C = integral (:real^2) (\z. lift((g:real^2->real) z))` THEN
  SUBGOAL_THEN
   `!x:real^1. integral (:real^2)
                 (\y. if &0 < drop x /\ drop x < &1 then lift(drop x pow 2 * (g:real^2->real) y)
                      else vec 0) =
               drop(if x IN interval(vec 0,vec 1) then lift(drop x pow 2) else vec 0) %
               (C:real^1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGRAL_0; DROP_VEC; VECTOR_MUL_LZERO; LIFT_DROP] THEN
    EXPAND_TAC "C" THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC INTEGRAL_CMUL THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x:real^1. drop(if x IN interval(vec 0,vec 1) then lift(drop x pow 2) else vec 0) %
                 (C:real^1))
     has_integral (&1 / &3) % C) (:real^1)`
  ASSUME_TAC THENL
   [MP_TAC(ONCE_REWRITE_RULE[GSYM HAS_INTEGRAL_RESTRICT_UNIV] CML_R2_INTEGRAL) THEN
    DISCH_THEN(MP_TAC o ISPEC `\v:real^1. drop v % (C:real^1)` o MATCH_MP
      (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
    REWRITE_TAC[o_DEF; LIFT_DROP] THEN ANTS_TAC THENL
     [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC];
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `integral (:real^(1,2)finite_sum) (Hf:real^(1,2)finite_sum->real^1) =
                (&1 / &3) % (C:real^1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL
      [`\x:real^1. drop(if x IN interval(vec 0,vec 1) then lift(drop x pow 2) else vec 0) %
                   (C:real^1)`; `(:real^1)`] HAS_INTEGRAL_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "fub" MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral Sp (\x:real^(1,2)finite_sum. lift(((lambda i. x$I i):real^3)$1 pow 2 *
                                               (g:real^2->real)(cml_v23((lambda i. x$I i):real^3)))) =
    integral (:real^(1,2)finite_sum) Hf`
  SUBST1_TAC THENL
   [EXPAND_TAC "Hf" THEN REWRITE_TAC[INTEGRAL_RESTRICT_UNIV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[DROP_CMUL] THEN REAL_ARITH_TAC);;

(* The transfer formula.                                                     *)

let CML_S2_TRANSFER = prove
 (`!f:real^3->real.
     (\x. lift(f(inv(norm x) % x))) absolutely_integrable_on ball(vec 0,&1)
     ==> (\z. lift(cml_rho z * f(stereo2_n_inv z))) absolutely_integrable_on (:real^2) /\
         p4_s2_integral f =
         drop(integral (:real^2) (\z. lift(cml_rho z * f(stereo2_n_inv z))))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_CV_COV) THEN
  MP_TAC(ISPEC `\z:real^2. cml_rho z * (f:real^3->real)(stereo2_n_inv z)` CML_S3_FUBINI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[p4_s2_integral] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
     can (find_term (fun t -> t = `CML_S3`)) (concl th))) THEN
  REFL_TAC);;

(* ========================================================================= *)
(* The planar core for a general auxiliary round metric rho1 (smooth,       *)
(* positive, curvature 1, smooth at infinity): 4 pi <= int_{lam > 0} K /    *)
(* lam + int_{lam = 0} rho1.                                                *)
(* ========================================================================= *)

let CML_AUX_INTEGRABLE = prove
 (`!(rho1:real^2->real) rho1q.
     smooth_map_on (:real^2) (\z. lift(rho1 z)) /\ (!z. &0 < rho1 z) /\
     smooth_map_on (:real^2) (\z. lift(rho1q z)) /\ (!z. &0 < rho1q z) /\
     (!z. ~(z = vec 0) ==> rho1 z = rho1q(cml_inv z) / norm z pow 4) /\
     (!z. rho1 z * cml_lap rho1 z - cml_grad2 rho1 z = --(&2) * rho1 z pow 3)
     ==> (\z. lift(rho1 z)) absolutely_integrable_on (:real^2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. --(cml_lap (\x. log((rho1:real^2->real) x)) z) / &2 = rho1 z`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`(:real^2)`; `rho1:real^2->real`; `z:real^2`] CML_LAP_LOG) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `z:real^2` (ASSUME `!z. &0 < (rho1:real^2->real) z`)) THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. &0 <= (rho1:real^2->real) z` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
  ASM_SIMP_TAC[IN_UNIV; DIMINDEX_1; FORALL_1; GSYM drop; LIFT_DROP] THEN
  MP_TAC(ISPECL [`\x. log((rho1:real^2->real) x)`; `\x. log((rho1q:real^2->real) x)`]
                CML_FLUX_BOUND) THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\z. lift(log((rho1:real^2->real) z))) /\
                smooth_map_on (:real^2) (\z. lift(log((rho1q:real^2->real) z)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CML_SM_LOG THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_LOG_REL THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `C:real`)] THEN
  SUBGOAL_THEN `!n. 1 <= n ==> drop(integral (ball(vec 0,&n)) (\z. lift((rho1:real^2->real) z))) <=
                               &4 * pi + C / (&2 * &n) /\
                               (\z. lift((rho1:real^2->real) z)) integrable_on ball(vec 0,&n)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= &n` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\x. log((rho1:real^2->real) x)`; `&n`] CML_GREEN_DISC) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&n`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\z. lift((rho1:real^2->real) z)) =
                  (\z. --(inv(&2)) % lift(cml_lap (\x. log((rho1:real^2->real) x)) z))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL] THEN X_GEN_TAC `y:real^2` THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th -> can (find_term (fun t -> t = `log`)) (concl th) && is_forall(concl th))) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL; INTEGRABLE_CMUL] THEN
    SUBGOAL_THEN `C / (&2 * &n) = (C / &n) / &2` SUBST1_TAC THENL
     [SUBGOAL_THEN `&0 < &n` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    UNDISCH_TAC `abs (cml_flux (\x. log ((rho1:real^2->real) x)) (&n) + &8 * pi) <= C / &n` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n:num z:real^2. if z IN ball(vec 0,&n + &1) then lift((rho1:real^2->real) z) else vec 0`;
                 `\z:real^2. lift((rho1:real^2->real) z)`; `(:real^2)`] MONOTONE_CONVERGENCE_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k + 1`) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN SIMP_TAC[ARITH_RULE `1 <= k + 1`];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[LIFT_DROP; DROP_VEC; REAL_LE_REFL]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_BALL_0; GSYM REAL_OF_NUM_SUC]) THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(SPEC `norm(z:real^2)` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_BALL_0] THEN
    SUBGOAL_THEN `norm(z:real^2) < &n + &1` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `N:num <= n` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[bounded; FORALL_IN_GSPEC; IN_UNIV; INTEGRAL_RESTRICT_UNIV] THEN
    EXISTS_TAC `&4 * pi + abs C` THEN X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k + 1`) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; ARITH_RULE `1 <= k + 1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= drop(integral (ball(vec 0,&k + &1)) (\z. lift((rho1:real^2->real) z)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_SIMP_TAC[LIFT_DROP; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `C / (&2 * (&k + &1)) <= abs C` MP_TAC THENL
     [SUBGOAL_THEN `&0 < &2 * (&k + &1)` ASSUME_TAC THENL
       [MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MP_TAC(SPECL [`abs C`; `&2 * &k + &1`] REAL_LE_MUL) THEN
      MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[NORM_1] THEN ASM_REAL_ARITH_TAC]);;

let CML_REG_PT_GEN = prove
 (`!(lam:real^2->real) (rho1:real^2->real) K B delta z.
     smooth_map_on (:real^2) (\z. lift(rho1 z)) /\ (!z. &0 < rho1 z) /\
     (!z. rho1 z * cml_lap rho1 z - cml_grad2 rho1 z = --(&2) * rho1 z pow 3) /\
     smooth_map_on (:real^2) (\z. lift(lam z)) /\ (!z. &0 <= lam z) /\
     &0 < delta /\ &0 <= B z /\ cml_lap lam z = B z - &2 * K z /\
     cml_grad2 lam z <= lam z * B z
     ==> --(cml_lap (\x. log(lam x + delta * rho1 x)) z) / &2
         <= (K z + delta * rho1 z pow 2) / (lam z + delta * rho1 z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\z. lift((lam:real^2->real) z + delta * rho1 z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CML_SM_ADD THEN ASM_SIMP_TAC[OPEN_UNIV; CML_SM_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. &0 < (lam:real^2->real) z + delta * rho1 z` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `\x. (lam:real^2->real) x + delta * rho1 x`; `z:real^2`]
                CML_LAP_LOG) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`lam:real^2->real`; `rho1:real^2->real`; `delta:real`; `z:real^2`] CML_LAP_LIN) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CML_DIV_FINAL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CML_PT_ALG THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `cml_grad2 lam z <= (lam:real^2->real) z * B z` THEN REWRITE_TAC[cml_grad2];
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th -> can (find_term (fun t -> t = `cml_grad2`)) (concl th) && is_forall(concl th))) THEN REWRITE_TAC[cml_grad2]]);;

let CML_CORE_GEN = prove
 (`!(lam:real^2->real) lamq K B (rho1:real^2->real) rho1q.
     smooth_map_on (:real^2) (\z. lift(rho1 z)) /\ (!z. &0 < rho1 z) /\
     smooth_map_on (:real^2) (\z. lift(rho1q z)) /\ (!z. &0 < rho1q z) /\
     (!z. ~(z = vec 0) ==> rho1 z = rho1q(cml_inv z) / norm z pow 4) /\
     (!z. rho1 z * cml_lap rho1 z - cml_grad2 rho1 z = --(&2) * rho1 z pow 3) /\
     smooth_map_on (:real^2) (\z. lift(lam z)) /\ (!z. &0 <= lam z) /\
     smooth_map_on (:real^2) (\z. lift(lamq z)) /\ (!z. &0 <= lamq z) /\
     (!z. ~(z = vec 0) ==> lam z = lamq(cml_inv z) / norm z pow 4) /\
     (\z. lift(K z)) continuous_on (:real^2) /\
     (!z. &0 <= B z /\ cml_lap lam z = B z - &2 * K z /\ cml_grad2 lam z <= lam z * B z) /\
     (!z. lam z = &0 ==> K z = &0) /\
     (\z. lift(if lam z = &0 then &0 else K z / lam z)) absolutely_integrable_on (:real^2)
     ==> &4 * pi <= drop(integral (:real^2)
                           (\z. lift(if lam z = &0 then &0 else K z / lam z))) +
                    drop(integral (:real^2) (\z. lift(if lam z = &0 then rho1 z else &0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Fd = \delta z. ((K:real^2->real) z + delta * rho1 z pow 2) /
                             ((lam:real^2->real) z + delta * rho1 z)` THEN
  ABBREV_TAC `H = \z. abs(if (lam:real^2->real) z = &0 then &0 else K z / lam z) + rho1 z` THEN
  SUBGOAL_THEN `(\z. lift((H:real^2->real) z)) integrable_on (:real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THENL
     [REWRITE_TAC[GSYM NORM_LIFT] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CML_AUX_INTEGRABLE THEN EXISTS_TAC `rho1q:real^2->real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!delta. &0 < delta
            ==> (\z. lift((Fd:real->real^2->real) delta z)) integrable_on (:real^2) /\
                (!z. abs(Fd delta z) <= (H:real^2->real) z) /\
                &4 * pi <= drop(integral (:real^2) (\z. lift(Fd delta z)))`
  (LABEL_TAC "reg") THENL
   [X_GEN_TAC `delta:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!z. &0 < (lam:real^2->real) z + delta * rho1 z` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
      ASM_SIMP_TAC[REAL_LT_MUL];
      ALL_TAC] THEN
    SUBGOAL_THEN `!z. abs((Fd:real->real^2->real) delta z) <= (H:real^2->real) z`
    ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "Fd" THEN EXPAND_TAC "H" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC CML_FD_BOUND THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\z. lift((Fd:real->real^2->real) delta z)) absolutely_integrable_on (:real^2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
      EXISTS_TAC `\z. lift((H:real^2->real) z)` THEN
      ASM_REWRITE_TAC[NORM_LIFT; LIFT_DROP; IN_UNIV] THEN
      EXPAND_TAC "Fd" THEN REWRITE_TAC[] THEN MATCH_MP_TAC MEASURABLE_ON_LIFT_DIV THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
        REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        MATCH_MP_TAC CML_SM_ADD THEN ASM_SIMP_TAC[OPEN_UNIV; CML_SM_CMUL];
        MATCH_MP_TAC(MESON[NEGLIGIBLE_EMPTY] `(s:real^2->bool) = {} ==> negligible s`) THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNIV] THEN
        ASM_MESON_TAC[REAL_LT_IMP_NZ]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC CML_GB_INEQ THEN
    MAP_EVERY EXISTS_TAC [`\x. (lam:real^2->real) x + delta * rho1 x`;
                          `\x. (lamq:real^2->real) x + delta * rho1q x`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CML_SM_ADD THEN ASM_SIMP_TAC[OPEN_UNIV; CML_SM_CMUL];
      MATCH_MP_TAC CML_SM_ADD THEN ASM_SIMP_TAC[OPEN_UNIV; CML_SM_CMUL];
      GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
      ASM_SIMP_TAC[REAL_LT_MUL];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `(rho1:real^2->real) z = rho1q(cml_inv z) / norm(z:real^2) pow 4` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      X_GEN_TAC `z:real^2` THEN EXPAND_TAC "Fd" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC CML_REG_PT_GEN THEN EXISTS_TAC `B:real^2->real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 < inv(&n + &1)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN MP_TAC(SPEC `n:num` REAL_POS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n:num z:real^2. lift((Fd:real->real^2->real) (inv(&n + &1)) z)`;
                 `\z:real^2. lift(if (lam:real^2->real) z = &0 then rho1 z else K z / lam z)`;
                 `\z:real^2. lift((H:real^2->real) z)`; `(:real^2)`] DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN USE_THEN "reg" (MP_TAC o SPEC `inv(&k + &1)`) THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
      USE_THEN "reg" (MP_TAC o SPEC `inv(&k + &1)`) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN EXPAND_TAC "Fd" THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC `(lam:real^2->real) z = &0` THEN ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
        EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN AP_TERM_TAC THEN
        SUBGOAL_THEN `(K:real^2->real) z = &0` SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        MP_TAC(SPEC `z:real^2` (ASSUME `!z. &0 < (rho1:real^2->real) z`)) THEN
        FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> t = `inv`)) (concl th))) THEN
        CONV_TAC REAL_FIELD;
        SUBGOAL_THEN
         `((\n. ((K:real^2->real) z + inv(&n + &1) * rho1 z pow 2) /
                ((lam:real^2->real) z + inv(&n + &1) * rho1 z)) ---> K z / lam z)
          sequentially`
        MP_TAC THENL
         [SUBGOAL_THEN `(K:real^2->real) z / (lam:real^2->real) z =
                        (K z + &0 * rho1 z pow 2) / (lam z + &0 * rho1 z)`
          SUBST1_TAC THENL [REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
          MATCH_MP_TAC REALLIM_DIV THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
            MATCH_MP_TAC REALLIM_RMUL THEN REWRITE_TAC[REALLIM_1_OVER_N_OFFSET];
            MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
            MATCH_MP_TAC REALLIM_RMUL THEN REWRITE_TAC[REALLIM_1_OVER_N_OFFSET];
            ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID]];
          REWRITE_TAC[TENDSTO_REAL; o_DEF]]]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `drop(integral (:real^2) (\z. lift(if (lam:real^2->real) z = &0 then &0 else K z / lam z))) +
    drop(integral (:real^2) (\z. lift(if lam z = &0 then rho1 z else &0))) =
    drop(integral (:real^2) (\z. lift(if lam z = &0 then rho1 z else K z / lam z)))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `(\z. lift(if (lam:real^2->real) z = &0 then rho1 z else &0)) =
      (\z. lift(if lam z = &0 then rho1 z else K z / lam z) -
           lift(if lam z = &0 then &0 else K z / lam z))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_SUB] THEN GEN_TAC THEN AP_TERM_TAC THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_SUB; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; DROP_SUB] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
  EXISTS_TAC `\n. integral (:real^2) (\z. lift((Fd:real->real^2->real) (inv(&n + &1)) z))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "reg" (MP_TAC o SPEC `inv(&n + &1)`) THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The Moebius family of round factors rho_{p,a}(z) = a^-2 rho((z - p)/a)   *)
(* (concentrating at p as a -> 0), and the planar core with the zero set of *)
(* lam handled by concentration at a point where lam > 0 (no unique         *)
(* continuation is needed).                                                 *)
(* ========================================================================= *)

let cml_rhoa = new_definition
 `cml_rhoa (p:real^2) a (z:real^2) = inv(a pow 2) * cml_rho(inv a % (z - p))`;;

let cml_rhoaq = new_definition
 `cml_rhoaq (p:real^2) a (w:real^2) =
    &4 * a pow 2 / ((a pow 2 + norm p pow 2) * norm w pow 2 - &2 * (w dot p) + &1) pow 2`;;

let CML_AFFINE_SMOOTH = prove
 (`!(u:real^2->real) c p.
     smooth_map_on (:real^2) (\z. lift(u z))
     ==> smooth_map_on (:real^2) (\z. lift(u(c % (z - p))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift((u:real^2->real)(c % (z - p)))) =
                (\x. lift(u x)) o (\z:real^2. c % (z - p))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

let CML_D_AFFINE = prove
 (`!(u:real^2->real) c p z i.
     smooth_map_on (:real^2) (\z. lift(u z))
     ==> cml_d i (\z. u(c % (z - p))) z = c * cml_d i u (c % (z - p))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_PARTIAL_LINE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_DIFF THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; CML_AFFINE_SMOOTH];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `c % ((z + t % b) - p) = c % (z - p) + (c * t) % b`] THEN
  MP_TAC(ISPECL [`\s. (u:real^2->real)(c % (z - p) + s % basis i)`; `\t:real. c * t`;
                 `c:real`; `cml_d i (u:real^2->real) (c % (z - p))`] CML_CHAIN_POINT) THEN
  REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_LINE_DERIV THEN MATCH_MP_TAC CML_SM_DIFF THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    REAL_DIFF_TAC THEN REAL_ARITH_TAC]);;

let CML_RHOA_SMOOTH = prove
 (`!p a. smooth_map_on (:real^2) (\z. lift(cml_rhoa p a z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cml_rhoa] THEN MATCH_MP_TAC CML_SM_CMUL THEN
  REWRITE_TAC[OPEN_UNIV] THEN MATCH_MP_TAC CML_AFFINE_SMOOTH THEN
  REWRITE_TAC[CML_RHO_SMOOTH]);;

let CML_RHOA_POS = prove
 (`!p a z. &0 < a ==> &0 < cml_rhoa p a z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_rhoa] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT; CML_RHO_POS]);;

let CML_RHOA_EXPLICIT = prove
 (`!p a z. &0 < a
           ==> cml_rhoa p a z = &4 * a pow 2 / (a pow 2 + norm(z - p) pow 2) pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_rhoa; cml_rho; NORM_MUL; REAL_POW_MUL] THEN
  ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < a ==> abs a = a`] THEN
  SUBGOAL_THEN `inv a pow 2 * norm(z - p:real^2) pow 2 + &1 =
                (a pow 2 + norm(z - p) pow 2) / a pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a pow 2 + norm(z - p:real^2) pow 2` MP_TAC THENL
   [MP_TAC(SPEC `norm(z - p:real^2)` REAL_LE_POW_2) THEN
    MP_TAC(SPECL [`a:real`; `2`] REAL_POW_LT) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD);;

(* Derivatives of rho_{p,a} and its curvature identity.                     *)

let CML_D_SCALED = prove
 (`!(u:real^2->real) b c p z i.
     smooth_map_on (:real^2) (\z. lift(u z))
     ==> cml_d i (\z. b * u(c % (z - p))) z = b * (c * cml_d i u (c % (z - p)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^2)`; `b:real`; `\z. (u:real^2->real)(c % (z - p))`; `z:real^2`;
                 `i:num`] CML_D_CMUL) THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; CML_AFFINE_SMOOTH] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CML_D_AFFINE THEN ASM_REWRITE_TAC[]);;

let CML_RHOA_D = prove
 (`!p a i. cml_d i (cml_rhoa p a) =
           \z. inv(a pow 2) * (inv a * cml_d i cml_rho (inv a % (z - p)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^2` THEN
  SUBGOAL_THEN `cml_rhoa p a = (\z. inv(a pow 2) * cml_rho(inv a % (z - p)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; cml_rhoa]; ALL_TAC] THEN
  MATCH_MP_TAC CML_D_SCALED THEN REWRITE_TAC[CML_RHO_SMOOTH]);;

let CML_RHOA_DD = prove
 (`!p a z i. cml_d i (cml_d i (cml_rhoa p a)) z =
             inv(a pow 2) * (inv a * (inv a * cml_d i (cml_d i cml_rho) (inv a % (z - p))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CML_RHOA_D] THEN
  MP_TAC(ISPECL [`(:real^2)`; `inv(a pow 2)`;
                 `\z. inv a * cml_d i cml_rho (inv a % (z - p))`; `z:real^2`; `i:num`]
                CML_D_CMUL) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [MATCH_MP_TAC CML_SM_CMUL THEN REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC CML_AFFINE_SMOOTH THEN SIMP_TAC[CML_D_SMOOTH; OPEN_UNIV; CML_RHO_SMOOTH];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CML_D_SCALED THEN
  SIMP_TAC[CML_D_SMOOTH; OPEN_UNIV; CML_RHO_SMOOTH]);;

let CML_RHOA_IDENT = prove
 (`!p a z. &0 < a
           ==> cml_rhoa p a z * cml_lap (cml_rhoa p a) z - cml_grad2 (cml_rhoa p a) z =
               --(&2) * cml_rhoa p a z pow 3`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_lap; cml_grad2; CML_RHOA_DD] THEN
  REWRITE_TAC[CML_RHOA_D] THEN REWRITE_TAC[cml_rhoa] THEN
  MP_TAC(SPEC `inv a % (z - p:real^2)` CML_RHO_IDENT) THEN
  REWRITE_TAC[cml_lap; cml_grad2] THEN
  ABBREV_TAC `r = cml_rho(inv a % (z - p:real^2))` THEN
  ABBREV_TAC `d1 = cml_d 1 cml_rho (inv a % (z - p:real^2))` THEN
  ABBREV_TAC `d2 = cml_d 2 cml_rho (inv a % (z - p:real^2))` THEN
  ABBREV_TAC `e1 = cml_d 1 (cml_d 1 cml_rho) (inv a % (z - p:real^2))` THEN
  ABBREV_TAC `e2 = cml_d 2 (cml_d 2 cml_rho) (inv a % (z - p:real^2))` THEN
  REWRITE_TAC[REAL_POW_INV] THEN UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD);;

(* The function at infinity.                                                *)

let CML_RHOAQ_DEN_POS = prove
 (`!(p:real^2) a (w:real^2). &0 < a
           ==> &0 < (a pow 2 + norm p pow 2) * norm w pow 2 - &2 * (w dot p) + &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`w:real^2`; `p:real^2`] NORM_CAUCHY_SCHWARZ) THEN
  SUBGOAL_THEN `&0 <= (norm(p:real^2) * norm(w:real^2) - &1) pow 2` MP_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ASM_CASES_TAC `w:real^2 = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; DOT_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a pow 2 * norm(w:real^2) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let CML_RHOAQ_POS = prove
 (`!p a w. &0 < a ==> &0 < cml_rhoaq p a w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_rhoaq] THEN MATCH_MP_TAC REAL_LT_MUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LT_DIV THEN
  ASM_SIMP_TAC[REAL_POW_LT; CML_RHOAQ_DEN_POS]);;

let CML_RHOAQ_SMOOTH = prove
 (`!p a. &0 < a ==> smooth_map_on (:real^2) (\w. lift(cml_rhoaq p a w))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_rhoaq] THEN MATCH_MP_TAC CML_SM_CMUL THEN
  REWRITE_TAC[OPEN_UNIV] THEN MATCH_MP_TAC CML_SM_DIV THEN
  REWRITE_TAC[OPEN_UNIV; CML_SM_CONST; IN_UNIV] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_POW THEN REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC CML_SM_ADD THEN REWRITE_TAC[OPEN_UNIV; CML_SM_CONST] THEN
    MATCH_MP_TAC CML_SM_SUB THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CML_SM_CMUL THEN SIMP_TAC[OPEN_UNIV; CML_SM_NORM2];
      MATCH_MP_TAC CML_SM_CMUL THEN REWRITE_TAC[OPEN_UNIV] THEN
      MP_TAC(ISPECL [`(:real^2)`; `\w:real^2. w`; `\w:real^2. p:real^2`] SMOOTH_MAP_ON_DOT_OPEN) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]];
    GEN_TAC THEN MATCH_MP_TAC REAL_POW_NZ THEN
    ASM_SIMP_TAC[CML_RHOAQ_DEN_POS; REAL_LT_IMP_NZ]]);;

let CML_RHOA_REL = prove
 (`!p a z. &0 < a /\ ~(z = vec 0)
           ==> cml_rhoa p a z = cml_rhoaq p a (cml_inv z) / norm z pow 4`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CML_RHOA_EXPLICIT; cml_rhoaq] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_NORM) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < norm(z:real^2)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(a pow 2 + norm(p:real^2) pow 2) * inv(norm(z:real^2)) pow 2 -
                &2 * (cml_inv z dot p) + &1 =
                (a pow 2 + norm(z - p) pow 2) / norm z pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[cml_inv; DOT_LMUL; NORM_POW_2; DOT_LSUB; DOT_RSUB] THEN
    REWRITE_TAC[GSYM NORM_POW_2] THEN
    SUBGOAL_THEN `(z:real^2) dot p = p dot z` SUBST1_TAC THENL [REWRITE_TAC[DOT_SYM]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < norm(z:real^2)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a pow 2 + norm(z - p:real^2) pow 2` MP_TAC THENL
   [MP_TAC(SPEC `norm(z - p:real^2)` REAL_LE_POW_2) THEN
    MP_TAC(SPECL [`a:real`; `2`] REAL_POW_LT) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < norm(z:real^2)` THEN CONV_TAC REAL_FIELD);;

(* Concentration: away from p, rho_{p,a} <= a^2 C rho_{p,1}.                *)

let CML_RHOA_COMPARE = prove
 (`!p a r0 z. &0 < a /\ &0 < r0 /\ r0 <= norm(z - p)
              ==> cml_rhoa p a z <= a pow 2 * (&1 + inv(r0 pow 2)) pow 2 * cml_rhoa p (&1) z`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CML_RHOA_EXPLICIT; REAL_ARITH `&0 < &1`] THEN
  ABBREV_TAC `s = norm(z - p:real^2) pow 2` THEN
  SUBGOAL_THEN `r0 pow 2 <= s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r0 pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ONE] THEN
  ABBREV_TAC `c = &1 + inv(r0 pow 2)` THEN
  SUBGOAL_THEN `&1 + s <= c * s` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 + s <= s + x`) THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MP_TAC(MATCH_MP REAL_LT_INV (ASSUME `&0 < r0 pow 2`)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + s) pow 2 <= (c * (a pow 2 + s)) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * s` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `a pow 2 * c pow 2 * (&4 * &1 / (&1 + s) pow 2) - &4 * a pow 2 / (a pow 2 + s) pow 2 =
    (&4 * a pow 2) * ((c * (a pow 2 + s)) pow 2 - (&1 + s) pow 2) /
    ((&1 + s) pow 2 * (a pow 2 + s) pow 2)`
  MP_TAC THENL
   [UNDISCH_TAC `&0 < s` THEN UNDISCH_TAC `&0 < a pow 2` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&4 * a pow 2) * ((c * (a pow 2 + s)) pow 2 - (&1 + s) pow 2) /
                       ((&1 + s) pow 2 * (a pow 2 + s) pow 2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* The planar core, with the zero set of lam handled by concentration.      *)

let CML_ZPART_INTEGRABLE = prove
 (`!(lam:real^2->real) (rho1:real^2->real).
     (\z. lift(lam z)) continuous_on (:real^2) /\
     (\z. lift(rho1 z)) continuous_on (:real^2) /\
     (!z. &0 <= rho1 z) /\ (\z. lift(rho1 z)) absolutely_integrable_on (:real^2)
     ==> (\z. lift(if lam z = &0 then rho1 z else &0)) integrable_on (:real^2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\z. lift((rho1:real^2->real) z)` THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; IN_UNIV] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\z. lift(if (lam:real^2->real) z = &0 then rho1 z else &0)) =
                  (\z. if z IN {z | lam z = &0} then lift(rho1 z) else vec 0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[LIFT_NUM];
      ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_ON_RESTRICT THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_CLOSED THEN
    SUBGOAL_THEN `{z | (lam:real^2->real) z = &0} = {z | lift(lam z) IN {vec 0}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[IN_SING; GSYM LIFT_NUM; LIFT_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN REWRITE_TAC[CLOSED_SING] THEN
    GEN_TAC THEN
    MP_TAC(ISPECL [`\z. lift((lam:real^2->real) z)`; `(:real^2)`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN SIMP_TAC[];
    GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x <= x`]]);;

let CML_CORE_POS = prove
 (`!(lam:real^2->real) lamq K B p r0.
     smooth_map_on (:real^2) (\z. lift(lam z)) /\ (!z. &0 <= lam z) /\
     smooth_map_on (:real^2) (\z. lift(lamq z)) /\ (!z. &0 <= lamq z) /\
     (!z. ~(z = vec 0) ==> lam z = lamq(cml_inv z) / norm z pow 4) /\
     (\z. lift(K z)) continuous_on (:real^2) /\
     (!z. &0 <= B z /\ cml_lap lam z = B z - &2 * K z /\ cml_grad2 lam z <= lam z * B z) /\
     (!z. lam z = &0 ==> K z = &0) /\
     &0 < r0 /\ (!z. z IN ball(p,r0) ==> &0 < lam z) /\
     (\z. lift(if lam z = &0 then &0 else K z / lam z)) absolutely_integrable_on (:real^2)
     ==> &4 * pi <= drop(integral (:real^2)
                           (\z. lift(if lam z = &0 then &0 else K z / lam z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Iv = drop(integral (:real^2)
                    (\z. lift(if (lam:real^2->real) z = &0 then &0 else K z / lam z)))` THEN
  ABBREV_TAC `M = (&1 + inv(r0 pow 2)) pow 2 *
                  drop(integral (:real^2) (\z. lift(cml_rhoa p (&1) z)))` THEN
  SUBGOAL_THEN `(\z. lift((lam:real^2->real) z)) continuous_on (:real^2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `!a. &0 < a ==> (\z. lift(cml_rhoa p a z)) absolutely_integrable_on (:real^2)`
  (LABEL_TAC "rhoint") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_AUX_INTEGRABLE THEN
    EXISTS_TAC `cml_rhoaq p a` THEN
    ASM_SIMP_TAC[CML_RHOA_SMOOTH; CML_RHOA_POS; CML_RHOAQ_SMOOTH; CML_RHOAQ_POS;
                 CML_RHOA_REL; CML_RHOA_IDENT; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. &0 < a ==> &4 * pi <= Iv + a pow 2 * M` ASSUME_TAC THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`lam:real^2->real`; `lamq:real^2->real`; `K:real^2->real`;
                   `B:real^2->real`; `cml_rhoa p a`; `cml_rhoaq p a`] CML_CORE_GEN) THEN
    ASM_SIMP_TAC[CML_RHOA_SMOOTH; CML_RHOA_POS; CML_RHOAQ_SMOOTH; CML_RHOAQ_POS;
                 CML_RHOA_REL; CML_RHOA_IDENT; ETA_AX] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= Iv + y ==> x <= Iv + z`) THEN
    EXPAND_TAC "M" THEN
    SUBGOAL_THEN `(\z. lift(cml_rhoa p (&1) z)) integrable_on (:real^2)` ASSUME_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      USE_THEN "rhoint" MATCH_MP_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `a pow 2 * (&1 + inv(r0 pow 2)) pow 2 *
                  drop(integral (:real^2) (\z. lift(cml_rhoa p (&1) z))) =
                  drop(integral (:real^2)
                    (\z. lift(a pow 2 * (&1 + inv(r0 pow 2)) pow 2 * cml_rhoa p (&1) z)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN
      SIMP_TAC[INTEGRAL_CMUL; INTEGRABLE_CMUL; DROP_CMUL;
               ASSUME `(\z. lift(cml_rhoa p (&1) z)) integrable_on (:real^2)`];
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CML_ZPART_INTEGRABLE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CML_RHOA_SMOOTH; CML_RHOA_POS;
                   REAL_LT_IMP_LE];
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      COND_CASES_TAC THENL
       [MATCH_MP_TAC CML_RHOA_COMPARE THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        SUBGOAL_THEN `&0 < (lam:real^2->real) z` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL; dist] THEN
          ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[REAL_LT_REFL]];
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC CML_RHOA_POS THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; REAL_ARITH `&0 < &1`; LIFT_DROP;
                 IN_UNIV; CML_RHOA_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?a. &0 < a /\ a <= &1 /\ a * (M + &1) <= (&4 * pi - Iv) / &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (&4 * pi - Iv) / (&2 * (M + &1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `min (&1 / &2) ((&4 * pi - Iv) / (&2 * (M + &1)))` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `((&4 * pi - Iv) / (&2 * (M + &1))) * (M + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        SUBGOAL_THEN `&0 < M + &1` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a pow 2 * M <= a * (M + &1)` MP_TAC THENL
   [SUBGOAL_THEN `a pow 2 <= a` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a * M` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Chart representations on the plane. For a parametrization X of the       *)
(* sphere (stereo2_n_inv or stereo2_s_inv) the pullback of a matrix field Q *)
(* by v o X (from p4_s2_gram), its chart formula through w = phi o v o X,   *)
(* and the curvature numerator K.                                           *)
(* ========================================================================= *)

let cml_wc = new_definition
 `cml_wc (c:(A->bool)#(A->real^3)) (v:real^3->A) (X:real^2->real^3) (z:real^2) =
    SND c (v(X z))`;;

let cml_pull = new_definition
 `cml_pull (atlas:((A->bool)#(A->real^3))->bool) (Q:A->real^3^3) (v:real^3->A)
           (X:real^2->real^3) (z:real^2) =
    (lambda i j. frechet_derivative X (at z) (basis i) dot
                 (p4_s2_gram atlas Q v (X z) ** frechet_derivative X (at z) (basis j))):real^2^2`;;

let CML_RADIAL_ON_SPHERE = prove
 (`!y:real^3. norm y = &1 ==> inv(norm y) % y = y`,
  SIMP_TAC[REAL_INV_1; VECTOR_MUL_LID]);;

(* The radial extension in a chart, composed with X, is cml_wc.             *)

let CML_WC_COMPOSE = prove
 (`!(c:(A->bool)#(A->real^3)) (v:real^3->A) (X:real^2->real^3).
     (!z. norm(X z) = &1)
     ==> cml_wc c v X = (\x. SND c (v(inv(norm x) % x))) o X`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; cml_wc] THEN
  ASM_SIMP_TAC[CML_RADIAL_ON_SPHERE]);;

let CML_PULL_CHART = prove
 (`!top atlas (Q:A->real^3^3) (v:real^3->A) (X:real^2->real^3) U phi z i j.
     smooth_manifold_atlas top atlas /\ p4_s2_smooth (top,atlas) v /\
     (U,phi) IN atlas /\ (!z. X differentiable (at z)) /\ (!z. norm(X z) = &1) /\
     v(X z) IN U /\ 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
     ==> cml_pull atlas Q v X z$i$j =
         partial_derivative i (cml_wc (U,phi) v X) z dot
         (metric_local atlas (U,phi) Q (phi(v(X z))) **
          partial_derivative j (cml_wc (U,phi) v X) z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p4_s2_smooth]) THEN
  ABBREV_TAC `F0 = \x:real^3. (phi:A->real^3)((v:real^3->A)(inv(norm x) % x))` THEN
  SUBGOAL_THEN `(F0:real^3->real^3) differentiable (at ((X:real^2->real^3) z))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{x:real^3 | ~(x = vec 0) /\ (v:real^3->A)(inv(norm x) % x) IN U}` THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `v:real^3->A`;
                     `(U:A->bool,phi:A->real^3)`] P4_RADIAL_CHART_OPEN) THEN
      ASM_REWRITE_TAC[FST];
      EXPAND_TAC "F0" THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN ASM_REWRITE_TAC[FST; SND];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[CML_RADIAL_ON_SPHERE] THEN
      REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Q:A->real^3^3`;
                 `v:real^3->A`; `U:A->bool`; `phi:A->real^3`; `(X:real^2->real^3) z`]
                P4_S2_GRAM_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_SPHERE_0] THEN
    UNDISCH_TAC `(F0:real^3->real^3) differentiable (at ((X:real^2->real^3) z))` THEN
    EXPAND_TAC "F0" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[cml_pull; LAMBDA_BETA; DIMINDEX_2] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[CML_WC_COMPOSE; partial_derivative] THEN
  ASM_SIMP_TAC[BEL_FRECHET_CHAIN; o_THM] THEN
  ASM_SIMP_TAC[GSYM BEL_JAC_APPLY]);;

(* ========================================================================= *)
(* Covariant derivatives along a planar map w into a chart with metric      *)
(* field G: line derivatives, smoothness of Christoffel compositions,       *)
(* metric compatibility, torsion freeness and the curvature commutator.     *)
(* ========================================================================= *)

let cml_cov = new_definition
 `cml_cov (G:real^3->real^3^3) (w:real^2->real^3) (X:real^2->real^3) (a:num) (z:real^2) =
    partial_derivative a X z + christoffel G (w z) (partial_derivative a w z) (X z)`;;

let CML_PD_VLINE = prove
 (`!(X:real^2->real^N) z i.
     X differentiable (at z)
     ==> ((\r:real^1. X(z + drop r % basis i)) has_vector_derivative
          partial_derivative i X z) (at (vec 0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_vector_derivative; partial_derivative] THEN
  SUBGOAL_THEN `(\r:real^1. (X:real^2->real^N)(z + drop r % basis i)) =
                X o (\r. z + drop r % basis i)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^1. drop x % frechet_derivative (X:real^2->real^N) (at z) (basis i)) =
                frechet_derivative X (at z) o (\x. drop x % basis i)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN SIMP_TAC[LINEAR_CMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:real^1. drop x % basis i:real^2) = (\x. vec 0 + drop x % basis i)`
    SUBST1_TAC THENL [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

let CML_PD_FROM_VLINE = prove
 (`!(X:real^2->real^N) z i d.
     X differentiable (at z) /\
     ((\r:real^1. X(z + drop r % basis i)) has_vector_derivative d) (at (vec 0))
     ==> partial_derivative i X z = d`,
  MESON_TAC[CML_PD_VLINE; VECTOR_DERIVATIVE_UNIQUE_AT]);;

(* The real-parameter form used by GEOC_DOT_DERIV.                           *)

let CML_PD_RLINE = prove
 (`!(X:real^2->real^N) z i.
     X differentiable (at z)
     ==> ((\s:real^1. (\t. X(z + t % basis i)) (drop s)) has_vector_derivative
          partial_derivative i X z) (at (lift(&0)))`,
  REWRITE_TAC[LIFT_NUM] THEN SIMP_TAC[CML_PD_VLINE]);;

(* Smoothness of Christoffel compositions.                                   *)

let CML_CHR_SMOOTH = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) (A:real^2->real^3) B.
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     smooth_map_on W A /\ smooth_map_on W B
     ==> smooth_map_on W (\z. christoffel G (w z) (A z) (B z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN W ==> christoffel G ((w:real^2->real^3) z) ((A:real^2->real^3) z) (B z) =
                   vsum (1..dimindex(:3))
                    (\i. vsum (1..dimindex(:3))
                      (\j. (A z$i * B z$j) % christoffel G (w z) (basis i) (basis j)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPC_BILINEAR_EXPAND THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN EXISTS_TAC `V:real^3->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[SMOOTH_MAP_ON_EQ_OPEN]
   `!g. open (W:real^2->bool) /\ smooth_map_on W (g:real^2->real^3) /\
        (!z. z IN W ==> f z = g z) ==> smooth_map_on W f`) THEN
  EXISTS_TAC `\z. vsum (1..dimindex(:3))
                    (\i. vsum (1..dimindex(:3))
                      (\j. ((A:real^2->real^3) z$i * (B:real^2->real^3) z$j) %
                           christoffel G ((w:real^2->real^3) z) (basis i) (basis j)))` THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`W:real^2->bool`; `\z. lift((A:real^2->real^3) z$i * (B:real^2->real^3) z$j)`;
                 `\z. christoffel G ((w:real^2->real^3) z) (basis i) (basis j)`]
                SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_MUL THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT];
    SUBGOAL_THEN `(\z. christoffel G ((w:real^2->real^3) z) (basis i) (basis j)) =
                  (\y. christoffel G y (basis i) (basis j)) o w` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH THEN ASM_REWRITE_TAC[]]);;

let CML_COV_SMOOTH = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) (X:real^2->real^3) a.
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     smooth_map_on W X
     ==> smooth_map_on W (cml_cov G w X a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cml_cov G (w:real^2->real^3) (X:real^2->real^3) a =
                \z. partial_derivative a X z +
                    christoffel G (w z) (partial_derivative a w z) (X z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; cml_cov]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CML_CHR_SMOOTH THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN
    ASM_REWRITE_TAC[]]);;

(* Smoothness of G-quadratic forms along w.                                 *)

let CML_GENTRY_SMOOTH = prove
 (`!V (G:real^3->real^3^3) i j. metric_field V G ==> smooth_map_on V (\y. lift(G y$i$j))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN `(\y. lift((G:real^3->real^3^3) y$i$j)) =
                (\x:real^(3,3)finite_prod. lift((matrify x:real^3^3)$i$j)) o
                ((vectorize:real^3^3->real^(3,3)finite_prod) o G)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY]);;

let CML_MATVEC_SMOOTH = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) (Y:real^2->real^3).
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     smooth_map_on W Y
     ==> smooth_map_on W (\z. G(w z) ** Y z)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE (ASSUME `open(W:real^2->bool)`)] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[dot; DIMINDEX_3] THEN
  SUBGOAL_THEN `(\z. lift(sum(1..3) (\i. ((G:real^3->real^3^3)((w:real^2->real^3) z))$k$i *
                                          (Y:real^2->real^3) z$i))) =
                (\z. lift(sum(1..3) (\i. drop((\i z. lift(G(w z)$k$i * Y z$i)) i z))))`
  SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CML_SM_MUL THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT] THEN
  SUBGOAL_THEN `(\z. lift((G:real^3->real^3^3)((w:real^2->real^3) z)$k$i)) =
                (\y. lift(G y$k$i)) o w` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^3->bool` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MATCH_MP_TAC CML_GENTRY_SMOOTH THEN ASM_REWRITE_TAC[]);;

let CML_QUAD_SMOOTH = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) (X:real^2->real^3) Y.
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     smooth_map_on W X /\ smooth_map_on W Y
     ==> smooth_map_on W (\z. lift(X z dot (G(w z) ** Y z)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^2->bool`; `X:real^2->real^3`;
                 `\z. (G:real^3->real^3^3)((w:real^2->real^3) z) ** (Y:real^2->real^3) z`]
                SMOOTH_MAP_ON_DOT_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CML_MATVEC_SMOOTH THEN EXISTS_TAC `V:real^3->bool` THEN ASM_REWRITE_TAC[]);;

(* Metric compatibility.                                                     *)

let CML_PD_METRIC = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) (X:real^2->real^3) Y z a.
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     smooth_map_on W X /\ smooth_map_on W Y /\ z IN W
     ==> partial_derivative a (\z. lift(X z dot (G(w z) ** Y z))) z =
         lift(cml_cov G w X a z dot (G(w z) ** Y z) +
              X z dot (G(w z) ** cml_cov G w Y a z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_PD_FROM_VLINE THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CML_QUAD_SMOOTH THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!(Z:real^2->real^3). smooth_map_on W Z ==> Z differentiable (at z)`
  ASSUME_TAC THENL [ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`;
                 `\t. (w:real^2->real^3)(z + t % basis a)`;
                 `partial_derivative a (w:real^2->real^3) z`;
                 `\t. (X:real^2->real^3)(z + t % basis a)`;
                 `partial_derivative a (X:real^2->real^3) z`;
                 `\t. (Y:real^2->real^3)(z + t % basis a)`;
                 `partial_derivative a (Y:real^2->real^3) z`; `&0`] GEOC_DOT_DERIV) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; LIFT_NUM; cml_cov] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THEN
    MP_TAC(ISPECL [`X:real^2->real^3`; `z:real^2`; `a:num`] CML_PD_RLINE) THEN
    MP_TAC(ISPECL [`Y:real^2->real^3`; `z:real^2`; `a:num`] CML_PD_RLINE) THEN
    MP_TAC(ISPECL [`w:real^2->real^3`; `z:real^2`; `a:num`] CML_PD_RLINE) THEN
    ASM_SIMP_TAC[LIFT_NUM];
    REWRITE_TAC[]]);;

(* Schwarz, torsion freeness, and the derivative of a Christoffel term.     *)

let CML_SCHWARZ = prove
 (`!W (u:real^2->real^N) z.
     open W /\ smooth_map_on W u /\ z IN W
     ==> partial_derivative 1 (partial_derivative 2 u) z =
         partial_derivative 2 (partial_derivative 1 u) z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PARTIAL_DERIVATIVE_ALT] THEN
  MATCH_MP_TAC SCHWARZ_C2 THEN EXISTS_TAC `W:real^2->bool` THEN
  ASM_REWRITE_TAC[IN_NUMSEG; DIMINDEX_2; ARITH] THEN ASM_MESON_TAC[smooth_map_on]);;

let CML_TORSION = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) z.
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     z IN W
     ==> cml_cov G w (partial_derivative 2 w) 1 z = cml_cov G w (partial_derivative 1 w) 2 z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_cov] THEN BINOP_TAC THENL
   [MATCH_MP_TAC CML_SCHWARZ THEN EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CHRISTOFFEL_SYM THEN EXISTS_TAC `V:real^3->bool` THEN ASM_SIMP_TAC[]]);;

let CML_PD_CHR = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) (A:real^2->real^3) B z a.
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     smooth_map_on W A /\ smooth_map_on W B /\ z IN W
     ==> partial_derivative a (\z. christoffel G (w z) (A z) (B z)) z =
         frechet_derivative (\y. christoffel G y (A z) (B z)) (at (w z))
           (partial_derivative a w z) +
         christoffel G (w z) (partial_derivative a A z) (B z) +
         christoffel G (w z) (A z) (partial_derivative a B z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!(Z:real^2->real^3). smooth_map_on W Z ==> Z differentiable (at z)`
  ASSUME_TAC THENL [ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE]; ALL_TAC] THEN
  MATCH_MP_TAC CML_PD_FROM_VLINE THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC CML_CHR_SMOOTH THEN
    EXISTS_TAC `V:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`;
                 `\r:real^1. (w:real^2->real^3)(z + drop r % basis a)`;
                 `\r:real^1. (A:real^2->real^3)(z + drop r % basis a)`;
                 `\r:real^1. (B:real^2->real^3)(z + drop r % basis a)`;
                 `partial_derivative a (w:real^2->real^3) z`;
                 `partial_derivative a (A:real^2->real^3) z`;
                 `partial_derivative a (B:real^2->real^3) z`; `vec 0:real^1`]
                CMPC_CHRISTOFFEL_ALONG) THEN
  REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[CML_PD_VLINE]);;

(* The curvature commutator along w.                                         *)

let CML_COMMUTATOR = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) (X:real^2->real^3) z.
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     smooth_map_on W X /\ z IN W
     ==> cml_cov G w (cml_cov G w X 2) 1 z - cml_cov G w (cml_cov G w X 1) 2 z =
         lriemann G (w z) (partial_derivative 1 w z) (partial_derivative 2 w z) (X z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!(Z:real^2->real^3). smooth_map_on W Z ==> Z differentiable (at z)`
  ASSUME_TAC THENL [ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `!a. smooth_map_on W (partial_derivative a (w:real^2->real^3)) /\
                    smooth_map_on W (partial_derivative a (X:real^2->real^3))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. partial_derivative a (cml_cov G (w:real^2->real^3) (X:real^2->real^3) b) z =
          partial_derivative a (partial_derivative b X) z +
          (frechet_derivative (\y. christoffel G y (partial_derivative b w z) (X z)) (at (w z))
             (partial_derivative a w z) +
           christoffel G (w z) (partial_derivative a (partial_derivative b w) z) (X z) +
           christoffel G (w z) (partial_derivative b w z) (partial_derivative a X z))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `cml_cov G (w:real^2->real^3) (X:real^2->real^3) b =
                  (\z. partial_derivative b X z +
                       christoffel G (w z) (partial_derivative b w z) (X z))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; cml_cov]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:num`; `partial_derivative b (X:real^2->real^3)`;
                   `\z. christoffel G ((w:real^2->real^3) z) (partial_derivative b w z)
                                      ((X:real^2->real^3) z)`; `z:real^2`]
                  PARTIAL_DERIVATIVE_ADD) THEN
    REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC CML_CHR_SMOOTH THEN EXISTS_TAC `V:real^3->bool` THEN
        ASM_REWRITE_TAC[ETA_AX]];
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CML_PD_CHR THEN EXISTS_TAC `V:real^3->bool` THEN
    EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[cml_cov] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `partial_derivative 1 (partial_derivative 2 (X:real^2->real^3)) z =
                partial_derivative 2 (partial_derivative 1 X) z /\
                partial_derivative 1 (partial_derivative 2 (w:real^2->real^3)) z =
                partial_derivative 2 (partial_derivative 1 w) z`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC CML_SCHWARZ THEN EXISTS_TAC `W:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bilinear (christoffel G ((w:real^2->real^3) z))` MP_TAC THENL
   [MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN EXISTS_TAC `V:real^3->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP BILINEAR_RADD th]) THEN
  REWRITE_TAC[lriemann] THEN
  MATCH_MP_TAC(VECTOR_ARITH
   `F1:real^3 = F1' /\ F2:real^3 = F2' /\ H1:real^3 = H1' /\ H2:real^3 = H2'
    ==> ((A + F1 + C + D) + E + H1) - ((A + F2 + C + E) + D + H2) =
        F1' - F2' + H1' - H2'`) THEN
  REPEAT CONJ_TAC THEN REFL_TAC);;

(* ========================================================================= *)
(* The Bochner identity and the Kato inequality for a conformal harmonic    *)
(* map in a chart:                                                          *)
(*   Lap lam = B - 2K,  |grad lam|^2 <= lam B,  B = 2(|D_1 e|^2 + |D_2 e|^2)  *)
(* with lam = |e|^2, e = d_1 w, K = <e, R(e,f)f>.                           *)
(* ========================================================================= *)

let CML_GPOS = prove
 (`!V (G:real^3->real^3^3) y x. metric_field V G /\ y IN V
                                ==> &0 <= x dot (G y ** x) /\
                                    (x dot (G y ** x) = &0 <=> x = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v:real^3. ~(v = vec 0) ==> &0 < v dot ((G:real^3->real^3^3) y ** v)`
  ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Locality and linearity of the covariant derivative along w.              *)

let CML_COV_LOCAL = prove
 (`!(G:real^3->real^3^3) (w:real^2->real^3) W (X:real^2->real^3) Y a z.
     open W /\ z IN W /\ (!x. x IN W ==> X x = Y x)
     ==> cml_cov G w X a z = cml_cov G w Y a z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_cov] THEN BINOP_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `W:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

let CML_COV_ADD = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) (X:real^2->real^3) Y a z.
     metric_field V G /\ open W /\ (!z. z IN W ==> w z IN V) /\
     smooth_map_on W X /\ smooth_map_on W Y /\ z IN W
     ==> cml_cov G w (\x. X x + Y x) a z = cml_cov G w X a z + cml_cov G w Y a z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_cov] THEN
  SUBGOAL_THEN `!(Z:real^2->real^3). smooth_map_on W Z ==> Z differentiable (at z)`
  ASSUME_TAC THENL [ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE]; ALL_TAC] THEN
  ASM_SIMP_TAC[PARTIAL_DERIVATIVE_ADD] THEN
  SUBGOAL_THEN `bilinear (christoffel G ((w:real^2->real^3) z))` MP_TAC THENL
   [MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN EXISTS_TAC `V:real^3->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP BILINEAR_RADD th]) THEN VECTOR_ARITH_TAC);;

let CML_COV_ZERO = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) (X:real^2->real^3) a z.
     metric_field V G /\ open W /\ (!z. z IN W ==> w z IN V) /\ z IN W /\
     (!x. x IN W ==> X x = vec 0)
     ==> cml_cov G w X a z = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cml_cov G (w:real^2->real^3) (X:real^2->real^3) a z = cml_cov G w (\x. vec 0) a z`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CML_COV_LOCAL THEN EXISTS_TAC `W:real^2->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[cml_cov; PARTIAL_DERIVATIVE_CONST] THEN
  SUBGOAL_THEN `bilinear (christoffel G ((w:real^2->real^3) z))` MP_TAC THENL
   [MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN EXISTS_TAC `V:real^3->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP BILINEAR_RZERO th]) THEN
  REWRITE_TAC[VECTOR_ADD_LID]);;

(* Derivatives of G-inner products in drop form.                            *)

let CML_D_QUAD = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) (X:real^2->real^3) Y z a.
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     smooth_map_on W X /\ smooth_map_on W Y /\ z IN W
     ==> cml_d a (\z. X z dot (G(w z) ** Y z)) z =
         cml_cov G w X a z dot (G(w z) ** Y z) + X z dot (G(w z) ** cml_cov G w Y a z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_d] THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `W:real^2->bool`; `w:real^2->real^3`;
                 `X:real^2->real^3`; `Y:real^2->real^3`; `z:real^2`; `a:num`] CML_PD_METRIC) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

(* Bessel's inequality for a G-orthogonal pair of equal length.             *)

let CML_BESSEL = prove
 (`!V (G:real^3->real^3^3) y e f x lam.
     metric_field V G /\ y IN V /\
     e dot (G y ** e) = lam /\ f dot (G y ** f) = lam /\ e dot (G y ** f) = &0
     ==> (x dot (G y ** e)) pow 2 + (x dot (G y ** f)) pow 2 <= lam * (x dot (G y ** x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= lam` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `e dot ((G:real^3->real^3^3) y ** e) = lam`)) THEN
    ASM_MESON_TAC[CML_GPOS];
    ALL_TAC] THEN
  ASM_CASES_TAC `lam = &0` THENL
   [SUBGOAL_THEN `e:real^3 = vec 0 /\ f:real^3 = vec 0` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[CML_GPOS]; ALL_TAC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `p = x dot ((G:real^3->real^3^3) y ** e)` THEN
  ABBREV_TAC `q = x dot ((G:real^3->real^3^3) y ** f)` THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                 `lam % x - p % e - q % f:real^3`] CML_GPOS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `e dot ((G:real^3->real^3^3) y ** x) = p /\ f dot (G y ** x) = q /\
                f dot (G y ** e) = &0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_MESON_TAC[LRG_METRIC_SYM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= lam * (lam * (x dot ((G:real^3->real^3^3) y ** x)) - (p pow 2 + q pow 2))
                ==> p pow 2 + q pow 2 <= lam * (x dot (G y ** x))` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* The conformal factor and the curvature numerator in a chart.             *)

let cml_lamc = new_definition
 `cml_lamc (G:real^3->real^3^3) (w:real^2->real^3) (z:real^2) =
    partial_derivative 1 w z dot (G(w z) ** partial_derivative 1 w z)`;;

let cml_kk = new_definition
 `cml_kk (G:real^3->real^3^3) (w:real^2->real^3) (z:real^2) =
    partial_derivative 1 w z dot
    (G(w z) ** lriemann G (w z) (partial_derivative 1 w z) (partial_derivative 2 w z)
                         (partial_derivative 2 w z))`;;

let CML_D_ZERO = prove
 (`!W (u:real^2->real) a z.
     open W /\ z IN W /\ (!x. x IN W ==> u x = &0) ==> cml_d a u z = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cml_d a (u:real^2->real) z = cml_d a (\x. &0) z` SUBST1_TAC THENL
   [MATCH_MP_TAC CML_D_LOCAL THEN EXISTS_TAC `W:real^2->bool` THEN ASM_SIMP_TAC[];
    REWRITE_TAC[cml_d; LIFT_NUM; PARTIAL_DERIVATIVE_CONST; DROP_VEC]]);;

let CML_D_CMUL_AT = prove
 (`!(u:real^2->real) c a z.
     (\x. lift(u x)) differentiable (at z) ==> cml_d a (\x. c * u x) z = c * cml_d a u z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_d; LIFT_CMUL] THEN
  ASM_SIMP_TAC[PARTIAL_DERIVATIVE_CMUL; DROP_CMUL]);;

let CML_D_QUAD2 = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) (X:real^2->real^3) Y z a.
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     smooth_map_on W X /\ smooth_map_on W Y /\ z IN W
     ==> cml_d a (\z. &2 * (X z dot (G(w z) ** Y z))) z =
         &2 * (cml_cov G w X a z dot (G(w z) ** Y z) + X z dot (G(w z) ** cml_cov G w Y a z))`,
  REPEAT STRIP_TAC THEN
  W(fun (asl,g) -> MP_TAC(ISPECL [`\z. (X:real^2->real^3) z dot
                                         ((G:real^3->real^3^3)((w:real^2->real^3) z) ** (Y:real^2->real^3) z)`;
                                   `&2`; `a:num`; `z:real^2`] CML_D_CMUL_AT)) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CML_QUAD_SMOOTH THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CML_D_QUAD THEN EXISTS_TAC `V:real^3->bool` THEN
  EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[]);;

let CML_LAMC_D = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) z a.
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     z IN W
     ==> cml_d a (cml_lamc G w) z =
         &2 * (cml_cov G w (partial_derivative 1 w) a z dot
               (G(w z) ** partial_derivative 1 w z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cml_lamc G (w:real^2->real^3) =
                (\z. partial_derivative 1 w z dot (G(w z) ** partial_derivative 1 w z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; cml_lamc]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `W:real^2->bool`; `w:real^2->real^3`;
                 `partial_derivative 1 (w:real^2->real^3)`;
                 `partial_derivative 1 (w:real^2->real^3)`; `z:real^2`; `a:num`] CML_D_QUAD) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `(w:real^2->real^3) z`;
                 `partial_derivative 1 (w:real^2->real^3) z`;
                 `cml_cov G (w:real^2->real^3) (partial_derivative 1 w) a z`] LRG_METRIC_SYM) THEN
  ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;

let CML_LAMC_D2 = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) z a.
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     (!z. z IN W ==> partial_derivative 2 w z dot (G(w z) ** partial_derivative 2 w z) =
                     partial_derivative 1 w z dot (G(w z) ** partial_derivative 1 w z)) /\
     z IN W
     ==> cml_d a (cml_lamc G w) z =
         &2 * (cml_cov G w (partial_derivative 2 w) a z dot
               (G(w z) ** partial_derivative 2 w z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cml_d a (cml_lamc G (w:real^2->real^3)) z =
                cml_d a (\z. partial_derivative 2 w z dot (G(w z) ** partial_derivative 2 w z)) z`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CML_D_LOCAL THEN EXISTS_TAC `W:real^2->bool` THEN
    ASM_SIMP_TAC[cml_lamc];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `W:real^2->bool`; `w:real^2->real^3`;
                 `partial_derivative 2 (w:real^2->real^3)`;
                 `partial_derivative 2 (w:real^2->real^3)`; `z:real^2`; `a:num`] CML_D_QUAD) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `(w:real^2->real^3) z`;
                 `partial_derivative 2 (w:real^2->real^3) z`;
                 `cml_cov G (w:real^2->real^3) (partial_derivative 2 w) a z`] LRG_METRIC_SYM) THEN
  ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;

let CML_EF_D = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) z a.
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     (!z. z IN W ==> partial_derivative 1 w z dot (G(w z) ** partial_derivative 2 w z) = &0) /\
     z IN W
     ==> cml_cov G w (partial_derivative 1 w) a z dot (G(w z) ** partial_derivative 2 w z) +
         partial_derivative 1 w z dot (G(w z) ** cml_cov G w (partial_derivative 2 w) a z) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `W:real^2->bool`; `w:real^2->real^3`;
                 `partial_derivative 1 (w:real^2->real^3)`;
                 `partial_derivative 2 (w:real^2->real^3)`; `z:real^2`; `a:num`] CML_D_QUAD) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CML_D_ZERO THEN EXISTS_TAC `W:real^2->bool` THEN ASM_SIMP_TAC[]);;

let CML_KATO_ARITH = prove
 (`!d1 d2 a1 a2 b1 b2 lam n1 n2.
     d1 = &2 * a1 /\ d2 = &2 * a2 /\ d1 = &2 * b2 /\ d2 = -- &2 * b1 /\
     a1 pow 2 + b1 pow 2 <= lam * n1 /\ a2 pow 2 + b2 pow 2 <= lam * n2
     ==> d1 pow 2 + d2 pow 2 <= lam * (&2 * (n1 + n2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `b2:real = a1 /\ b1:real = --a2` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  ASM_REAL_ARITH_TAC);;

(* The Bochner identity and the Kato inequality.                             *)

let CML_BOCHNER = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) z.
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     (!z. z IN W ==> cml_cov G w (partial_derivative 1 w) 1 z +
                     cml_cov G w (partial_derivative 2 w) 2 z = vec 0) /\
     (!z. z IN W ==> partial_derivative 2 w z dot (G(w z) ** partial_derivative 2 w z) =
                     partial_derivative 1 w z dot (G(w z) ** partial_derivative 1 w z) /\
                     partial_derivative 1 w z dot (G(w z) ** partial_derivative 2 w z) = &0) /\
     z IN W
     ==> cml_lap (cml_lamc G w) z + &2 * cml_kk G w z =
         &2 * (cml_cov G w (partial_derivative 1 w) 1 z dot
               (G(w z) ** cml_cov G w (partial_derivative 1 w) 1 z) +
               cml_cov G w (partial_derivative 1 w) 2 z dot
               (G(w z) ** cml_cov G w (partial_derivative 1 w) 2 z)) /\
         &0 <= cml_lap (cml_lamc G w) z + &2 * cml_kk G w z /\
         cml_grad2 (cml_lamc G w) z <=
         cml_lamc G w z * (cml_lap (cml_lamc G w) z + &2 * cml_kk G w z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a. smooth_map_on W (partial_derivative a (w:real^2->real^3))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `!(X:real^2->real^3) a. smooth_map_on W X
                                       ==> smooth_map_on W (cml_cov G (w:real^2->real^3) X a)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_COV_SMOOTH THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN W ==> cml_cov G (w:real^2->real^3) (partial_derivative 1 w) 2 x =
                               cml_cov G w (partial_derivative 2 w) 1 x`
  (LABEL_TAC "TOR") THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CML_TORSION THEN
    EXISTS_TAC `V:real^3->bool` THEN EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN W ==> cml_cov G (w:real^2->real^3) (partial_derivative 2 w) 2 x =
                               --(cml_cov G w (partial_derivative 1 w) 1 x)`
  (LABEL_TAC "HAR") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(VECTOR_ARITH `a + b:real^3 = vec 0 ==> b = --a`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* first derivatives of lam *)
  SUBGOAL_THEN `!a. cml_d a (cml_lamc G (w:real^2->real^3)) z =
                    &2 * (cml_cov G w (partial_derivative 1 w) a z dot
                          (G(w z) ** partial_derivative 1 w z))`
  (LABEL_TAC "D1") THENL
   [GEN_TAC THEN MATCH_MP_TAC CML_LAMC_D THEN EXISTS_TAC `V:real^3->bool` THEN
    EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. cml_d a (cml_lamc G (w:real^2->real^3)) z =
                    &2 * (cml_cov G w (partial_derivative 2 w) a z dot
                          (G(w z) ** partial_derivative 2 w z))`
  (LABEL_TAC "D2") THENL
   [GEN_TAC THEN MATCH_MP_TAC CML_LAMC_D2 THEN EXISTS_TAC `V:real^3->bool` THEN
    EXISTS_TAC `W:real^2->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* second derivatives of lam *)
  SUBGOAL_THEN
   `cml_d 1 (cml_d 1 (cml_lamc G (w:real^2->real^3))) z =
    &2 * (cml_cov G w (cml_cov G w (partial_derivative 1 w) 1) 1 z dot
          (G(w z) ** partial_derivative 1 w z) +
          cml_cov G w (partial_derivative 1 w) 1 z dot
          (G(w z) ** cml_cov G w (partial_derivative 1 w) 1 z))`
  (LABEL_TAC "DD1") THENL
   [SUBGOAL_THEN
     `cml_d 1 (cml_d 1 (cml_lamc G (w:real^2->real^3))) z =
      cml_d 1 (\x. &2 * (cml_cov G w (partial_derivative 1 w) 1 x dot
                         (G(w x) ** partial_derivative 1 w x))) z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CML_D_LOCAL THEN EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC CML_LAMC_D THEN
      EXISTS_TAC `V:real^3->bool` THEN EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CML_D_QUAD2 THEN EXISTS_TAC `V:real^3->bool` THEN
      EXISTS_TAC `W:real^2->bool` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cml_d 2 (cml_d 2 (cml_lamc G (w:real^2->real^3))) z =
    &2 * (cml_cov G w (cml_cov G w (partial_derivative 1 w) 2) 2 z dot
          (G(w z) ** partial_derivative 1 w z) +
          cml_cov G w (partial_derivative 1 w) 2 z dot
          (G(w z) ** cml_cov G w (partial_derivative 1 w) 2 z))`
  (LABEL_TAC "DD2") THENL
   [SUBGOAL_THEN
     `cml_d 2 (cml_d 2 (cml_lamc G (w:real^2->real^3))) z =
      cml_d 2 (\x. &2 * (cml_cov G w (partial_derivative 1 w) 2 x dot
                         (G(w x) ** partial_derivative 1 w x))) z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CML_D_LOCAL THEN EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC CML_LAMC_D THEN
      EXISTS_TAC `V:real^3->bool` THEN EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CML_D_QUAD2 THEN EXISTS_TAC `V:real^3->bool` THEN
      EXISTS_TAC `W:real^2->bool` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* D_2 D_2 e = - D_1 D_1 e - R(e,f)f *)
  SUBGOAL_THEN
   `cml_cov G (w:real^2->real^3) (cml_cov G w (partial_derivative 1 w) 2) 2 z =
    --(cml_cov G w (cml_cov G w (partial_derivative 1 w) 1) 1 z) -
    lriemann G (w z) (partial_derivative 1 w z) (partial_derivative 2 w z)
             (partial_derivative 2 w z)`
  (LABEL_TAC "E22") THENL
   [SUBGOAL_THEN
     `cml_cov G (w:real^2->real^3) (cml_cov G w (partial_derivative 1 w) 2) 2 z =
      cml_cov G w (cml_cov G w (partial_derivative 2 w) 1) 2 z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CML_COV_LOCAL THEN EXISTS_TAC `W:real^2->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `W:real^2->bool`;
                   `w:real^2->real^3`; `partial_derivative 2 (w:real^2->real^3)`; `z:real^2`]
                  CML_COMMUTATOR) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `cml_cov G (w:real^2->real^3) (cml_cov G w (partial_derivative 2 w) 2) 1 z =
      --(cml_cov G w (cml_cov G w (partial_derivative 1 w) 1) 1 z)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `W:real^2->bool`;
                     `w:real^2->real^3`;
                     `cml_cov G (w:real^2->real^3) (partial_derivative 1 w) 1`;
                     `cml_cov G (w:real^2->real^3) (partial_derivative 2 w) 2`;
                     `1`; `z:real^2`] CML_COV_ADD) THEN
      ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `W:real^2->bool`;
                     `w:real^2->real^3`;
                     `\x. cml_cov G (w:real^2->real^3) (partial_derivative 1 w) 1 x +
                          cml_cov G w (partial_derivative 2 w) 2 x`;
                     `1`; `z:real^2`] CML_COV_ZERO) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  (* the Bochner identity *)
  SUBGOAL_THEN
   `cml_lap (cml_lamc G (w:real^2->real^3)) z + &2 * cml_kk G w z =
    &2 * (cml_cov G w (partial_derivative 1 w) 1 z dot
          (G(w z) ** cml_cov G w (partial_derivative 1 w) 1 z) +
          cml_cov G w (partial_derivative 1 w) 2 z dot
          (G(w z) ** cml_cov G w (partial_derivative 1 w) 2 z))`
  (LABEL_TAC "BOCH") THENL
   [REWRITE_TAC[cml_lap] THEN USE_THEN "DD1" SUBST1_TAC THEN USE_THEN "DD2" SUBST1_TAC THEN
    USE_THEN "E22" SUBST1_TAC THEN REWRITE_TAC[cml_kk; DOT_LSUB; DOT_LNEG] THEN
    MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `(w:real^2->real^3) z`;
                   `partial_derivative 1 (w:real^2->real^3) z`;
                   `lriemann G ((w:real^2->real^3) z) (partial_derivative 1 w z)
                             (partial_derivative 2 w z) (partial_derivative 2 w z)`]
                  LRG_METRIC_SYM) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_ADD THEN
    ASM_MESON_TAC[CML_GPOS];
    ALL_TAC] THEN
  (* Kato *)
  REWRITE_TAC[cml_grad2] THEN MATCH_MP_TAC CML_KATO_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`cml_cov G (w:real^2->real^3) (partial_derivative 1 w) 1 z dot
     (G(w z) ** partial_derivative 1 w z)`;
    `cml_cov G (w:real^2->real^3) (partial_derivative 1 w) 2 z dot
     (G(w z) ** partial_derivative 1 w z)`;
    `cml_cov G (w:real^2->real^3) (partial_derivative 1 w) 1 z dot
     (G(w z) ** partial_derivative 2 w z)`;
    `cml_cov G (w:real^2->real^3) (partial_derivative 1 w) 2 z dot
     (G(w z) ** partial_derivative 2 w z)`] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "D1" (fun th -> REWRITE_TAC[th]);
    USE_THEN "D1" (fun th -> REWRITE_TAC[th]);
    USE_THEN "D2" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "TOR" (fun th ->
      ASM_SIMP_TAC[th]);
    USE_THEN "D2" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "HAR" (fun th ->
      ASM_SIMP_TAC[th]) THEN REWRITE_TAC[DOT_LNEG] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC CML_BESSEL THEN EXISTS_TAC `V:real^3->bool` THEN
    REWRITE_TAC[cml_lamc] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC CML_BESSEL THEN EXISTS_TAC `V:real^3->bool` THEN
    REWRITE_TAC[cml_lamc] THEN ASM_SIMP_TAC[]]);;

(* The Hopf differential (|e|^2 - |f|^2, -2<e,f>) satisfies the Cauchy-      *)
(* Riemann equations for a harmonic map.                                     *)

let CML_D_SUB_AT = prove
 (`!(u:real^2->real) u' a z.
     (\x. lift(u x)) differentiable (at z) /\ (\x. lift(u' x)) differentiable (at z)
     ==> cml_d a (\x. u x - u' x) z = cml_d a u z - cml_d a u' z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_d; LIFT_SUB] THEN
  ASM_SIMP_TAC[PARTIAL_DERIVATIVE_SUB; DROP_SUB]);;

let CML_HOPF_CR = prove
 (`!V (G:real^3->real^3^3) W (w:real^2->real^3) z.
     metric_field V G /\ open W /\ smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\
     (!z. z IN W ==> cml_cov G w (partial_derivative 1 w) 1 z +
                     cml_cov G w (partial_derivative 2 w) 2 z = vec 0) /\
     z IN W
     ==> cml_d 1 (\z. partial_derivative 1 w z dot (G(w z) ** partial_derivative 1 w z) -
                      partial_derivative 2 w z dot (G(w z) ** partial_derivative 2 w z)) z =
         -- &2 * cml_d 2 (\z. partial_derivative 1 w z dot
                              (G(w z) ** partial_derivative 2 w z)) z /\
         cml_d 2 (\z. partial_derivative 1 w z dot (G(w z) ** partial_derivative 1 w z) -
                      partial_derivative 2 w z dot (G(w z) ** partial_derivative 2 w z)) z =
         &2 * cml_d 1 (\z. partial_derivative 1 w z dot
                           (G(w z) ** partial_derivative 2 w z)) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a. smooth_map_on W (partial_derivative a (w:real^2->real^3))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. (\x. lift(partial_derivative a (w:real^2->real^3) x dot
                    (G(w x) ** partial_derivative b w x))) differentiable (at z)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CML_QUAD_SMOOTH THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CML_D_SUB_AT] THEN
  SUBGOAL_THEN
   `!a b c. cml_d c (\x. partial_derivative a (w:real^2->real^3) x dot
                         (G(w x) ** partial_derivative b w x)) z =
            cml_cov G w (partial_derivative a w) c z dot (G(w z) ** partial_derivative b w z) +
            partial_derivative a w z dot (G(w z) ** cml_cov G w (partial_derivative b w) c z)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC CML_D_QUAD THEN EXISTS_TAC `V:real^3->bool` THEN
    EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cml_cov G (w:real^2->real^3) (partial_derivative 2 w) 1 z =
                cml_cov G w (partial_derivative 1 w) 2 z /\
                cml_cov G (w:real^2->real^3) (partial_derivative 2 w) 2 z =
                --(cml_cov G w (partial_derivative 1 w) 1 z)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CML_TORSION THEN EXISTS_TAC `V:real^3->bool` THEN
      EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(VECTOR_ARITH `a + b:real^3 = vec 0 ==> b = --a`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x u. x dot ((G:real^3->real^3^3)((w:real^2->real^3) z) ** u) =
                      u dot (G(w z) ** x)`
  ASSUME_TAC THENL [ASM_MESON_TAC[LRG_METRIC_SYM]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_LNEG; DOT_RNEG] THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPECL [`partial_derivative 1 (w:real^2->real^3) z`;
                                      `cml_cov G (w:real^2->real^3) (partial_derivative 1 w) 1 z`] th) THEN
                        MP_TAC(SPECL [`partial_derivative 2 (w:real^2->real^3) z`;
                                      `cml_cov G (w:real^2->real^3) (partial_derivative 1 w) 2 z`] th) THEN
                        MP_TAC(SPECL [`partial_derivative 1 (w:real^2->real^3) z`;
                                      `cml_cov G (w:real^2->real^3) (partial_derivative 1 w) 2 z`] th) THEN
                        MP_TAC(SPECL [`partial_derivative 2 (w:real^2->real^3) z`;
                                      `cml_cov G (w:real^2->real^3) (partial_derivative 1 w) 1 z`] th)) THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Tools for the Euler-Lagrange equation.  Scaling of derivatives of        *)
(* 0-homogeneous maps, the trace of a bilinear form in an orthonormal basis *)
(* and in the stereographic frame (P z, dP e1, dP e2), integrals of         *)
(* derivatives of compactly supported functions, and positivity of          *)
(* integrals.                                                               *)
(* ========================================================================= *)

let CML_HOMOG_PD = prove
 (`!(u:real^3->real^N) y t i.
     &0 < t /\ ~(y = vec 0) /\ (!x. ~(x = vec 0) ==> u(t % x) = u x) /\
     u differentiable (at y)
     ==> partial_derivative i u (t % y) = inv t % partial_derivative i u y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. ~(x = vec 0) ==> (u:real^3->real^N) x = (u o (\x. inv t % x)) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv t % x:real^3`) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                 VECTOR_MUL_EQ_0; REAL_INV_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t % y:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `partial_derivative i (u:real^3->real^N) (t % y) =
                partial_derivative i (u o (\x. inv t % x)) (t % y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; SET_RULE `{x | ~(x = a)} = (:real^3) DELETE a`;
                 OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x:real^3. inv t % x) has_derivative (\x. inv t % x)) (at (t % y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv t % t % y:real^3 = y` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((u:real^3->real^N) o (\x. inv t % x) has_derivative
     frechet_derivative u (at y) o (\x. inv t % x)) (at (t % y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE th]) THEN
  REWRITE_TAC[o_THM; partial_derivative] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN SIMP_TAC[LINEAR_CMUL]);;

(* The trace of a matrix in an orthonormal basis of R^3.                    *)

let CML_TRACE_ONB = prove
 (`!(N:real^3^3) b1 b2 b3.
     b1 dot b1 = &1 /\ b2 dot b2 = &1 /\ b3 dot b3 = &1 /\
     b1 dot b2 = &0 /\ b1 dot b3 = &0 /\ b2 dot b3 = &0
     ==> trace N = b1 dot (N ** b1) + b2 dot (N ** b2) + b3 dot (N ** b3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(vector[b1:real^3;b2;b3]:real^3^3) ** transp(vector[b1;b2;b3]:real^3^3) = mat 1`
  ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[dot; DIMINDEX_3; SUM_3]) THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; matrix_mul; transp; mat; LAMBDA_BETA; ARITH;
             VECTOR_3; SUM_3] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `transp(vector[b1:real^3;b2;b3]:real^3^3) ** (vector[b1;b2;b3]:real^3^3) = mat 1`
  ASSUME_TAC THENL [ASM_MESON_TAC[MATRIX_LEFT_RIGHT_INVERSE]; ALL_TAC] THEN
  SUBGOAL_THEN `trace(N:real^3^3) =
                trace((vector[b1:real^3;b2;b3]:real^3^3) ** (N ** transp(vector[b1;b2;b3]:real^3^3)))`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[TRACE_MUL_SYM] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_MUL_RID];
    ALL_TAC] THEN
  SIMP_TAC[trace; SUM_3; DIMINDEX_3; matrix_mul; transp; LAMBDA_BETA; ARITH; dot;
           matrix_vector_mul; VECTOR_3] THEN
  REAL_ARITH_TAC);;

(* The trace of a bilinear form killing the radial direction, in the       *)
(* stereographic frame.                                                       *)

let CML_FRAME_SUM = prove
 (`!(P:real^3->real^3) (Q:real^3->real^3) (M:real^3^3) z.
     linear P /\ linear Q /\ P(stereo2_n_inv z) = vec 0
     ==> sum(1..3) (\i. P(basis i) dot (M ** Q(basis i))) =
         inv(cml_rho z) * (P(bel_dP z (basis 1)) dot (M ** Q(bel_dP z (basis 1))) +
                           P(bel_dP z (basis 2)) dot (M ** Q(bel_dP z (basis 2))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `N = transp(matrix(P:real^3->real^3)) ** (M:real^3^3) ** matrix(Q:real^3->real^3)` THEN
  SUBGOAL_THEN `!x:real^3. x dot ((N:real^3^3) ** x) =
                          (P:real^3->real^3) x dot ((M:real^3^3) ** (Q:real^3->real^3) x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "N" THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
    ASM_SIMP_TAC[MATRIX_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(1..3) (\i. (P:real^3->real^3)(basis i) dot
                                ((M:real^3^3) ** (Q:real^3->real^3)(basis i))) =
                trace(N:real^3^3)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
    SIMP_TAC[trace; DIMINDEX_3; SUM_3; DOT_BASIS; MATRIX_VECTOR_MUL_BASIS; column;
             LAMBDA_BETA; ARITH; transp];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cml_rho z` ASSUME_TAC THENL
   [REWRITE_TAC[cml_rho] THEN MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_POW_LT THEN
    MP_TAC(SPEC `norm(z:real^2) pow 2` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `norm(z:real^2)` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s = inv(sqrt(cml_rho z))` THEN
  SUBGOAL_THEN `s pow 2 = inv(cml_rho z)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[REAL_POW_INV] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!h k. bel_dP z h dot bel_dP z k = cml_rho z * (h dot k)` ASSUME_TAC THENL
   [REWRITE_TAC[BEL_P_CONF; cml_rho]; ALL_TAC] THEN
  MP_TAC(ISPECL [`N:real^3^3`; `stereo2_n_inv z`; `s % bel_dP z (basis 1)`;
                 `s % bel_dP z (basis 2)`] CML_TRACE_ONB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DOT_LMUL; DOT_RMUL; BEL_P_NORM; BEL_P_TANG] THEN
    SIMP_TAC[DOT_BASIS; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_MUL_ASSOC; GSYM REAL_POW_2] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `z:real^2` BEL_DP_LINEAR) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[LINEAR_CMUL; MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL; DOT_LZERO] THEN
  UNDISCH_TAC `s pow 2 = inv(cml_rho z)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Compact support.                                                          *)

let CML_CSUPP_ABSINT = prove
 (`!(f:real^2->real^N) k.
     f continuous_on (:real^2) /\ compact k /\ (!x. ~(x IN k) ==> f x = vec 0)
     ==> f absolutely_integrable_on (:real^2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^2` (X_CHOOSE_TAC `b:real^2`)) THEN
  SUBGOAL_THEN `(f:real^2->real^N) absolutely_integrable_on interval[a,b]` MP_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(\x. if x IN interval[a,b] then (f:real^2->real^N) x else vec 0)
                absolutely_integrable_on (:real^2)` MP_TAC THENL
   [ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ABSOLUTELY_INTEGRABLE_EQ) THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_UNIV] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let CML_DIV_ZERO = prove
 (`!(h:real^2->real) k a.
     smooth_map_on (:real^2) (\x. lift(h x)) /\ compact k /\ (!x. ~(x IN k) ==> h x = &0)
     ==> (\x. lift(cml_d a h x)) absolutely_integrable_on (:real^2) /\
         integral (:real^2) (\x. lift(cml_d a h x)) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. ~(x IN k) ==> cml_d a (h:real^2->real) x = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_D_ZERO THEN
    EXISTS_TAC `(:real^2) DIFF k` THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CML_CSUPP_ABSINT THEN EXISTS_TAC `k:real^2->bool` THEN
    ASM_SIMP_TAC[LIFT_NUM] THEN REWRITE_TAC[cml_d; LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^2. &1`; `&0`; `h:real^2->real`; `k:real^2->bool`;
                 `basis a:real^2`] WAN_LIP_IBP_UNIV) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_MUL_LZERO; REAL_LE_REFL] THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_CONST_AT; DROP_VEC; REAL_MUL_LZERO; LIFT_NUM;
              INTEGRAL_0; VECTOR_NEG_0; REAL_MUL_LID] THEN
  REWRITE_TAC[cml_d; partial_derivative; LIFT_DROP] THEN SIMP_TAC[]);;

(* An integral of a nonnegative continuous function which is positive at   *)
(* some point is positive.                                                   *)

let CML_INTEGRAL_POS = prove
 (`!(h:real^2->real) z0.
     (\x. lift(h x)) continuous_on (:real^2) /\ (!x. &0 <= h x) /\ &0 < h z0 /\
     (\x. lift(h x)) integrable_on (:real^2)
     ==> &0 < drop(integral (:real^2) (\x. lift(h x)))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z0:real^2` o REWRITE_RULE[continuous_on] o
    check (fun th -> is_binary "continuous_on" (concl th))) THEN
  REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(MP_TAC o SPEC `(h:real^2->real) z0 / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN ball(z0:real^2,r) ==> (h:real^2->real) z0 / &2 <= h x` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[DIST_LIFT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `drop(integral (ball(z0:real^2,r)) (\x. lift((h:real^2->real) z0 / &2)))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[MEASURE_BALL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (ball(z0:real^2,r)) (\x. lift((h:real^2->real) x)))` THEN
  SUBGOAL_THEN `(\x. lift((h:real^2->real) x)) integrable_on ball(z0,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN REWRITE_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_BALL] THEN
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    ASM_REWRITE_TAC[IN_UNIV; DIMINDEX_1; FORALL_1; GSYM drop; LIFT_DROP];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[LIFT_DROP; MEASURABLE_BALL;
                                                     INTEGRABLE_ON_CONST];
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[SUBSET_UNIV; LIFT_DROP]]);;

(* ========================================================================= *)
(* The variation of a map of S^2 in one chart.  For a chart (U,phi), a      *)
(* 0-homogeneous test field eta (vanishing on an open set E covering the    *)
(* points outside the chart) and an embedding f of the manifold, cml_fam is *)
(* the family                                                               *)
(*   (s,y) |-> f(phi^-1(phi(v(y/|y|)) + s eta(y)))                          *)
(* of maps into the embedded manifold, as needed by CMT_FV_ZERO.            *)
(* ========================================================================= *)

let cml_fam = new_definition
 `cml_fam (f:A->real^K) (c:(A->bool)#(A->real^3)) (v:real^3->A) (eta:real^3->real^3)
          (x:real^(1,3)finite_sum) =
    if v(inv(norm(sndcart x)) % sndcart x) IN FST c
    then f(chart_inv c (SND c (v(inv(norm(sndcart x)) % sndcart x)) +
                        drop(fstcart x) % eta(sndcart x)))
    else f(v(inv(norm(sndcart x)) % sndcart x))`;;

let CML_SNDCART_COMPOSE = prove
 (`!s t (g:real^3->real^N).
     open s /\ open t /\ (!x:real^(1,3)finite_sum. x IN s ==> sndcart x IN t) /\
     smooth_map_on t g
     ==> smooth_map_on s (\x. g(sndcart x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^(1,3)finite_sum. (g:real^3->real^N)(sndcart x)) = g o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `t:real^3->bool` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  SUBGOAL_THEN `sndcart = (sndcart:real^(1,3)finite_sum->real^3) o (\x. x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  ASM_REWRITE_TAC[LINEAR_SNDCART; SMOOTH_MAP_ON_ID]);;

let CML_FSTCART_SMOOTH = prove
 (`!s. smooth_map_on s (fstcart:real^(1,3)finite_sum->real^1)`,
  GEN_TAC THEN
  SUBGOAL_THEN `fstcart = (fstcart:real^(1,3)finite_sum->real^1) o (\x. x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,3)finite_sum)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  REWRITE_TAC[LINEAR_FSTCART; SMOOTH_MAP_ON_ID; OPEN_UNIV]);;

let CML_FAM_SMOOTH = prove
 (`!top atlas (f:A->real^K) (v:real^3->A) U phi (eta:real^3->real^3) E.
     smooth_manifold_atlas top atlas /\ smooth_immersion_into atlas f /\
     p4_s2_smooth (top,atlas) v /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (f o v)) /\
     (U,phi) IN atlas /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} eta /\
     open E /\ (!y. y IN E ==> eta y = vec 0) /\
     (!y. ~(y = vec 0) ==> v(inv(norm y) % y) IN U \/ y IN E) /\
     (!y s. ~(y = vec 0) /\ v(inv(norm y) % y) IN U /\ abs s < &1
            ==> phi(v(inv(norm y) % y)) + s % eta y IN IMAGE phi U)
     ==> smooth_map_on {x | drop(fstcart x) IN real_interval(--(&1),&1) /\
                            ~(sndcart x = vec 0)}
                       (cml_fam f (U,phi) v eta)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p4_s2_smooth]) THEN
  ABBREV_TAC `D = {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                            ~(sndcart x = vec 0)}` THEN
  SUBGOAL_THEN `open(D:real^(1,3)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[CMT_TIME_OPEN]; ALL_TAC] THEN
  ABBREV_TAC `C = {z:real^3 | ~(z = vec 0) /\ (v:real^3->A)(inv(norm z) % z) IN U}` THEN
  SUBGOAL_THEN `open(C:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `v:real^3->A`;
                   `(U:A->bool,phi:A->real^3)`] P4_RADIAL_CHART_OPEN) THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^3 | ~(z = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `{x | ~(x = a)} = (:real^3) DELETE a`] THEN
    SIMP_TAC[OPEN_DELETE; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. open s ==> open {x:real^(1,3)finite_sum | x IN D /\ sndcart x IN s}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[SET_RULE `{x:real^(1,3)finite_sum | x IN D /\ P x} = D INTER {x | P x}`] THEN
    MATCH_MP_TAC OPEN_INTER THEN ASM_SIMP_TAC[CMT_SNDCART_OPEN];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^(1,3)finite_sum. x IN D ==> ~(sndcart x = vec 0) /\
                                                abs(drop(fstcart x)) < &1`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x0:real^(1,3)finite_sum` THEN DISCH_TAC THEN
  ASM_CASES_TAC `sndcart(x0:real^(1,3)finite_sum) IN C` THENL
   [EXISTS_TAC `{x:real^(1,3)finite_sum | x IN D /\ sndcart x IN C}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `((f:A->real^K) o chart_inv (U,phi)) o
                (\x:real^(1,3)finite_sum. (phi:A->real^3)((v:real^3->A)(inv(norm(sndcart x)) %
                                                              sndcart x)) +
                                          drop(fstcart x) % (eta:real^3->real^3)(sndcart x))` THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^(1,3)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      UNDISCH_TAC `sndcart(x:real^(1,3)finite_sum) IN C` THEN EXPAND_TAC "C" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[cml_fam; FST; SND; o_THM];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `f:A->real^K`;
                   `(U:A->bool,phi:A->real^3)`] GRGE_IMMERSION_CHART) THEN
    ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^(1,3)finite_sum` THEN STRIP_TAC THEN
      UNDISCH_TAC `sndcart(x:real^(1,3)finite_sum) IN C` THEN EXPAND_TAC "C" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`{x:real^(1,3)finite_sum | x IN D /\ sndcart x IN C}`; `C:real^3->bool`;
                       `\z:real^3. (phi:A->real^3)((v:real^3->A)(inv(norm z) % z))`]
                      CML_SNDCART_COMPOSE) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[IN_ELIM_THM] THEN
        EXPAND_TAC "C" THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN
        ASM_REWRITE_TAC[FST; SND];
        MP_TAC(ISPECL [`{x:real^(1,3)finite_sum | x IN D /\ sndcart x IN C}`;
                       `fstcart:real^(1,3)finite_sum->real^1`;
                       `\x:real^(1,3)finite_sum. (eta:real^3->real^3)(sndcart x)`]
                      SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[CML_FSTCART_SMOOTH] THEN
        MATCH_MP_TAC CML_SNDCART_COMPOSE THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
        ASM_SIMP_TAC[IN_ELIM_THM]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sndcart(x0:real^(1,3)finite_sum) IN E` ASSUME_TAC THENL
   [UNDISCH_TAC `~(sndcart(x0:real^(1,3)finite_sum) IN C)` THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{x:real^(1,3)finite_sum | x IN D /\ sndcart x IN E}` THEN
  ASM_SIMP_TAC[IN_ELIM_THM] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\x:real^(1,3)finite_sum. wan_rext ((f:A->real^K) o (v:real^3->A)) (sndcart x)` THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^(1,3)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[cml_fam; FST; SND; wan_rext; o_THM; VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                   `phi:A->real^3`] CHART_INV) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC CML_SNDCART_COMPOSE THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; ETA_AX]]);;

(* Homogeneity, values in the embedded manifold, and the value at s = 0.    *)

let CML_NRM_SCALE = prove
 (`!t (y:real^3). &0 < t ==> inv(norm(t % y)) % (t % y) = inv(norm y) % y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC; REAL_INV_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_CASES_TAC `y:real^3 = vec 0` THEN
  ASM_SIMP_TAC[NORM_0; REAL_INV_0; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  REWRITE_TAC[REAL_ARITH `(a * b) * t = b * (a * t)`] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID]);;

let CML_FAM_PROPS = prove
 (`!top atlas (f:A->real^K) (v:real^3->A) U phi (eta:real^3->real^3).
     smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
     (!y. y IN sphere(vec 0,&1) ==> v y IN topspace top) /\
     (!t y. &0 < t /\ ~(y = vec 0) ==> eta(t % y) = eta y) /\
     (!y s. ~(y = vec 0) /\ v(inv(norm y) % y) IN U /\ abs s < &1
            ==> phi(v(inv(norm y) % y)) + s % eta y IN IMAGE phi U)
     ==> (!x t. drop(fstcart x) IN real_interval(--(&1),&1) /\ ~(sndcart x = vec 0) /\
                &0 < t
                ==> cml_fam f (U,phi) v eta (pastecart (fstcart x) (t % sndcart x)) =
                    cml_fam f (U,phi) v eta x) /\
         (!x. drop(fstcart x) IN real_interval(--(&1),&1) /\ ~(sndcart x = vec 0)
              ==> cml_fam f (U,phi) v eta x IN IMAGE f (topspace top)) /\
         (!y. ~(y = vec 0) ==> cml_fam f (U,phi) v eta (pastecart (lift(&0)) y) =
                               wan_rext (f o v) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^3. ~(y = vec 0) ==> inv(norm y) % y IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[cml_fam; FSTCART_PASTECART; SNDCART_PASTECART; CML_NRM_SCALE];
    X_GEN_TAC `x:real^(1,3)finite_sum` THEN STRIP_TAC THEN
    REWRITE_TAC[cml_fam; FST; SND] THEN COND_CASES_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THENL
     [SUBGOAL_THEN `(phi:A->real^3)((v:real^3->A)(inv(norm(sndcart(x:real^(1,3)finite_sum))) %
                                                   sndcart x)) +
                    drop(fstcart x) % (eta:real^3->real^3)(sndcart x) IN IMAGE phi U`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `drop(fstcart(x:real^(1,3)finite_sum)) IN real_interval(--(&1),&1)` THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` MP_TAC THENL
       [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[]];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[cml_fam; FSTCART_PASTECART; SNDCART_PASTECART; FST; SND; DROP_VEC; LIFT_NUM;
                VECTOR_MUL_LZERO; VECTOR_ADD_RID; wan_rext; o_THM] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* The energy density of the chart family and its first variation at s = 0, *)
(* computed in the chart:                                                   *)
(*   psi(s,y) = sum_i |d_i w3 + s d_i eta|^2 at w3 + s eta  (metric_local), *)
(*   d/ds psi(0,y) = 2 sum_i <d_i eta + Gamma(eta, d_i w3), d_i w3>.        *)
(* ========================================================================= *)

let cml_famhyp = new_definition
 `cml_famhyp (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
             (f:A->real^K) (G:real^K->real^K^K) (d:real) (v:real^3->A)
             (c:(A->bool)#(A->real^3)) (eta:real^3->real^3) (E:real^3->bool) <=>
    cm_emb (top,atlas) g f G d /\ p4_s2_smooth (top,atlas) v /\
    (!y. y IN sphere(vec 0,&1) ==> v y IN topspace top) /\
    smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (f o v)) /\
    c IN atlas /\ smooth_map_on {z:real^3 | ~(z = vec 0)} eta /\
    (!t y. &0 < t /\ ~(y = vec 0) ==> eta(t % y) = eta y) /\
    open E /\ (!y. y IN E ==> eta y = vec 0) /\
    (!y. ~(y = vec 0) ==> v(inv(norm y) % y) IN FST c \/ y IN E) /\
    (!y s. ~(y = vec 0) /\ v(inv(norm y) % y) IN FST c /\ abs s < &1
           ==> SND c (v(inv(norm y) % y)) + s % eta y IN IMAGE (SND c) (FST c))`;;

let CML_FAMHYP_SMOOTH = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d v U phi eta E.
     cml_famhyp (top,atlas) g f G d v (U,phi) eta E
     ==> smooth_map_on {x | drop(fstcart x) IN real_interval(--(&1),&1) /\
                            ~(sndcart x = vec 0)}
                       (cml_fam f (U,phi) v eta)`,
  REWRITE_TAC[cml_famhyp; cm_emb; mfd_embedding; FST; SND] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CML_FAM_SMOOTH THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `E:real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* The chart metric as the pullback of the ambient metric.                  *)

let CML_EMB_QUAD = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) (G:real^K->real^K^K) d U phi p u.
     cm_emb (top,atlas) g f G d /\ (U,phi) IN atlas /\ p IN IMAGE phi U
     ==> frechet_derivative (f o chart_inv (U:A->bool,phi:A->real^3)) (at p) u dot
         (G(f(chart_inv (U:A->bool,phi:A->real^3) p)) ** frechet_derivative (f o chart_inv (U:A->bool,phi:A->real^3)) (at p) u) =
         u dot (metric_local atlas (U,phi) g p ** u)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  SUBGOAL_THEN `smooth_immersion_into (atlas:((A->bool)#(A->real^3))->bool) (f:A->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_embedding]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `f:A->real^K`;
                 `(U:A->bool,phi:A->real^3)`] GRGE_IMMERSION_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative ((f:A->real^K) o chart_inv (U:A->bool,phi:A->real^3)) (at (p:real^3)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(U:A->bool,phi:A->real^3)`; `p:real^3`]) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS; o_THM]);;

(* The spatial derivatives of the family in the chart.                      *)

let CML_FAM_PD = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) U phi
    (eta:real^3->real^3) E y s i.
     cml_famhyp (top,atlas) g f G d v (U,phi) eta E /\
     ~(y = vec 0) /\ v(inv(norm y) % y) IN U /\ abs s < &1 /\ 1 <= i /\ i <= 3
     ==> partial_derivative (i + 1) (cml_fam f (U,phi) v eta) (pastecart (lift s) y) =
         frechet_derivative (f o chart_inv (U:A->bool,phi:A->real^3))
           (at (phi(v(inv(norm y) % y)) + s % eta y))
           (partial_derivative i (\z. phi(v(inv(norm z) % z))) y +
            s % partial_derivative i eta y) /\
         cml_fam f (U,phi) v eta (pastecart (lift s) y) =
         (f o chart_inv (U:A->bool,phi:A->real^3)) (phi(v(inv(norm y) % y)) + s % eta y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CML_FAMHYP_SMOOTH) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FST; SND] o GEN_REWRITE_RULE I [cml_famhyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  SUBGOAL_THEN `smooth_immersion_into (atlas:((A->bool)#(A->real^3))->bool) (f:A->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_embedding]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p4_s2_smooth]) THEN
  ABBREV_TAC `C = {z:real^3 | ~(z = vec 0) /\ (v:real^3->A)(inv(norm z) % z) IN U}` THEN
  SUBGOAL_THEN `open(C:real^3->bool) /\ (y:real^3) IN C` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `v:real^3->A`;
                   `(U:A->bool,phi:A->real^3)`] P4_RADIAL_CHART_OPEN) THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on C (\z:real^3. (phi:A->real^3)((v:real^3->A)(inv(norm z) % z)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^3 | ~(z = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `{x | ~(x = a)} = (:real^3) DELETE a`] THEN
    SIMP_TAC[OPEN_DELETE; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^3. (phi:A->real^3)((v:real^3->A)(inv(norm z) % z))) differentiable at y /\
                (eta:real^3->real^3) differentiable at y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `C:real^3->bool`; EXISTS_TAC `{z:real^3 | ~(z = vec 0)}`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^3)((v:real^3->A)(inv(norm(y:real^3)) % y)) + s % (eta:real^3->real^3) y
                IN IMAGE phi U` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `f:A->real^K`;
                 `(U:A->bool,phi:A->real^3)`] GRGE_IMMERSION_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((f:A->real^K) o chart_inv (U:A->bool,phi:A->real^3)) differentiable
                at ((phi:A->real^3)((v:real^3->A)(inv(norm(y:real^3)) % y)) +
                    s % (eta:real^3->real^3) y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN C ==> cml_fam (f:A->real^K) (U,phi) (v:real^3->A) (eta:real^3->real^3)
                           (pastecart (lift s) z) =
                   ((f o chart_inv (U:A->bool,phi:A->real^3)) o
                    (\z. (phi:A->real^3)(v(inv(norm z) % z)) + s % eta z)) z`
  ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[cml_fam; FST; SND; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                    o_THM];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[o_THM]] THEN
  MP_TAC(ISPECL [`cml_fam (f:A->real^K) (U,phi) (v:real^3->A) (eta:real^3->real^3)`;
                 `s:real`; `y:real^3`; `i:num`] CMT_PD_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                          ~(sndcart x = vec 0)}` THEN
    ASM_REWRITE_TAC[CMT_TIME_OPEN; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                    LIFT_DROP; IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  SUBGOAL_THEN
   `partial_derivative i (\z. cml_fam (f:A->real^K) (U,phi) (v:real^3->A)
                                      (eta:real^3->real^3) (pastecart (lift s) z)) y =
    partial_derivative i ((f o chart_inv (U:A->bool,phi:A->real^3)) o
                          (\z. (phi:A->real^3)(v(inv(norm z) % z)) + s % eta z)) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `C:real^3->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (phi:A->real^3)((v:real^3->A)(inv(norm z) % z)) +
                     s % (eta:real^3->real^3) z) differentiable at y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[partial_derivative] THEN
  MP_TAC(ISPECL [`\z. (phi:A->real^3)((v:real^3->A)(inv(norm z) % z)) +
                      s % (eta:real^3->real^3) z`;
                 `(f:A->real^K) o chart_inv (U:A->bool,phi:A->real^3)`; `y:real^3`] BEL_FRECHET_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM partial_derivative] THEN
  MP_TAC(ISPECL [`i:num`; `\z. (phi:A->real^3)((v:real^3->A)(inv(norm z) % z))`;
                 `\z. s % (eta:real^3->real^3) z`; `y:real^3`] PARTIAL_DERIVATIVE_ADD) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFFERENTIABLE_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_CMUL THEN ASM_REWRITE_TAC[]);;

(* The energy density of the family in the chart (Claim A).                 *)

let CML_FAM_PSI = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) U phi
    (eta:real^3->real^3) E y s.
     cml_famhyp (top,atlas) g f G d v (U,phi) eta E /\
     ~(y = vec 0) /\ v(inv(norm y) % y) IN U /\ abs s < &1
     ==> cmt_psi G (cmt_jet (cml_fam f (U,phi) v eta) (pastecart (lift s) y)) =
         sum(1..3)
          (\i. (partial_derivative i (\z. phi(v(inv(norm z) % z))) y +
                s % partial_derivative i eta y) dot
               (metric_local atlas (U,phi) g (phi(v(inv(norm y) % y)) + s % eta y) **
                (partial_derivative i (\z. phi(v(inv(norm z) % z))) y +
                 s % partial_derivative i eta y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `U:A->bool`;
                 `phi:A->real^3`; `eta:real^3->real^3`; `E:real^3->bool`; `y:real^3`;
                 `s:real`] CML_FAM_PD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `1`) THEN FIRST_ASSUM(MP_TAC o SPEC `2`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `3`) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[ARITH] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[cmt_psi; cmt_jet; FSTCART_PASTECART; SNDCART_PASTECART; SUM_3] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FST; SND] o GEN_REWRITE_RULE I [cml_famhyp]) THEN
  SUBGOAL_THEN `(phi:A->real^3)((v:real^3->A)(inv(norm(y:real^3)) % y)) + s % (eta:real^3->real^3) y
                IN IMAGE phi U` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `U:A->bool`; `phi:A->real^3`;
                 `(phi:A->real^3)((v:real^3->A)(inv(norm(y:real^3)) % y)) +
                  s % (eta:real^3->real^3) y`] CML_EMB_QUAD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* The first variation of the density at s = 0 (Claim B).                   *)

let CML_LINE_VD = prove
 (`!(c:real^N) d x. ((\s. c + drop s % d) has_vector_derivative d) (at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN `(\x:real^1. drop x % (d:real^N)) = (\x. vec 0 + drop x % d)` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
  VECTOR_ARITH_TAC);;

let CML_QUAD_LINE_DERIV = prove
 (`!V (G:real^3->real^3^3) c d a b.
     metric_field V G /\ c IN V
     ==> ((\s. (a + s % b) dot (G(c + s % d) ** (a + s % b))) has_real_derivative
          &2 * ((b + christoffel G c d a) dot (G c ** a))) (atreal (&0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_NUM] THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `\t. (c:real^3) + t % d`; `d:real^3`;
                 `\t. (a:real^3) + t % b`; `b:real^3`; `\t. (a:real^3) + t % b`; `b:real^3`;
                 `&0`] GEOC_DOT_DERIV) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; LIFT_NUM] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[CML_LINE_VD]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `c:real^3`; `a:real^3`;
                 `b + christoffel (G:real^3->real^3^3) c d a`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CML_FAM_Q = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) U phi
    (eta:real^3->real^3) E y.
     cml_famhyp (top,atlas) g f G d v (U,phi) eta E /\
     ~(y = vec 0) /\ v(inv(norm y) % y) IN U
     ==> drop(partial_derivative 1
                (\x. lift(cmt_psi G (cmt_jet (cml_fam f (U,phi) v eta) x)))
                (pastecart (lift(&0)) y)) =
         sum(1..3)
          (\i. &2 * ((partial_derivative i eta y +
                      christoffel (metric_local atlas (U,phi) g) (phi(v(inv(norm y) % y)))
                                  (eta y) (partial_derivative i (\z. phi(v(inv(norm z) % z))) y))
                     dot
                     (metric_local atlas (U,phi) g (phi(v(inv(norm y) % y))) **
                      partial_derivative i (\z. phi(v(inv(norm z) % z))) y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CML_FAMHYP_SMOOTH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FST; SND] o GEN_REWRITE_RULE I [cml_famhyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target] o
    check (fun th -> is_comb(concl th) && is_comb(rator(concl th)) &&
                     is_comb(rator(rator(concl th))) &&
                     is_const(rator(rator(rator(concl th)))) &&
                     fst(dest_const(rator(rator(rator(concl th))))) = "cm_target")) THEN
  ABBREV_TAC `D = {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                            ~(sndcart x = vec 0)}` THEN
  SUBGOAL_THEN `open(D:real^(1,3)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[CMT_TIME_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on D (\x. lift(cmt_psi (G:real^K->real^K^K)
                               (cmt_jet (cml_fam (f:A->real^K) (U,phi) (v:real^3->A)
                                                 (eta:real^3->real^3)) x)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\x. lift(cmt_psi (G:real^K->real^K^K)
                 (cmt_jet (cml_fam (f:A->real^K) (U,phi) (v:real^3->A) (eta:real^3->real^3)) x))) =
      (\y. lift(cmt_psi G y)) o cmt_jet (cml_fam f (U,phi) v eta)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; CMT_PSI_SMOOTH; CMT_JET_SMOOTH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(cmt_psi (G:real^K->real^K^K)
                            (cmt_jet (cml_fam (f:A->real^K) (U,phi) (v:real^3->A)
                                              (eta:real^3->real^3)) x))`;
                 `&0`; `y:real^3`] CMT_TIME_DERIV) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^(1,3)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN
    REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                IN_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[] THEN DISCH_TAC] THEN
  MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  EXISTS_TAC `\s. drop(lift(cmt_psi (G:real^K->real^K^K)
                       (cmt_jet (cml_fam (f:A->real^K) (U,phi) (v:real^3->A)
                                         (eta:real^3->real^3)) (pastecart (lift s) y))))` THEN
  EXISTS_TAC `&0` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s. sum(1..3)
                   (\i. (partial_derivative i (\z. (phi:A->real^3)((v:real^3->A)(inv(norm z) % z))) y +
                         s % partial_derivative i (eta:real^3->real^3) y) dot
                        (metric_local atlas (U,phi) (g:A->real^3^3)
                           (phi(v(inv(norm(y:real^3)) % y)) + s % eta y) **
                         (partial_derivative i (\z. phi(v(inv(norm z) % z))) y +
                          s % partial_derivative i eta y)))` THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
    REWRITE_TAC[LIFT_DROP] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CML_FAM_PSI THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `d:real`; `E:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CML_QUAD_LINE_DERIV THEN
  EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `metric_field (IMAGE (SND(U:A->bool,phi:A->real^3)) (FST(U:A->bool,phi)))
                               (metric_local atlas (U,phi) (g:A->real^3^3))` MP_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; REWRITE_TAC[FST; SND]];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* Away from the chart the family is constant in s.                         *)

let CML_RADIAL_KILL = prove
 (`!(u:real^3->real^N) y.
     (!t x. &0 < t /\ ~(x = vec 0) ==> u(t % x) = u x) /\ ~(y = vec 0) /\
     u differentiable at y
     ==> frechet_derivative u (at y) y = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((u:real^3->real^N) o (\s:real^1. drop s % y) has_derivative
                 frechet_derivative u (at y) o (\s. drop s % y)) (at (lift(&1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
      VECTOR_ARITH_TAC;
      REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((u:real^3->real^N) o (\s:real^1. drop s % y) has_derivative (\h. vec 0))
                (at (lift(&1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\s:real^1. (u:real^3->real^N) y` THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01; HAS_DERIVATIVE_CONST; o_THM] THEN
    X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(u:real^3->real^N) o (\s:real^1. drop s % y)`;
                 `frechet_derivative (u:real^3->real^N) (at y) o (\s:real^1. drop s % y)`;
                 `\h:real^1. vec 0:real^N`; `lift(&1)`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN
  REWRITE_TAC[o_THM; LIFT_DROP; VECTOR_MUL_LID]);;

let CML_FAM_OFF = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) U phi
    (eta:real^3->real^3) E y s i.
     cml_famhyp (top,atlas) g f G d v (U,phi) eta E /\
     ~(y = vec 0) /\ y IN E /\ abs s < &1 /\ 1 <= i /\ i <= 3
     ==> cml_fam f (U,phi) v eta (pastecart (lift s) y) = wan_rext (f o v) y /\
         partial_derivative (i + 1) (cml_fam f (U,phi) v eta) (pastecart (lift s) y) =
         partial_derivative i (wan_rext (f o v)) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CML_FAMHYP_SMOOTH) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FST; SND] o GEN_REWRITE_RULE I [cml_famhyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN E /\ ~(z = vec 0)
        ==> cml_fam (f:A->real^K) (U,phi) (v:real^3->A) (eta:real^3->real^3)
                    (pastecart (lift s) z) = wan_rext (f o v) z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[cml_fam; FST; SND; FSTCART_PASTECART; SNDCART_PASTECART; wan_rext; o_THM;
                 VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cml_fam (f:A->real^K) (U,phi) (v:real^3->A) (eta:real^3->real^3)`;
                 `s:real`; `y:real^3`; `i:num`] CMT_PD_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                          ~(sndcart x = vec 0)}` THEN
    ASM_REWRITE_TAC[CMT_TIME_OPEN; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                    LIFT_DROP; IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
  EXISTS_TAC `E INTER {z:real^3 | ~(z = vec 0)}` THEN
  ASM_SIMP_TAC[IN_INTER; IN_ELIM_THM] THEN MATCH_MP_TAC OPEN_INTER THEN
  ASM_REWRITE_TAC[SET_RULE `{x | ~(x = a)} = (:real^3) DELETE a`] THEN
  SIMP_TAC[OPEN_DELETE; OPEN_UNIV]);;

let CML_FAM_Q_OFF = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) U phi
    (eta:real^3->real^3) E y.
     cml_famhyp (top,atlas) g f G d v (U,phi) eta E /\ ~(y = vec 0) /\ y IN E
     ==> drop(partial_derivative 1
                (\x. lift(cmt_psi G (cmt_jet (cml_fam f (U,phi) v eta) x)))
                (pastecart (lift(&0)) y)) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CML_FAMHYP_SMOOTH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FST; SND] o GEN_REWRITE_RULE I [cml_famhyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target] o
    check (fun th -> is_comb(concl th) && is_comb(rator(concl th)) &&
                     is_comb(rator(rator(concl th))) &&
                     is_const(rator(rator(rator(concl th)))) &&
                     fst(dest_const(rator(rator(rator(concl th))))) = "cm_target")) THEN
  ABBREV_TAC `D = {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                            ~(sndcart x = vec 0)}` THEN
  SUBGOAL_THEN `open(D:real^(1,3)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[CMT_TIME_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on D (\x. lift(cmt_psi (G:real^K->real^K^K)
                               (cmt_jet (cml_fam (f:A->real^K) (U,phi) (v:real^3->A)
                                                 (eta:real^3->real^3)) x)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\x. lift(cmt_psi (G:real^K->real^K^K)
                 (cmt_jet (cml_fam (f:A->real^K) (U,phi) (v:real^3->A) (eta:real^3->real^3)) x))) =
      (\y. lift(cmt_psi G y)) o cmt_jet (cml_fam f (U,phi) v eta)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; CMT_PSI_SMOOTH; CMT_JET_SMOOTH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(cmt_psi (G:real^K->real^K^K)
                            (cmt_jet (cml_fam (f:A->real^K) (U,phi) (v:real^3->A)
                                              (eta:real^3->real^3)) x))`;
                 `&0`; `y:real^3`] CMT_TIME_DERIV) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^(1,3)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN
    REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                IN_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[] THEN DISCH_TAC] THEN
  MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  EXISTS_TAC `\s. drop(lift(cmt_psi (G:real^K->real^K^K)
                       (cmt_jet (cml_fam (f:A->real^K) (U,phi) (v:real^3->A)
                                         (eta:real^3->real^3)) (pastecart (lift s) y))))` THEN
  EXISTS_TAC `&0` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s:real. cmt_psi (G:real^K->real^K^K)
                         (cmt_jet (cml_fam (f:A->real^K) (U,phi) (v:real^3->A)
                                           (eta:real^3->real^3)) (pastecart (lift(&0)) y))` THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; HAS_REAL_DERIVATIVE_CONST] THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[REAL_SUB_RZERO; LIFT_DROP] THEN DISCH_TAC THEN
  REWRITE_TAC[cmt_psi; cmt_jet; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `U:A->bool`;
                 `phi:A->real^3`; `eta:real^3->real^3`; `E:real^3->bool`; `y:real^3`]
                CML_FAM_OFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:real`; `1`]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:real`; `2`]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s:real`; `3`]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`&0`; `1`]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`&0`; `2`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `3`]) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[ARITH; REAL_ABS_NUM; REAL_LT_01] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)) THEN REFL_TAC);;

(* The first variation density at P(z), in the plane (Claim C).             *)

let CML_FAM_PLANE = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) U phi
    (eta:real^3->real^3) E z.
     cml_famhyp (top,atlas) g f G d v (U,phi) eta E /\ v(stereo2_n_inv z) IN U
     ==> cml_rho z *
         drop(partial_derivative 1
                (\x. lift(cmt_psi G (cmt_jet (cml_fam f (U,phi) v eta) x)))
                (pastecart (lift(&0)) (stereo2_n_inv z))) =
         &2 * (cml_cov (metric_local atlas (U,phi) g) (cml_wc (U,phi) v stereo2_n_inv)
                       (\z. eta(stereo2_n_inv z)) 1 z dot
               (metric_local atlas (U,phi) g (cml_wc (U,phi) v stereo2_n_inv z) **
                partial_derivative 1 (cml_wc (U,phi) v stereo2_n_inv) z) +
               cml_cov (metric_local atlas (U,phi) g) (cml_wc (U,phi) v stereo2_n_inv)
                       (\z. eta(stereo2_n_inv z)) 2 z dot
               (metric_local atlas (U,phi) g (cml_wc (U,phi) v stereo2_n_inv z) **
                partial_derivative 2 (cml_wc (U,phi) v stereo2_n_inv) z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FST; SND] o GEN_REWRITE_RULE I [cml_famhyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p4_s2_smooth]) THEN
  SUBGOAL_THEN `~(stereo2_n_inv z = vec 0) /\
                inv(norm(stereo2_n_inv z)) % stereo2_n_inv z = stereo2_n_inv z`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0; CML_P_NORM; REAL_INV_1; VECTOR_MUL_LID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^3) U) (metric_local atlas (U,phi) (g:A->real^3^3))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `metric_field (IMAGE (SND(U:A->bool,phi:A->real^3)) (FST(U:A->bool,phi)))
                               (metric_local atlas (U,phi) (g:A->real^3^3))` MP_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; REWRITE_TAC[FST; SND]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^3)((v:real^3->A)(stereo2_n_inv z)) IN IMAGE phi U` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `C = {x:real^3 | ~(x = vec 0) /\ (v:real^3->A)(inv(norm x) % x) IN U}` THEN
  SUBGOAL_THEN `open(C:real^3->bool) /\ stereo2_n_inv z IN C` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `v:real^3->A`;
                   `(U:A->bool,phi:A->real^3)`] P4_RADIAL_CHART_OPEN) THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^3. (phi:A->real^3)((v:real^3->A)(inv(norm z) % z))) differentiable
                at (stereo2_n_inv z) /\
                (eta:real^3->real^3) differentiable at (stereo2_n_inv z)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `C:real^3->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN ASM_REWRITE_TAC[FST; SND];
      EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[SET_RULE `{x | ~(x = a)} = (:real^3) DELETE a`] THEN
      SIMP_TAC[OPEN_DELETE; OPEN_UNIV]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `U:A->bool`;
                 `phi:A->real^3`; `eta:real^3->real^3`; `E:real^3->bool`;
                 `stereo2_n_inv z`] CML_FAM_Q) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`\h. frechet_derivative (eta:real^3->real^3) (at (stereo2_n_inv z)) h +
         christoffel (metric_local atlas (U,phi) (g:A->real^3^3))
                     ((phi:A->real^3)((v:real^3->A)(stereo2_n_inv z)))
                     (eta(stereo2_n_inv z))
                     (frechet_derivative (\z:real^3. phi(v(inv(norm z) % z)))
                                         (at (stereo2_n_inv z)) h)`;
    `frechet_derivative (\z:real^3. (phi:A->real^3)((v:real^3->A)(inv(norm z) % z)))
                        (at (stereo2_n_inv z))`;
    `metric_local atlas (U,phi) (g:A->real^3^3) ((phi:A->real^3)((v:real^3->A)(stereo2_n_inv z)))`;
    `z:real^2`] CML_FRAME_SUM) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `linear(christoffel (metric_local atlas (U,phi) (g:A->real^3^3))
                                   ((phi:A->real^3)((v:real^3->A)(stereo2_n_inv z)))
                                   ((eta:real^3->real^3)(stereo2_n_inv z)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `metric_local atlas (U,phi) (g:A->real^3^3)`;
                   `(phi:A->real^3)((v:real^3->A)(stereo2_n_inv z))`] LRG_CHRISTOFFEL_LINEAR) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE; ETA_AX] THEN
      SUBGOAL_THEN
       `(\h. christoffel (metric_local atlas (U,phi) (g:A->real^3^3))
                         ((phi:A->real^3)((v:real^3->A)(stereo2_n_inv z)))
                         ((eta:real^3->real^3)(stereo2_n_inv z))
                         (frechet_derivative (\z:real^3. phi(v(inv(norm z) % z)))
                                             (at (stereo2_n_inv z)) h)) =
        christoffel (metric_local atlas (U,phi) g) (phi(v(stereo2_n_inv z)))
                    (eta(stereo2_n_inv z)) o
        frechet_derivative (\z:real^3. phi(v(inv(norm z) % z))) (at (stereo2_n_inv z))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE];
      ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE];
      SUBGOAL_THEN
       `frechet_derivative (eta:real^3->real^3) (at (stereo2_n_inv z)) (stereo2_n_inv z) = vec 0 /\
        frechet_derivative (\z:real^3. (phi:A->real^3)((v:real^3->A)(inv(norm z) % z)))
                           (at (stereo2_n_inv z)) (stereo2_n_inv z) = vec 0`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN MATCH_MP_TAC CML_RADIAL_KILL THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[CML_NRM_SCALE];
        REWRITE_TAC[VECTOR_ADD_LID] THEN
        MP_TAC(ISPEC `christoffel (metric_local atlas (U,phi) (g:A->real^3^3))
                                  ((phi:A->real^3)((v:real^3->A)(stereo2_n_inv z)))
                                  ((eta:real^3->real^3)(stereo2_n_inv z))` LINEAR_0) THEN
        ASM_REWRITE_TAC[]]];
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[GSYM partial_derivative])] THEN
  ASM_REWRITE_TAC[SUM_LMUL] THEN
  SUBGOAL_THEN
   `!a. partial_derivative a (cml_wc (U,phi) (v:real^3->A) stereo2_n_inv) z =
        frechet_derivative (\z:real^3. (phi:A->real^3)(v(inv(norm z) % z)))
                           (at (stereo2_n_inv z)) (bel_dP z (basis a)) /\
        partial_derivative a (\z. (eta:real^3->real^3)(stereo2_n_inv z)) z =
        frechet_derivative eta (at (stereo2_n_inv z)) (bel_dP z (basis a))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[partial_derivative] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(U:A->bool,phi:A->real^3)`; `v:real^3->A`; `stereo2_n_inv`]
                    CML_WC_COMPOSE) THEN
      REWRITE_TAC[CML_P_NORM; SND] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`stereo2_n_inv`;
                     `\z:real^3. (phi:A->real^3)((v:real^3->A)(inv(norm z) % z))`;
                     `z:real^2`] BEL_FRECHET_CHAIN);
      SUBGOAL_THEN `(\z. (eta:real^3->real^3)(stereo2_n_inv z)) = eta o stereo2_n_inv`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MP_TAC(ISPECL [`stereo2_n_inv`; `eta:real^3->real^3`; `z:real^2`] BEL_FRECHET_CHAIN)] THEN
    ASM_REWRITE_TAC[BEL_P_FRECHET] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    REWRITE_TAC[o_THM; BEL_P_FRECHET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cml_cov; cml_wc; SND] THEN
  SUBGOAL_THEN
   `!u. christoffel (metric_local atlas (U,phi) (g:A->real^3^3))
                    ((phi:A->real^3)((v:real^3->A)(stereo2_n_inv z))) u
                    ((eta:real^3->real^3)(stereo2_n_inv z)) =
        christoffel (metric_local atlas (U,phi) g) (phi(v(stereo2_n_inv z)))
                    (eta(stereo2_n_inv z)) u`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC CHRISTOFFEL_SYM THEN EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cml_rho z` MP_TAC THENL
   [REWRITE_TAC[cml_rho] THEN MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_POW_LT THEN
    MP_TAC(SPEC `norm(z:real^2)` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The first variation in the plane. The shell integral of the first        *)
(* variation density (zero for a critical map, CMT_FV_ZERO) is 3/2 times    *)
(* the sphere integral (homogeneity), which is the plane integral of rho    *)
(* times the density at P(z) (CML_S2_TRANSFER) = 2 int <D_a eta, d_a w>     *)
(* over the chart region.                                                   *)
(* ========================================================================= *)

let CML_FAM_HOMOG = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) U phi
    (eta:real^3->real^3) E y t.
     cml_famhyp (top,atlas) g f G d v (U,phi) eta E /\ ~(y = vec 0) /\ &0 < t
     ==> drop(partial_derivative 1
                (\x. lift(cmt_psi G (cmt_jet (cml_fam f (U,phi) v eta) x)))
                (pastecart (lift(&0)) (t % y))) =
         inv(t pow 2) *
         drop(partial_derivative 1
                (\x. lift(cmt_psi G (cmt_jet (cml_fam f (U,phi) v eta) x)))
                (pastecart (lift(&0)) y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FST; SND] o GEN_REWRITE_RULE I [cml_famhyp]) THEN
  SUBGOAL_THEN `~(t % y:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  ASM_CASES_TAC `(v:real^3->A)(inv(norm(y:real^3)) % y) IN U` THENL
   [ALL_TAC;
    SUBGOAL_THEN `(y:real^3) IN E /\ t % y IN E` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(v:real^3->A)(inv(norm(t % y:real^3)) % (t % y)) = v(inv(norm y) % y)`
      ASSUME_TAC THENL [ASM_SIMP_TAC[CML_NRM_SCALE]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `U:A->bool`;
                   `phi:A->real^3`; `eta:real^3->real^3`; `E:real^3->bool`] CML_FAM_Q_OFF) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `y:real^3` th) THEN MP_TAC(SPEC `t % y:real^3` th)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO]] THEN
  SUBGOAL_THEN `(v:real^3->A)(inv(norm(t % y:real^3)) % (t % y)) IN U` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CML_NRM_SCALE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `U:A->bool`;
                 `phi:A->real^3`; `eta:real^3->real^3`; `E:real^3->bool`] CML_FAM_Q) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `y:real^3` th) THEN MP_TAC(SPEC `t % y:real^3` th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[CML_NRM_SCALE] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p4_s2_smooth]) THEN
  ABBREV_TAC `C = {x:real^3 | ~(x = vec 0) /\ (v:real^3->A)(inv(norm x) % x) IN U}` THEN
  SUBGOAL_THEN `open(C:real^3->bool) /\ (y:real^3) IN C` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `v:real^3->A`;
                   `(U:A->bool,phi:A->real^3)`] P4_RADIAL_CHART_OPEN) THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. partial_derivative i (\z:real^3. (phi:A->real^3)((v:real^3->A)(inv(norm z) % z)))
                                       (t % y) =
                    inv t % partial_derivative i (\z. phi(v(inv(norm z) % z))) y /\
                    partial_derivative i (eta:real^3->real^3) (t % y) =
                    inv t % partial_derivative i eta y`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC CML_HOMOG_PD THEN ASM_SIMP_TAC[CML_NRM_SCALE] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `C:real^3->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN ASM_REWRITE_TAC[FST; SND];
      EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[SET_RULE `{x | ~(x = a)} = (:real^3) DELETE a`] THEN
      SIMP_TAC[OPEN_DELETE; OPEN_UNIV]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `linear(christoffel (metric_local atlas (U,phi) (g:A->real^3^3))
                                   ((phi:A->real^3)((v:real^3->A)(inv(norm(y:real^3)) % y)))
                                   ((eta:real^3->real^3) y))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
    SUBGOAL_THEN `metric_field (IMAGE (SND(U:A->bool,phi:A->real^3)) (FST(U:A->bool,phi)))
                               (metric_local atlas (U,phi) (g:A->real^3^3))` MP_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; REWRITE_TAC[FST; SND] THEN DISCH_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `metric_local atlas (U,phi) (g:A->real^3^3)`;
                   `(phi:A->real^3)((v:real^3->A)(inv(norm(y:real^3)) % y))`]
                  LRG_CHRISTOFFEL_LINEAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
                    SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_CMUL] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM VECTOR_ADD_LDISTRIB; DOT_LMUL; DOT_RMUL; MATRIX_VECTOR_MUL_RMUL] THEN
  REWRITE_TAC[REAL_POW_2; REAL_INV_MUL] THEN REAL_ARITH_TAC);;

let CML_FAM_CONT = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) U phi
    (eta:real^3->real^3) E.
     cml_famhyp (top,atlas) g f G d v (U,phi) eta E
     ==> (\y. lift(drop(partial_derivative 1
                          (\x. lift(cmt_psi G (cmt_jet (cml_fam f (U,phi) v eta) x)))
                          (pastecart (lift(&0)) y))))
         continuous_on {y:real^3 | ~(y = vec 0)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CML_FAMHYP_SMOOTH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FST; SND] o GEN_REWRITE_RULE I [cml_famhyp]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target] o
    check (fun th -> is_comb(concl th) && is_comb(rator(concl th)) &&
                     is_comb(rator(rator(concl th))) &&
                     is_const(rator(rator(rator(concl th)))) &&
                     fst(dest_const(rator(rator(rator(concl th))))) = "cm_target")) THEN
  ABBREV_TAC `D = {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                            ~(sndcart x = vec 0)}` THEN
  SUBGOAL_THEN `open(D:real^(1,3)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[CMT_TIME_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on D (\x. lift(cmt_psi (G:real^K->real^K^K)
                               (cmt_jet (cml_fam (f:A->real^K) (U,phi) (v:real^3->A)
                                                 (eta:real^3->real^3)) x)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\x. lift(cmt_psi (G:real^K->real^K^K)
                 (cmt_jet (cml_fam (f:A->real^K) (U,phi) (v:real^3->A) (eta:real^3->real^3)) x))) =
      (\y. lift(cmt_psi G y)) o cmt_jet (cml_fam f (U,phi) v eta)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; CMT_PSI_SMOOTH; CMT_JET_SMOOTH];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN
   `(\y:real^3. partial_derivative 1
                  (\x. lift(cmt_psi (G:real^K->real^K^K)
                              (cmt_jet (cml_fam (f:A->real^K) (U,phi) (v:real^3->A)
                                                (eta:real^3->real^3)) x)))
                  (pastecart (lift(&0)) y)) =
    partial_derivative 1
      (\x. lift(cmt_psi G (cmt_jet (cml_fam f (U,phi) v eta) x))) o
    (\y. pastecart (lift(&0)) y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `D:real^(1,3)finite_sum->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN
    EXPAND_TAC "D" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP; IN_REAL_INTERVAL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC[]]);;

(* The planar first variation density.                                       *)

let cml_fvd = new_definition
 `cml_fvd (G:real^3->real^3^3) (w:real^2->real^3) (X:real^2->real^3) (z:real^2) =
    cml_cov G w X 1 z dot (G(w z) ** partial_derivative 1 w z) +
    cml_cov G w X 2 z dot (G(w z) ** partial_derivative 2 w z)`;;

let CML_FV_PLANE = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) U phi
    (eta:real^3->real^3) E.
     cml_famhyp (top,atlas) g f G d v (U,phi) eta E /\
     (!psi:real^3->real^K.
         smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext psi)
         ==> ((\e. cm_sen G (\y. closest_point (IMAGE f (topspace top))
                                                ((f o v) y + e % psi y)))
              has_real_derivative &0) (atreal (&0)))
     ==> (\z. lift(if v(stereo2_n_inv z) IN U
                   then cml_fvd (metric_local atlas (U,phi) g) (cml_wc (U,phi) v stereo2_n_inv)
                                (\z. eta(stereo2_n_inv z)) z
                   else &0)) absolutely_integrable_on (:real^2) /\
         drop(integral (:real^2)
                (\z. lift(if v(stereo2_n_inv z) IN U
                          then cml_fvd (metric_local atlas (U,phi) g)
                                       (cml_wc (U,phi) v stereo2_n_inv)
                                       (\z. eta(stereo2_n_inv z)) z
                          else &0))) = &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CRIT")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[FST; SND] o GEN_REWRITE_RULE I [cml_famhyp]) THEN
  ABBREV_TAC `q = \y:real^3. drop(partial_derivative 1
                    (\x. lift(cmt_psi (G:real^K->real^K^K)
                                (cmt_jet (cml_fam (f:A->real^K) (U,phi) (v:real^3->A)
                                                  (eta:real^3->real^3)) x)))
                    (pastecart (lift(&0)) y))` THEN
  SUBGOAL_THEN `(\y. lift((q:real^3->real) y)) continuous_on {y:real^3 | ~(y = vec 0)}`
  ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `U:A->bool`;
                   `phi:A->real^3`; `eta:real^3->real^3`; `E:real^3->bool`] CML_FAM_CONT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t y. &0 < t /\ ~(y = vec 0) ==> (q:real^3->real)(t % y) = inv(t pow 2) * q y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "q" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CML_FAM_HOMOG THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `d:real`; `E:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?B. !y. y IN sphere(vec 0:real^3,&1) ==> abs((q:real^3->real) y) <= B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\y. lift((q:real^3->real) y)`; `sphere(vec 0:real^3,&1)`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_SPHERE] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SPHERE_0] THEN GEN_TAC THEN
      DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
      REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift((q:real^3->real) y)) measurable_on (:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMT_CONT_NONZERO_MEASURABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `q:real^3->real` CM_SHELL_INTEGRAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(\x. lift((q:real^3->real)(inv(norm x) % x))) absolutely_integrable_on
                ball(vec 0,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\x:real^3. lift(max B (abs((q:real^3->real)(vec 0))))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^3)` THEN REWRITE_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_BALL] THEN
      MATCH_MP_TAC CMT_CONT_NONZERO_MEASURABLE THEN
      SUBGOAL_THEN `(\z:real^3. lift((q:real^3->real)(inv(norm z) % z))) =
                    (\y. lift(q y)) o (\z. inv(norm z) % z)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3) DIFF {vec 0}` THEN
        REWRITE_TAC[P4_RADIAL_CONTINUOUS] THEN SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0] THEN MESON_TAC[]];
      REWRITE_TAC[INTEGRABLE_ON_CONST; MEASURABLE_BALL];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
      ASM_CASES_TAC `x:real^3 = vec 0` THENL
       [ASM_REWRITE_TAC[NORM_0; REAL_INV_0; VECTOR_MUL_LZERO] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= max b c`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE]]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `q:real^3->real` CML_S2_TRANSFER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. cml_rho z * (q:real^3->real)(stereo2_n_inv z) =
        &2 * (if (v:real^3->A)(stereo2_n_inv z) IN U
              then cml_fvd (metric_local atlas (U,phi) (g:A->real^3^3))
                           (cml_wc (U,phi) v stereo2_n_inv)
                           (\z. (eta:real^3->real^3)(stereo2_n_inv z)) z
              else &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN COND_CASES_TAC THENL
     [EXPAND_TAC "q" THEN REWRITE_TAC[cml_fvd] THEN MATCH_MP_TAC CML_FAM_PLANE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `d:real`; `E:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(stereo2_n_inv z = vec 0) /\
                    inv(norm(stereo2_n_inv z)) % stereo2_n_inv z = stereo2_n_inv z`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[GSYM NORM_EQ_0; CML_P_NORM; REAL_INV_1; VECTOR_MUL_LID] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `stereo2_n_inv z IN E` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "q" THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `U:A->bool`;
                     `phi:A->real^3`; `eta:real^3->real^3`; `E:real^3->bool`;
                     `stereo2_n_inv z`] CML_FAM_Q_OFF) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral wan_shell (\z. lift((q:real^3->real) z))) / &3 = &0`
  ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN `smooth_map_on {x | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                     ~(sndcart x = vec 0)}
                                (cml_fam (f:A->real^K) (U,phi) (v:real^3->A) (eta:real^3->real^3))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CML_FAMHYP_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `G:real^K->real^K^K`; `d:real`;
                            `E:real^3->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `f:A->real^K`;
                   `v:real^3->A`; `U:A->bool`; `phi:A->real^3`; `eta:real^3->real^3`]
                  CML_FAM_PROPS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                   `cml_fam (f:A->real^K) (U,phi) (v:real^3->A) (eta:real^3->real^3)`]
                  CMT_FV_ZERO) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(if (v:real^3->A)(stereo2_n_inv z) IN U
              then cml_fvd (metric_local atlas (U,phi) (g:A->real^3^3))
                           (cml_wc (U,phi) v stereo2_n_inv)
                           (\z. (eta:real^3->real^3)(stereo2_n_inv z)) z
              else &0)) =
    (\z. inv(&2) % lift(cml_rho z * (q:real^3->real)(stereo2_n_inv z)))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL] THEN GEN_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_CMUL; INTEGRAL_CMUL;
               ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; DROP_CMUL] THEN
  UNDISCH_TAC `drop(integral wan_shell (\z. lift((q:real^3->real) z))) / &3 = &0` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
     lhand(concl th) = `p4_s2_integral (q:real^3->real)`)) THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Integration by parts of the planar first variation for test fields with  *)
(* compact support in the chart region:  int <D_a X, d_a w> = - int <X,     *)
(* tau(w)>.                                                                 *)
(* ========================================================================= *)

let CML_GLUE_SMOOTH = prove
 (`!Wc K (h:real^2->real).
     open Wc /\ compact K /\ K SUBSET Wc /\ smooth_map_on Wc (\z. lift(h z)) /\
     (!z. z IN Wc /\ ~(z IN K) ==> h z = &0)
     ==> smooth_map_on (:real^2) (\z. lift(if z IN Wc then h z else &0)) /\
         (!z. ~(z IN K) ==> (if z IN Wc then h z else &0) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC; GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `z0:real^2` THEN ASM_CASES_TAC `(z0:real^2) IN Wc` THENL
   [EXISTS_TAC `Wc:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\z. lift((h:real^2->real) z)` THEN
    ASM_SIMP_TAC[];
    EXISTS_TAC `(:real^2) DIFF K` THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\z:real^2. lift(&0)` THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]]);;

let CML_IBP_SUPP = prove
 (`!V (G:real^3->real^3^3) Wc (w:real^2->real^3) (X:real^2->real^3) K.
     metric_field V G /\ open Wc /\ smooth_map_on Wc w /\ (!z. z IN Wc ==> w z IN V) /\
     smooth_map_on Wc X /\ compact K /\ K SUBSET Wc /\
     (!z. z IN Wc /\ ~(z IN K) ==> X z = vec 0) /\
     (\z. lift(if z IN Wc then cml_fvd G w X z else &0)) absolutely_integrable_on (:real^2) /\
     drop(integral (:real^2) (\z. lift(if z IN Wc then cml_fvd G w X z else &0))) = &0
     ==> (\z. lift(if z IN Wc
                   then X z dot (G(w z) ** (cml_cov G w (partial_derivative 1 w) 1 z +
                                            cml_cov G w (partial_derivative 2 w) 2 z))
                   else &0)) absolutely_integrable_on (:real^2) /\
         drop(integral (:real^2)
                (\z. lift(if z IN Wc
                          then X z dot (G(w z) ** (cml_cov G w (partial_derivative 1 w) 1 z +
                                                   cml_cov G w (partial_derivative 2 w) 2 z))
                          else &0))) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a. smooth_map_on Wc (partial_derivative a (w:real^2->real^3))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. smooth_map_on (:real^2)
          (\z. lift(if z IN Wc then (X:real^2->real^3) z dot
                                    ((G:real^3->real^3^3)((w:real^2->real^3) z) **
                                     partial_derivative a w z)
                    else &0)) /\
        (!z. ~(z IN K) ==> (if z IN Wc then X z dot (G(w z) ** partial_derivative a w z)
                            else &0) = &0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CML_GLUE_SMOOTH THEN ASM_SIMP_TAC[DOT_LZERO] THEN
    MATCH_MP_TAC CML_QUAD_SMOOTH THEN EXISTS_TAC `V:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. (\z. lift(cml_d a (\z. if z IN Wc then (X:real^2->real^3) z dot
                                         ((G:real^3->real^3^3)((w:real^2->real^3) z) **
                                          partial_derivative a w z)
                               else &0) z)) absolutely_integrable_on (:real^2) /\
        integral (:real^2)
          (\z. lift(cml_d a (\z. if z IN Wc then X z dot (G(w z) ** partial_derivative a w z)
                                 else &0) z)) = vec 0`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CML_DIV_ZERO THEN EXISTS_TAC `K:real^2->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. (if z IN Wc
         then (X:real^2->real^3) z dot ((G:real^3->real^3^3)((w:real^2->real^3) z) **
                (cml_cov G w (partial_derivative 1 w) 1 z +
                 cml_cov G w (partial_derivative 2 w) 2 z))
         else &0) =
        (cml_d 1 (\z. if z IN Wc then X z dot (G(w z) ** partial_derivative 1 w z) else &0) z +
         cml_d 2 (\z. if z IN Wc then X z dot (G(w z) ** partial_derivative 2 w z) else &0) z) -
        (if z IN Wc then cml_fvd G w X z else &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN
       `!a. cml_d a (\z. if z IN Wc then (X:real^2->real^3) z dot
                                         ((G:real^3->real^3^3)((w:real^2->real^3) z) **
                                          partial_derivative a w z)
                         else &0) z =
            cml_cov G w X a z dot (G(w z) ** partial_derivative a w z) +
            X z dot (G(w z) ** cml_cov G w (partial_derivative a w) a z)`
      (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN
        SUBGOAL_THEN
         `cml_d a (\z. if z IN Wc then (X:real^2->real^3) z dot
                                       ((G:real^3->real^3^3)((w:real^2->real^3) z) **
                                        partial_derivative a w z)
                       else &0) z =
          cml_d a (\z. X z dot (G(w z) ** partial_derivative a w z)) z`
        SUBST1_TAC THENL
         [MATCH_MP_TAC CML_D_LOCAL THEN EXISTS_TAC `Wc:real^2->bool` THEN ASM_SIMP_TAC[];
          MATCH_MP_TAC CML_D_QUAD THEN EXISTS_TAC `V:real^3->bool` THEN
          EXISTS_TAC `Wc:real^2->bool` THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[cml_fvd; MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_RADD] THEN REAL_ARITH_TAC];
      REWRITE_TAC[REAL_SUB_RZERO] THEN
      SUBGOAL_THEN `~((z:real^2) IN K)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `!a. cml_d a (\z. if z IN Wc then (X:real^2->real^3) z dot
                                         ((G:real^3->real^3^3)((w:real^2->real^3) z) **
                                          partial_derivative a w z)
                         else &0) z = &0`
      (fun th -> REWRITE_TAC[th; REAL_ADD_LID]) THEN
      GEN_TAC THEN MATCH_MP_TAC CML_D_ZERO THEN EXISTS_TAC `(:real^2) DIFF K` THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_SUB; LIFT_ADD] THEN
  SUBGOAL_THEN
   `!a. (\z. lift(cml_d a (\z. if z IN Wc then (X:real^2->real^3) z dot
                                         ((G:real^3->real^3^3)((w:real^2->real^3) z) **
                                          partial_derivative a w z)
                               else &0) z)) integrable_on (:real^2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(if z IN Wc then cml_fvd (G:real^3->real^3^3) (w:real^2->real^3)
                                                  (X:real^2->real^3) z else &0))
                integrable_on (:real^2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[INTEGRAL_SUB; INTEGRAL_ADD; INTEGRABLE_ADD] THEN
    ASM_REWRITE_TAC[DROP_SUB; DROP_ADD; DROP_VEC] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The Euler-Lagrange equation in charts.  A bump test field supported near *)
(* P(z0) gives an admissible variation (cml_famhyp); by CML_FV_PLANE and    *)
(* CML_IBP_SUPP the integral of <eta, tau(w)> vanishes, which forces        *)
(* tau(w)(z0) = 0 by positivity.                                            *)
(* ========================================================================= *)

let CML_XN_3 = prove
 (`!z. (stereo2_n_inv z)$3 < &1`,
  GEN_TAC THEN SIMP_TAC[stereo2_n_inv; LAMBDA_BETA; DIMINDEX_3; ARITH] THEN
  SUBGOAL_THEN `&0 < norm(z:real^2) pow 2 + &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `norm(z:real^2)` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC);;

let CML_FAMHYP_BUMP = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) U phi z0 r delta r2 eps
    (c3:real^3).
     cm_emb (top,atlas) g f G d /\ p4_s2_smooth (top,atlas) v /\
     (!y. y IN sphere(vec 0,&1) ==> v y IN topspace top) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (f o v)) /\
     (U,phi) IN atlas /\
     (!z. z IN ball(z0,r)
          ==> v(stereo2_n_inv z) IN U /\
              ball(phi(v(stereo2_n_inv z)),delta) SUBSET IMAGE phi U) /\
     &0 < r2 /\
     (!y. y IN sphere(vec 0,&1) /\ norm(y - stereo2_n_inv z0) <= r2
          ==> y$3 < &1 /\ stereo2_n y IN ball(z0,r)) /\
     &0 < eps /\ eps * norm c3 < delta
     ==> cml_famhyp (top,atlas) g f G d v (U,phi)
           (\y. (eps * smooth_bump (r2 / &2) r2 (inv(norm y) % y - stereo2_n_inv z0)) % c3)
           {y | ~(y = vec 0) /\ r2 < norm(inv(norm y) % y - stereo2_n_inv z0)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= r2 / &2 /\ r2 / &2 < r2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. ~(y = vec 0) /\ norm(inv(norm y) % y - stereo2_n_inv z0) <= r2
               ==> stereo2_n_inv(stereo2_n(inv(norm y) % y)) = inv(norm y) % y /\
                   stereo2_n(inv(norm y) % y) IN ball(z0,r)`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `inv(norm y) % y IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[P4_RADIAL_SPHERE]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv(norm y) % y:real^3` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> t = `stereo2_n`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC STEX_STEREO2_N_LEFT THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^3. x$3`) THEN REWRITE_TAC[] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[cml_famhyp; FST; SND] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* smoothness of eta *)
    MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`;
                   `\y:real^3. lift(eps * smooth_bump (r2 / &2) r2 (inv(norm y) % y - stereo2_n_inv z0))`;
                   `\y:real^3. (c3:real^3)`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_NONZERO; SMOOTH_MAP_ON_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `(\y:real^3. lift(eps * smooth_bump (r2 / &2) r2 (inv(norm y) % y - stereo2_n_inv z0))) =
      (\x. eps % lift(smooth_bump (r2 / &2) r2 x)) o (\y. inv(norm y) % y - stereo2_n_inv z0)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[OPEN_NONZERO; OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_NORMALIZE; SMOOTH_MAP_ON_CONST];
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
      MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN ASM_REWRITE_TAC[]];
    (* homogeneity *)
    SIMP_TAC[CML_NRM_SCALE];
    (* E open *)
    MP_TAC(ISPECL [`\y:real^3. inv(norm y) % y - stereo2_n_inv z0`; `{z:real^3 | ~(z = vec 0)}`;
                   `{x:real^3 | r2 < norm x}`] CONTINUOUS_OPEN_PREIMAGE) THEN
    REWRITE_TAC[IN_ELIM_THM; OPEN_NONZERO] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_NORMALIZE; SMOOTH_MAP_ON_CONST];
      SUBGOAL_THEN `{x:real^3 | r2 < norm x} = (:real^3) DIFF cball(vec 0,r2)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL_0] THEN REAL_ARITH_TAC;
        SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL]]];
    (* eta = 0 on E *)
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `smooth_bump (r2 / &2) r2 (inv(norm(y:real^3)) % y - stereo2_n_inv z0) = &0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_RZERO; VECTOR_MUL_LZERO]];
    (* cover *)
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `norm(inv(norm(y:real^3)) % y - stereo2_n_inv z0) <= r2` THENL
     [DISJ1_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `stereo2_n(inv(norm(y:real^3)) % y)` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> t = `ball:real^2#real->real^2->bool`)) (concl th))) THEN
      ASM_SIMP_TAC[];
      DISJ2_TAC THEN ASM_REAL_ARITH_TAC];
    (* staying in the chart *)
    MAP_EVERY X_GEN_TAC [`y:real^3`; `s:real`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `norm(inv(norm(y:real^3)) % y - stereo2_n_inv z0) <= r2` THENL
     [ALL_TAC;
      SUBGOAL_THEN `smooth_bump (r2 / &2) r2 (inv(norm(y:real^3)) % y - stereo2_n_inv z0) = &0`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `stereo2_n(inv(norm(y:real^3)) % y)` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> t = `ball:real^2#real->real^2->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `a - (a + b):real^N = --b`; NORM_NEG] THEN
    REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC] THEN
    MP_TAC(ISPECL [`r2 / &2`; `r2:real`; `inv(norm(y:real^3)) % y - stereo2_n_inv z0`]
                  SMOOTH_BUMP_BOUNDS) THEN
    ABBREV_TAC `b = smooth_bump (r2 / &2) r2 (inv(norm(y:real^3)) % y - stereo2_n_inv z0)` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `eps * norm(c3:real^3)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`; REAL_ARITH `&0 <= b ==> abs b = b`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE; REAL_LE_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* The chart region, the chart representation and its tension field.        *)

let CML_CHART_REGION = prove
 (`!top atlas (v:real^3->A) U phi.
     smooth_manifold_atlas top atlas /\ p4_s2_smooth (top,atlas) v /\ (U,phi) IN atlas
     ==> open {z:real^2 | v(stereo2_n_inv z) IN U} /\
         smooth_map_on {z:real^2 | v(stereo2_n_inv z) IN U} (cml_wc (U,phi) v stereo2_n_inv) /\
         (!z. z IN {z:real^2 | v(stereo2_n_inv z) IN U}
              ==> cml_wc (U,phi) v stereo2_n_inv z IN IMAGE phi U)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p4_s2_smooth]) THEN
  ABBREV_TAC `C = {x:real^3 | ~(x = vec 0) /\ (v:real^3->A)(inv(norm x) % x) IN U}` THEN
  SUBGOAL_THEN `open(C:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `v:real^3->A`;
                   `(U:A->bool,phi:A->real^3)`] P4_RADIAL_CHART_OPEN) THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. ~(stereo2_n_inv z = vec 0) /\
                    inv(norm(stereo2_n_inv z)) % stereo2_n_inv z = stereo2_n_inv z`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM NORM_EQ_0; CML_P_NORM; REAL_INV_1; VECTOR_MUL_LID] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{z:real^2 | (v:real^3->A)(stereo2_n_inv z) IN U} =
                {z | stereo2_n_inv z IN C}` SUBST1_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT; BEL_P_FRECHET];
    MP_TAC(ISPECL [`(U:A->bool,phi:A->real^3)`; `v:real^3->A`; `stereo2_n_inv`]
                  CML_WC_COMPOSE) THEN
    REWRITE_TAC[CML_P_NORM; SND] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `C:real^3->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT; BEL_P_FRECHET];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV; STEX_STEREO2_N_INV_SMOOTH];
      EXPAND_TAC "C" THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN ASM_REWRITE_TAC[FST; SND]];
    REWRITE_TAC[IN_ELIM_THM; cml_wc; SND] THEN X_GEN_TAC `z:real^2` THEN
    EXPAND_TAC "C" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let CML_EPS_ARITH = prove
 (`!e n. &0 < e /\ &0 <= n ==> &0 < e / (n + &1) /\ e / (n + &1) * n < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < n + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  REWRITE_TAC[REAL_ARITH `x / y * n = (x * n) / y`] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC);;

(* The Euler-Lagrange equation in a chart.                                    *)

let CML_EL_CHART = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) (G:real^K->real^K^K) d (v:real^3->A) U phi z0.
     cm_emb (top,atlas) g f G d /\ p4_s2_smooth (top,atlas) v /\
     (!y. y IN sphere(vec 0,&1) ==> v y IN topspace top) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (f o v)) /\
     (!psi:real^3->real^K.
         smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext psi)
         ==> ((\e. cm_sen G (\y. closest_point (IMAGE f (topspace top))
                                                ((f o v) y + e % psi y)))
              has_real_derivative &0) (atreal (&0))) /\
     (U,phi) IN atlas /\ v(stereo2_n_inv z0) IN U
     ==> cml_cov (metric_local atlas (U,phi) g) (cml_wc (U,phi) v stereo2_n_inv)
                 (partial_derivative 1 (cml_wc (U,phi) v stereo2_n_inv)) 1 z0 +
         cml_cov (metric_local atlas (U,phi) g) (cml_wc (U,phi) v stereo2_n_inv)
                 (partial_derivative 2 (cml_wc (U,phi) v stereo2_n_inv)) 2 z0 = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `v:real^3->A`;
                 `U:A->bool`; `phi:A->real^3`] CML_CHART_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^3) U) (metric_local atlas (U,phi) (g:A->real^3^3))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `metric_field (IMAGE (SND(U:A->bool,phi:A->real^3)) (FST(U:A->bool,phi)))
                               (metric_local atlas (U,phi) (g:A->real^3^3))` MP_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; REWRITE_TAC[FST; SND]];
    ALL_TAC] THEN
  ABBREV_TAC `Gl = metric_local atlas (U:A->bool,phi:A->real^3) (g:A->real^3^3)` THEN
  ABBREV_TAC `w = cml_wc (U:A->bool,phi:A->real^3) (v:real^3->A) stereo2_n_inv` THEN
  ABBREV_TAC `Wc = {z:real^2 | (v:real^3->A)(stereo2_n_inv z) IN U}` THEN
  SUBGOAL_THEN `(z0:real^2) IN Wc` ASSUME_TAC THENL
   [EXPAND_TAC "Wc" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!a. smooth_map_on Wc (partial_derivative a (w:real^2->real^3))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on Wc (\z. cml_cov Gl (w:real^2->real^3) (partial_derivative 1 w) 1 z +
                          cml_cov Gl w (partial_derivative 2 w) 2 z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CML_COV_SMOOTH THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  ABBREV_TAC `c3 = cml_cov Gl (w:real^2->real^3) (partial_derivative 1 w) 1 z0 +
                   cml_cov Gl w (partial_derivative 2 w) 2 z0` THEN
  (* positivity of <c3, tau> near z0 and a chart margin *)
  SUBGOAL_THEN
   `smooth_map_on Wc (\z. lift((\z:real^2. c3:real^3) z dot
                              ((Gl:real^3->real^3^3)((w:real^2->real^3) z) **
                               (\z. cml_cov Gl w (partial_derivative 1 w) 1 z +
                                    cml_cov Gl w (partial_derivative 2 w) 2 z) z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CML_QUAD_SMOOTH THEN EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  SUBGOAL_THEN `&0 < (c3:real^3) dot ((Gl:real^3->real^3^3)((w:real^2->real^3) z0) ** c3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e. &0 < e /\ ball((w:real^2->real^3) z0,e) SUBSET IMAGE (phi:A->real^3) U`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open(IMAGE (phi:A->real^3) U)` MP_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?r. &0 < r /\ ball(z0,r) SUBSET Wc /\
        (!z. z IN ball(z0,r)
             ==> &0 < (c3:real^3) dot ((Gl:real^3->real^3^3)((w:real^2->real^3) z) **
                                       (cml_cov Gl w (partial_derivative 1 w) 1 z +
                                        cml_cov Gl w (partial_derivative 2 w) 2 z)) /\
                 dist(w z,w z0) < e / &2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\z. lift((c3:real^3) dot ((Gl:real^3->real^3^3)((w:real^2->real^3) z) **
                                 (cml_cov Gl w (partial_derivative 1 w) 1 z +
                                  cml_cov Gl w (partial_derivative 2 w) 2 z))))
      continuous at z0 /\ (w:real^2->real^3) continuous at z0`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `Wc:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (MP_TAC o SPEC `(c3:real^3) dot ((Gl:real^3->real^3^3)((w:real^2->real^3) z0) ** c3)`)
      (MP_TAC o SPEC `e / &2`)) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?d3. &0 < d3 /\ ball(z0:real^2,d3) SUBSET Wc` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
    EXISTS_TAC `min d1 (min d2 d3)` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z0:real^2,d3)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o
        check (fun th -> can (find_term (fun t -> t = `c3:real^3`)) (concl th) &&
                         is_forall(concl th))) THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[DIST_LIFT] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> t = `e / &2`)) (concl th))) THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. (w:real^2->real^3) z = (phi:A->real^3)((v:real^3->A)(stereo2_n_inv z))`
  (LABEL_TAC "WEQ") THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[cml_wc; SND]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN Wc <=> (v:real^3->A)(stereo2_n_inv z) IN U` (LABEL_TAC "WCIFF") THENL
   [EXPAND_TAC "Wc" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  (* the radius r2 on the sphere *)
  SUBGOAL_THEN
   `?r2. &0 < r2 /\
         (!y. y IN sphere(vec 0,&1) /\ norm(y - stereo2_n_inv z0) <= r2
              ==> y$3 < &1 /\ stereo2_n y IN ball(z0,r))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `stereo2_n continuous at (stereo2_n_inv z0)` MP_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `{x:real^3 | x$3 < &1}` THEN
      REWRITE_TAC[STEX_STEREO2_N_SMOOTH; OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM; CML_XN_3];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at; STEX_STEREO2_N_RIGHT] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d4:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?d5. &0 < d5 /\ ball(stereo2_n_inv z0,d5) SUBSET {x:real^3 | x$3 < &1}`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `open {x:real^3 | x$3 < &1}` MP_TAC THENL
       [REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT]; ALL_TAC] THEN
      REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_ELIM_THM; CML_XN_3];
      ALL_TAC] THEN
    EXISTS_TAC `min d4 d5 / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(y:real^3) IN ball(stereo2_n_inv z0,d5)` MP_TAC THENL
       [REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `ball(stereo2_n_inv z0,d5) SUBSET {x:real^3 | x$3 < &1}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
         can (find_term (fun t -> t = `stereo2_n`)) (concl th))) THEN
      REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the test field *)
  MP_TAC(ISPECL [`e / &2`; `norm(c3:real^3)`] CML_EPS_ARITH) THEN
  ASM_REWRITE_TAC[NORM_POS_LE; REAL_HALF] THEN
  ABBREV_TAC `eps = e / &2 / (norm(c3:real^3) + &1)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `U:A->bool`;
                 `phi:A->real^3`; `z0:real^2`; `r:real`; `e / &2`; `r2:real`; `eps:real`;
                 `c3:real^3`] CML_FAMHYP_BUMP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(z:real^2) IN Wc` MP_TAC THENL
       [UNDISCH_TAC `ball(z0:real^2,r) SUBSET Wc` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      FIRST_ASSUM(MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME `(z:real^2) IN ball(z0,r)`) o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> t = `e / &2`)) (concl th) &&
                         can (find_term (fun t -> t = `c3:real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball((w:real^2->real^3) z0,e)` THEN
      ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN CONV_TAC NORM_ARITH];
    DISCH_TAC] THEN
  REMOVE_THEN "WEQ" (K ALL_TAC) THEN REMOVE_THEN "WCIFF" (K ALL_TAC) THEN
  (* the planar test field *)
  SUBGOAL_THEN
   `smooth_map_on (:real^2)
      (\z. (eps * smooth_bump (r2 / &2) r2 (stereo2_n_inv z - stereo2_n_inv z0)) % (c3:real^3))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^2)`;
                   `\z. lift(eps * smooth_bump (r2 / &2) r2 (stereo2_n_inv z - stereo2_n_inv z0))`;
                   `\z:real^2. (c3:real^3)`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `(\z:real^2. lift(eps * smooth_bump (r2 / &2) r2 (stereo2_n_inv z - stereo2_n_inv z0))) =
      (\x. eps % lift(smooth_bump (r2 / &2) r2 x)) o (\z. stereo2_n_inv z - stereo2_n_inv z0)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; ETA_AX; STEX_STEREO2_N_INV_SMOOTH; SMOOTH_MAP_ON_CONST];
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
      MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `K = {z:real^2 | norm(stereo2_n_inv z - stereo2_n_inv z0) <= r2}` THEN
  SUBGOAL_THEN `K SUBSET ball(z0:real^2,r)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `stereo2_n_inv z` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> t = `stereo2_n`)) (concl th))) THEN
    REWRITE_TAC[IN_SPHERE_0; CML_P_NORM; STEX_STEREO2_N_RIGHT] THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(K:real^2->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `ball(z0:real^2,r)` THEN
      ASM_REWRITE_TAC[BOUNDED_BALL];
      SUBGOAL_THEN `K = {z:real^2 | stereo2_n_inv z - stereo2_n_inv z0 IN cball(vec 0,r2)}`
      SUBST1_TAC THENL
       [EXPAND_TAC "K" THEN REWRITE_TAC[IN_CBALL_0]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN REWRITE_TAC[CLOSED_CBALL] THEN
      GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_SUB THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
      MESON_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT; BEL_P_FRECHET; ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. ~(z IN K)
                    ==> (eps * smooth_bump (r2 / &2) r2 (stereo2_n_inv z - stereo2_n_inv z0)) %
                        (c3:real^3) = vec 0`
  ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM; REAL_NOT_LE] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `smooth_bump (r2 / &2) r2 (stereo2_n_inv z - stereo2_n_inv z0) = &0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_RZERO; VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  (* the first variation vanishes *)
  SUBGOAL_THEN
   `(\z. lift(if z IN Wc
              then cml_fvd Gl (w:real^2->real^3)
                     (\z. (eps * smooth_bump (r2 / &2) r2 (stereo2_n_inv z - stereo2_n_inv z0)) %
                          (c3:real^3)) z
              else &0)) absolutely_integrable_on (:real^2) /\
    drop(integral (:real^2)
           (\z. lift(if z IN Wc
                     then cml_fvd Gl w
                            (\z. (eps * smooth_bump (r2 / &2) r2
                                          (stereo2_n_inv z - stereo2_n_inv z0)) % c3) z
                     else &0))) = &0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `U:A->bool`;
                   `phi:A->real^3`;
                   `\y:real^3. (eps * smooth_bump (r2 / &2) r2 (inv(norm y) % y - stereo2_n_inv z0)) %
                               (c3:real^3)`;
                   `{y:real^3 | ~(y = vec 0) /\ r2 < norm(inv(norm y) % y - stereo2_n_inv z0)}`]
                  CML_FV_PLANE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CML_P_NORM; REAL_INV_1; VECTOR_MUL_LID] THEN
    EXPAND_TAC "Wc" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* integration by parts *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `Gl:real^3->real^3^3`; `Wc:real^2->bool`;
                 `w:real^2->real^3`;
                 `\z. (eps * smooth_bump (r2 / &2) r2 (stereo2_n_inv z - stereo2_n_inv z0)) %
                      (c3:real^3)`;
                 `K:real^2->bool`] CML_IBP_SUPP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z0:real^2,r)` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    REWRITE_TAC[] THEN STRIP_TAC] THEN
  (* positivity *)
  MP_TAC(ISPECL
   [`\z. if z IN Wc
         then ((eps * smooth_bump (r2 / &2) r2 (stereo2_n_inv z - stereo2_n_inv z0)) %
               (c3:real^3)) dot
              ((Gl:real^3->real^3^3)((w:real^2->real^3) z) **
               (cml_cov Gl w (partial_derivative 1 w) 1 z +
                cml_cov Gl w (partial_derivative 2 w) 2 z))
         else &0`; `z0:real^2`] CML_INTEGRAL_POS) THEN
  ANTS_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[REAL_LT_REFL]] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MP_TAC(ISPECL [`Wc:real^2->bool`; `K:real^2->bool`;
                   `\z. ((eps * smooth_bump (r2 / &2) r2 (stereo2_n_inv z - stereo2_n_inv z0)) %
                         (c3:real^3)) dot
                        ((Gl:real^3->real^3^3)((w:real^2->real^3) z) **
                         (cml_cov Gl w (partial_derivative 1 w) 1 z +
                          cml_cov Gl w (partial_derivative 2 w) 2 z))`] CML_GLUE_SMOOTH) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z0:real^2,r)` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `Gl:real^3->real^3^3`; `Wc:real^2->bool`;
                     `w:real^2->real^3`;
                     `\z. (eps * smooth_bump (r2 / &2) r2 (stereo2_n_inv z - stereo2_n_inv z0)) %
                          (c3:real^3)`;
                     `\z. cml_cov (Gl:real^3->real^3^3) (w:real^2->real^3)
                                  (partial_derivative 1 w) 1 z +
                          cml_cov Gl w (partial_derivative 2 w) 2 z`] CML_QUAD_SMOOTH) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      ASM_SIMP_TAC[DOT_LZERO]];
    X_GEN_TAC `z:real^2` THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    REWRITE_TAC[DOT_LMUL] THEN ASM_CASES_TAC `(z:real^2) IN K` THENL
     [SUBGOAL_THEN `(z:real^2) IN ball(z0,r)` ASSUME_TAC THENL
       [UNDISCH_TAC `K SUBSET ball(z0:real^2,r)` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; SMOOTH_BUMP_BOUNDS];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_X_ASSUM(MATCH_ACCEPT_TAC o CONJUNCT1 o
          C MATCH_MP (ASSUME `(z:real^2) IN ball(z0,r)`) o
          check (fun th -> is_forall(concl th) &&
                           can (find_term (fun t -> t = `e / &2`)) (concl th) &&
                           can (find_term (fun t -> t = `c3:real^3`)) (concl th)))];
      SUBGOAL_THEN `smooth_bump (r2 / &2) r2 (stereo2_n_inv z - stereo2_n_inv z0) = &0`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SMOOTH_BUMP_0 THEN UNDISCH_TAC `~((z:real^2) IN K)` THEN
        EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; REAL_LE_REFL]]];
    ASM_REWRITE_TAC[VECTOR_SUB_REFL] THEN
    SUBGOAL_THEN `smooth_bump (r2 / &2) r2 (vec 0:real^3) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_1 THEN REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; DOT_LMUL] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The pullback cml_pull through the embedding.  For X = stereo2_n_inv or   *)
(* stereo2_s_inv the matrix of a symmetric 2-tensor R (with ambient         *)
(* extension Qa) pulled back by v o X is d_a u . Qa(u) d_b u with u =       *)
(* (radial extension of f o v) o X; hence it is smooth on the plane.        *)
(* Stereographic facts and the inversion.                                   *)
(* ========================================================================= *)

let CML_P4_SMOOTH_C1 = prove
 (`!top atlas (u:real^3->A).
     p4_s2_smooth (top,atlas) u ==> p4_s2_c1 (top,atlas:((A->bool)#(A->real^N))->bool) u`,
  REWRITE_TAC[p4_s2_smooth; p4_s2_c1; smooth_map_on] THEN MESON_TAC[]);;

let CML_XS_PROPS = prove
 (`smooth_map_on (:real^2) stereo2_s_inv /\
   (!z. norm(stereo2_s_inv z) = &1) /\
   (!z. stereo2_s_inv differentiable at z)`,
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `stereo2_s_inv = bel_refl3 o stereo2_n_inv` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; BEL_Q_FORM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    REWRITE_TAC[OPEN_UNIV; STEX_STEREO2_N_INV_SMOOTH] THEN
    REWRITE_TAC[linear; bel_refl3; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[NORM_EQ_1; BEL_Q_FORM; BEL_REFL3_DOT; BEL_P_NORM];
    REWRITE_TAC[BEL_P_FRECHET]]);;

let CML_XN_PROPS = prove
 (`smooth_map_on (:real^2) stereo2_n_inv /\
   (!z. norm(stereo2_n_inv z) = &1) /\
   (!z. stereo2_n_inv differentiable at z)`,
  REWRITE_TAC[STEX_STEREO2_N_INV_SMOOTH; CML_P_NORM; BEL_P_FRECHET]);;

let CML_XN_XS = prove
 (`!z. ~(z = vec 0)
       ==> stereo2_n_inv z = stereo2_s_inv(cml_inv z) /\
           stereo2_s_inv z = stereo2_n_inv(cml_inv z)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_NORM) THEN
  MP_TAC(SPEC `z:real^2` BEL_QT_P) THEN MP_TAC(SPEC `cml_inv z` BEL_QT_P) THEN
  ASM_REWRITE_TAC[BEL_INV_CNJ_CMUL; GSYM cml_inv; GSYM COMPLEX_VEC_0] THEN
  SIMP_TAC[]);;

(* Smoothness of quadratic forms of a smooth ambient matrix field.          *)

let CML_KENTRY_SMOOTH = prove
 (`!(Q:real^K->real^K^K) i j.
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q)
     ==> smooth_map_on (:real^K) (\y. lift(Q y$i$j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. lift((Q:real^K->real^K^K) y$i$j)) =
                (\x:real^(K,K)finite_prod. lift((matrify x:real^K^K)$i$j)) o
                ((vectorize:real^K^K->real^(K,K)finite_prod) o Q)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[OPEN_UNIV; LRG_LINEAR_MATRIFY_ENTRY]);;

let CML_KQUAD_SMOOTH = prove
 (`!(Q:real^K->real^K^K) s (u:real^2->real^K) (a:real^2->real^K) b.
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
     open s /\ smooth_map_on s u /\ smooth_map_on s a /\ smooth_map_on s b
     ==> smooth_map_on s (\z. lift(a z dot (Q(u z) ** b z)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `a:real^2->real^K`;
                 `\z. (Q:real^K->real^K^K)((u:real^2->real^K) z) ** (b:real^2->real^K) z`]
                SMOOTH_MAP_ON_DOT_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE (ASSUME `open(s:real^2->bool)`)] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[dot] THEN
  SUBGOAL_THEN `(\z. lift(sum(1..dimindex(:K))
                    (\i. ((Q:real^K->real^K^K)((u:real^2->real^K) z))$k$i *
                         (b:real^2->real^K) z$i))) =
                (\z. lift(sum(1..dimindex(:K)) (\i. drop((\i z. lift(Q(u z)$k$i * b z$i)) i z))))`
  SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CML_SM_MUL THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT] THEN
  SUBGOAL_THEN `(\z. lift((Q:real^K->real^K^K)((u:real^2->real^K) z)$k$i)) =
                (\y. lift(Q y$k$i)) o u` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^K)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC CML_KENTRY_SMOOTH THEN ASM_REWRITE_TAC[]);;

(* The pullback through the embedding.                                       *)

let CML_PULL_EMB = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) (G:real^K->real^K^K) d (R:A->real^3^3)
    (Qa:real^K->real^K^K) (v:real^3->A) (X:real^2->real^3) z i j.
     cm_emb (top,atlas) g f G d /\
     (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
            ==> metric_local atlas c R w =
                transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                Qa(f(chart_inv c w)) **
                matrix(frechet_derivative (f o chart_inv c) (at w))) /\
     p4_s2_smooth (top,atlas) v /\
     (!z. X differentiable (at z)) /\ (!z. norm(X z) = &1) /\
     1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
     ==> cml_pull atlas R v X z$i$j =
         partial_derivative i (\z. wan_rext (f o v) (X z)) z dot
         (Qa(wan_rext (f o v) (X z)) ** partial_derivative j (\z. wan_rext (f o v) (X z)) z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  SUBGOAL_THEN `smooth_immersion_into (atlas:((A->bool)#(A->real^3))->bool) (f:A->real^K)`
  ASSUME_TAC THENL [ASM_MESON_TAC[mfd_embedding]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext ((f:A->real^K) o (v:real^3->A)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`] CM_P4_TO_EMB) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_rext ((f:A->real^K) o (v:real^3->A)) differentiable at ((X:real^2->real^3) z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN
    REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `R:A->real^3^3`;
                 `f:A->real^K`; `Qa:real^K->real^K^K`; `v:real^3->A`; `(X:real^2->real^3) z`]
                CM_S2_GRAM) THEN
  ASM_SIMP_TAC[CML_P4_SMOOTH_C1; IN_SPHERE_0] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[cml_pull; LAMBDA_BETA; DIMINDEX_2] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[BEL_JAC_APPLY] THEN
  SUBGOAL_THEN `(\z. wan_rext ((f:A->real^K) o (v:real^3->A)) ((X:real^2->real^3) z)) =
                wan_rext (f o v) o X` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[partial_derivative] THEN
  MP_TAC(ISPECL [`X:real^2->real^3`; `wan_rext ((f:A->real^K) o (v:real^3->A))`; `z:real^2`]
                BEL_FRECHET_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[wan_rext; o_THM; REAL_INV_1; VECTOR_MUL_LID]);;

let CML_PULL_SMOOTH = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) (G:real^K->real^K^K) d (R:A->real^3^3)
    (Qa:real^K->real^K^K) (v:real^3->A) (X:real^2->real^3) i j.
     cm_emb (top,atlas) g f G d /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Qa) /\
     (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
            ==> metric_local atlas c R w =
                transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                Qa(f(chart_inv c w)) **
                matrix(frechet_derivative (f o chart_inv c) (at w))) /\
     p4_s2_smooth (top,atlas) v /\
     smooth_map_on (:real^2) X /\ (!z. norm(X z) = &1) /\
     1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
     ==> smooth_map_on (:real^2) (\z. lift(cml_pull atlas R v X z$i$j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z. (X:real^2->real^3) differentiable at z` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(cml_pull atlas (R:A->real^3^3) (v:real^3->A) (X:real^2->real^3) z$i$j)) =
    (\z. lift(partial_derivative i (\z. wan_rext ((f:A->real^K) o v) (X z)) z dot
              ((Qa:real^K->real^K^K)(wan_rext (f o v) (X z)) **
               partial_derivative j (\z. wan_rext (f o v) (X z)) z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CML_PULL_EMB THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^3^3`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\z. wan_rext ((f:A->real^K) o (v:real^3->A))
                                                     ((X:real^2->real^3) z))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\z. wan_rext ((f:A->real^K) o (v:real^3->A)) ((X:real^2->real^3) z)) =
                  wan_rext (f o v) o X` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; OPEN_NONZERO; SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`] CM_P4_TO_EMB) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CML_KQUAD_SMOOTH THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
  CONJ_TAC THEN REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN
  ASM_REWRITE_TAC[OPEN_UNIV]);;

(* ========================================================================= *)
(* The inversion z |-> z/|z|^2 (the change between the two stereographic    *)
(* pictures) and the transformation of the pullbacks:  pull_1(z) = Dinv^T   *)
(* pull_2(inv z) Dinv  whenever X1 = X2 o cml_inv off 0.                    *)
(* ========================================================================= *)

let CML_INV_EQ = prove
 (`cml_inv = (\w:complex. inv(cnj w))`,
  REWRITE_TAC[FUN_EQ_THM; cml_inv; BEL_INV_CNJ_CMUL]);;

let CML_INV_FRECHET = prove
 (`!z:real^2. ~(z = vec 0)
              ==> cml_inv differentiable at z /\ frechet_derivative cml_inv (at z) = bel_dT z`,
  GEN_TAC THEN REWRITE_TAC[CML_INV_EQ; COMPLEX_VEC_0] THEN DISCH_TAC THEN
  MATCH_MP_TAC BEL_T_FRECHET THEN ASM_REWRITE_TAC[]);;

let CML_DT_DOT = prove
 (`!z h k. bel_dT z h dot bel_dT z k = inv(norm z pow 4) * (h dot k)`,
  REWRITE_TAC[BEL_T_CONF; COMPLEX_NORM_INV; COMPLEX_NORM_POW; REAL_POW_INV; REAL_POW_POW] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CML_DT_LINEAR = prove
 (`!z. linear(bel_dT z)`,
  GEN_TAC THEN REWRITE_TAC[bel_dT; linear; CNJ_ADD; CNJ_MUL; COMPLEX_CMUL; CNJ_CX] THEN
  CONV_TAC COMPLEX_RING);;

let CML_DT_COMPONENT = prove
 (`!z a k. 1 <= a /\ a <= 2 ==> abs((bel_dT z (basis a))$k) <= inv(norm z pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(bel_dT z (basis a))` THEN REWRITE_TAC[COMPONENT_LE_NORM] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[NORM_EQ_SQUARE; CML_DT_DOT] THEN
  ASM_SIMP_TAC[DOT_BASIS; BASIS_COMPONENT; DIMINDEX_2] THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_POW_LE; NORM_POS_LE; REAL_MUL_RID; REAL_POW_INV;
              REAL_POW_POW] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_LE_POW_2]);;

(* Derivatives in the plane through the basis.                               *)

let CML_FRECHET_BASIS2 = prove
 (`!(Fm:real^2->real^N) w h.
     Fm differentiable at w
     ==> frechet_derivative Fm (at w) h =
         h$1 % partial_derivative 1 Fm w + h$2 % partial_derivative 2 Fm w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM LINEAR_CMUL; GSYM LINEAR_ADD] THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           BASIS_COMPONENT; ARITH] THEN
  REAL_ARITH_TAC);;

(* The transformation of the pullback.                                       *)

let CML_PULL_COMP = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) (G:real^K->real^K^K) d (R:A->real^3^3)
    (Qa:real^K->real^K^K) (v:real^3->A) (X1:real^2->real^3) X2 z a b.
     cm_emb (top,atlas) g f G d /\
     (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
            ==> metric_local atlas c R w =
                transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                Qa(f(chart_inv c w)) **
                matrix(frechet_derivative (f o chart_inv c) (at w))) /\
     p4_s2_smooth (top,atlas) v /\
     smooth_map_on (:real^2) X1 /\ (!z. norm(X1 z) = &1) /\
     smooth_map_on (:real^2) X2 /\ (!z. norm(X2 z) = &1) /\
     (!z. ~(z = vec 0) ==> X1 z = X2(cml_inv z)) /\
     ~(z = vec 0) /\ 1 <= a /\ a <= 2 /\ 1 <= b /\ b <= 2
     ==> cml_pull atlas R v X1 z$a$b =
         sum(1..2) (\k. sum(1..2) (\l. (bel_dT z (basis a))$k * (bel_dT z (basis b))$l *
                                       cml_pull atlas R v X2 (cml_inv z)$k$l))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z. (X1:real^2->real^3) differentiable at z /\ (X2:real^2->real^3) differentiable at z`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  SUBGOAL_THEN `smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext ((f:A->real^K) o (v:real^3->A)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`] CM_P4_TO_EMB) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!X:real^2->real^3. smooth_map_on (:real^2) X /\ (!z. norm(X z) = &1)
                ==> smooth_map_on (:real^2) (\z. wan_rext ((f:A->real^K) o (v:real^3->A)) (X z))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(\z. wan_rext ((f:A->real^K) o (v:real^3->A)) ((X:real^2->real^3) z)) =
                  wan_rext (f o v) o X` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; OPEN_NONZERO; SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u1 = \z. wan_rext ((f:A->real^K) o (v:real^3->A)) ((X1:real^2->real^3) z)` THEN
  ABBREV_TAC `u2 = \z. wan_rext ((f:A->real^K) o (v:real^3->A)) ((X2:real^2->real^3) z)` THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (u1:real^2->real^K) /\ smooth_map_on (:real^2) (u2:real^2->real^K)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u1" THEN EXPAND_TAC "u2" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. (u1:real^2->real^K) differentiable at z /\ (u2:real^2->real^K) differentiable at z`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!X i j w. (X = X1 \/ X = X2) /\ 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
              ==> cml_pull atlas (R:A->real^3^3) (v:real^3->A) (X:real^2->real^3) w$i$j =
                  partial_derivative i (\z. wan_rext ((f:A->real^K) o v) (X z)) w dot
                  ((Qa:real^K->real^K^K)(wan_rext (f o v) (X w)) **
                   partial_derivative j (\z. wan_rext (f o v) (X z)) w)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CML_PULL_EMB THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^3^3`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_2] THEN ASM_SIMP_TAC[ARITH] THEN
  SUBGOAL_THEN `(\z. wan_rext ((f:A->real^K) o (v:real^3->A)) ((X1:real^2->real^3) z)) = u1 /\
                (\z. wan_rext ((f:A->real^K) o (v:real^3->A)) ((X2:real^2->real^3) z)) = u2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_rext ((f:A->real^K) o (v:real^3->A)) ((X1:real^2->real^3) z) =
                (u2:real^2->real^K)(cml_inv z)` SUBST1_TAC THENL
   [EXPAND_TAC "u2" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. partial_derivative i (u1:real^2->real^K) z =
        frechet_derivative (u2:real^2->real^K) (at (cml_inv z)) (bel_dT z (basis i))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `partial_derivative i (u1:real^2->real^K) z =
                  partial_derivative i ((u2:real^2->real^K) o cml_inv) z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
      EXISTS_TAC `{z:real^2 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN EXPAND_TAC "u1" THEN EXPAND_TAC "u2" THEN
      ASM_SIMP_TAC[o_THM];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_FRECHET) THEN
    REWRITE_TAC[partial_derivative] THEN
    MP_TAC(ISPECL [`cml_inv`; `u2:real^2->real^K`; `z:real^2`] BEL_FRECHET_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CML_FRECHET_BASIS2] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              MATRIX_VECTOR_MUL_RMUL] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Hopf's argument.  The Hopf differential (|e|^2 - |f|^2) - 2i <e,f> of a  *)
(* harmonic sphere in the north stereographic plane is holomorphic          *)
(* (Cauchy-Riemann from the Euler-Lagrange equation in charts) and decays   *)
(* like |z|^-4 (south picture), so it vanishes by Liouville: the map is     *)
(* conformal.                                                               *)
(* ========================================================================= *)

let CML_HOLO_FROM_CR = prove
 (`!(A:real^2->real) B.
     smooth_map_on (:real^2) (\z. lift(A z)) /\ smooth_map_on (:real^2) (\z. lift(B z)) /\
     (!z. cml_d 1 A z = cml_d 2 B z /\ cml_d 2 A z = --(cml_d 1 B z))
     ==> (\z. vector[A z; B z]:complex) holomorphic_on (:complex)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[GSYM complex_differentiable] THEN
  REWRITE_TAC[CAUCHY_RIEMANN] THEN
  SUBGOAL_THEN `(\x:real^2. lift((A:real^2->real) x)) differentiable at z /\
                (\x:real^2. lift((B:real^2->real) x)) differentiable at z`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. vector[(A:real^2->real) z; (B:real^2->real) z]:complex) differentiable at z`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE OPEN_UNIV] THEN
    REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
          ==> jacobian (\z. vector[(A:real^2->real) z; (B:real^2->real) z]:complex) (at z)$i$j =
              cml_d j (\x. (vector[A x; B x]:real^2)$i) z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[jacobian; matrix; LAMBDA_BETA; DIMINDEX_2] THEN
    ASM_SIMP_TAC[CML_FRECHET_COMPONENT; DIMINDEX_2] THEN
    REWRITE_TAC[cml_d; partial_derivative];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH] THEN REWRITE_TAC[VECTOR_2; ETA_AX] THEN ASM_REWRITE_TAC[]);;

let CML_DECAY_ARITH = prove
 (`!a b C n e. &0 < e /\ &0 < n /\ a <= C / n /\ b <= C / n /\ &2 * (abs C + &1) <= e * n
               ==> a + b < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&2 * C) / n < e` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  UNDISCH_TAC `a <= C / n` THEN UNDISCH_TAC `b <= C / n` THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let CML_LIOUVILLE_ZERO = prove
 (`!(A:real^2->real) B C.
     smooth_map_on (:real^2) (\z. lift(A z)) /\ smooth_map_on (:real^2) (\z. lift(B z)) /\
     (!z. cml_d 1 A z = cml_d 2 B z /\ cml_d 2 A z = --(cml_d 1 B z)) /\
     (!z. &1 <= norm z ==> abs(A z) <= C / norm z pow 4 /\ abs(B z) <= C / norm z pow 4)
     ==> !z. A z = &0 /\ B z = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. vector[(A:real^2->real) z; (B:real^2->real) z]:complex`; `Cx(&0)`]
                LIOUVILLE_WEAK) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC CML_HOLO_FROM_CR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LIM_AT_INFINITY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    EXISTS_TAC `max (&1) ((&2 * (abs C + &1)) / e)` THEN X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[real_ge; REAL_MAX_LE] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[dist; GSYM COMPLEX_VEC_0; VECTOR_SUB_RZERO] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs((A:real^2->real) z) + abs((B:real^2->real) z)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:2)) (\i. abs((vector[(A:real^2->real) z; B z]:real^2)$i))` THEN
      REWRITE_TAC[NORM_LE_L1] THEN REWRITE_TAC[DIMINDEX_2; SUM_2; VECTOR_2; REAL_LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC CML_DECAY_ARITH THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `norm(z:complex) pow 4`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 <= norm(z:complex) pow 4 /\ norm z <= norm z pow 4` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN MATCH_MP_TAC REAL_POW_MONO THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e * norm(z:complex)` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(&2 * (abs C + &1)) / e <= norm(z:complex)` THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN DISCH_TAC THEN X_GEN_TAC `z:real^2` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2`) THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
  SIMP_TAC[]);;

(* ========================================================================= *)
(* Conformality of a harmonic sphere in both stereographic pictures, and    *)
(* the relation of the conformal factors:                                   *)
(*   pull_n = lam I,  pull_s = lamq I,  lam z = lamq(inv z) / |z|^4.        *)
(* ========================================================================= *)

let cml_hs = new_definition
 `cml_hs (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
         (f:A->real^K) (G:real^K->real^K^K) (d:real) (v:real^3->A) <=>
    cm_emb (top,atlas) g f G d /\ p4_s2_smooth (top,atlas) v /\
    (!y. y IN sphere(vec 0,&1) ==> v y IN topspace top) /\
    smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (f o v)) /\
    (!psi:real^3->real^K.
        smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext psi)
        ==> ((\e. cm_sen G (\y. closest_point (IMAGE f (topspace top))
                                               ((f o v) y + e % psi y)))
             has_real_derivative &0) (atreal (&0)))`;;

let CML_HS_CHART = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) y.
     cml_hs (top,atlas) g f G d v /\ y IN sphere(vec 0,&1)
     ==> ?U phi. (U,phi) IN atlas /\ v y IN U`,
  REWRITE_TAC[cml_hs; cm_emb] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(v:real^3->A) y`]
                CHART_AT) THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^3))->bool) ((v:real^3->A) y)`
               PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST] THEN MESON_TAC[]);;

(* The Cauchy-Riemann equations of the Hopf differential, globally.          *)

let CML_CR_GLOBAL = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) z0.
     cml_hs (top,atlas) g f G d v
     ==> cml_d 1 (\z. cml_pull atlas g v stereo2_n_inv z$1$1 -
                      cml_pull atlas g v stereo2_n_inv z$2$2) z0 =
         -- &2 * cml_d 2 (\z. cml_pull atlas g v stereo2_n_inv z$1$2) z0 /\
         cml_d 2 (\z. cml_pull atlas g v stereo2_n_inv z$1$1 -
                      cml_pull atlas g v stereo2_n_inv z$2$2) z0 =
         &2 * cml_d 1 (\z. cml_pull atlas g v stereo2_n_inv z$1$2) z0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                 `stereo2_n_inv z0`] CML_HS_CHART) THEN
  ASM_REWRITE_TAC[IN_SPHERE_0; CML_P_NORM] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cml_hs]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `v:real^3->A`;
                 `U:A->bool`; `phi:A->real^3`] CML_CHART_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^3) U) (metric_local atlas (U,phi) (g:A->real^3^3))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `metric_field (IMAGE (SND(U:A->bool,phi:A->real^3)) (FST(U:A->bool,phi)))
                               (metric_local atlas (U,phi) (g:A->real^3^3))` MP_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; REWRITE_TAC[FST; SND]];
    ALL_TAC] THEN
  ABBREV_TAC `Wc = {z:real^2 | (v:real^3->A)(stereo2_n_inv z) IN U}` THEN
  ABBREV_TAC `w = cml_wc (U:A->bool,phi:A->real^3) (v:real^3->A) stereo2_n_inv` THEN
  ABBREV_TAC `Gl = metric_local atlas (U:A->bool,phi:A->real^3) (g:A->real^3^3)` THEN
  SUBGOAL_THEN `(z0:real^2) IN Wc` ASSUME_TAC THENL
   [EXPAND_TAC "Wc" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z i j. z IN Wc /\ 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
            ==> cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv z$i$j =
                partial_derivative i (w:real^2->real^3) z dot
                ((Gl:real^3->real^3^3)(w z) ** partial_derivative j w z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "w" THEN EXPAND_TAC "Gl" THEN
    REWRITE_TAC[cml_wc; SND] THEN MATCH_MP_TAC CML_PULL_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[CML_XN_PROPS] THEN
    UNDISCH_TAC `(z:real^2) IN Wc` THEN EXPAND_TAC "Wc" THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN Wc
        ==> cml_cov Gl (w:real^2->real^3) (partial_derivative 1 w) 1 z +
            cml_cov Gl w (partial_derivative 2 w) 2 z = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "w" THEN EXPAND_TAC "Gl" THEN
    MATCH_MP_TAC CML_EL_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^2) IN Wc` THEN EXPAND_TAC "Wc" THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `Gl:real^3->real^3^3`; `Wc:real^2->bool`;
                 `w:real^2->real^3`; `z0:real^2`] CML_HOPF_CR) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(a <=> a') /\ (b <=> b') ==> a /\ b ==> a' /\ b'`) THEN
  REPEAT CONJ_TAC THEN
  BINOP_TAC THEN TRY AP_TERM_TAC THEN
  MATCH_MP_TAC CML_D_LOCAL THEN EXISTS_TAC `Wc:real^2->bool` THEN
  ASM_SIMP_TAC[ARITH]);;

(* Small arithmetic and continuity facts.                                     *)

let CML_ABS3 = prove
 (`!a b p t M. abs a <= t /\ abs b <= t /\ abs p <= M ==> abs(a * b * p) <= t * t * M`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS; REAL_LE_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

let CML_CONT_ZERO_EXT = prove
 (`!(F0:real^2->real) z0.
     (\w. lift(F0 w)) continuous at z0 /\ (!w. ~(w = z0) ==> F0 w = &0) ==> F0 z0 = &0`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `abs((F0:real^2->real) z0)` o REWRITE_RULE[continuous_at]) THEN
  ASM_REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(z0 + (e / &2) % basis 1:real^2 = z0)` ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `a + b:real^N = a <=> b = vec 0`; VECTOR_MUL_EQ_0] THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z0 + (e / &2) % basis 1:real^2`) THEN
  REWRITE_TAC[dist; VECTOR_ARITH `(a + b) - a:real^N = b`; NORM_MUL; GSYM LIFT_SUB; NORM_LIFT] THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CML_CONT_BOUNDED_CBALL = prove
 (`!h:real^2->real.
     (\z. lift(h z)) continuous_on (:real^2) ==> ?M. !w. w IN cball(vec 0,&1) ==> abs(h w) <= M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. lift((h:real^2->real) z)`; `cball(vec 0:real^2,&1)`]
                COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN MESON_TAC[]);;

(* Conformality in the north picture.                                         *)

let CML_HS_PULL_SMOOTH = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) X i j.
     cml_hs (top,atlas) g f G d v /\
     smooth_map_on (:real^2) X /\ (!z. norm(X z) = &1) /\
     1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
     ==> smooth_map_on (:real^2) (\z. lift(cml_pull atlas g v X z$i$j))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cml_hs]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target] o
    check (fun th -> is_comb(concl th) && is_comb(rator(concl th)) &&
                     is_comb(rator(rator(concl th))) &&
                     is_const(rator(rator(rator(concl th)))) &&
                     fst(dest_const(rator(rator(rator(concl th))))) = "cm_target")) THEN
  MATCH_MP_TAC CML_PULL_SMOOTH THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^3^3`; `f:A->real^K`; `G:real^K->real^K^K`;
                        `d:real`; `G:real^K->real^K^K`] THEN
  ASM_REWRITE_TAC[]);;

let CML_PULL_DECAY = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) M z a b.
     cml_hs (top,atlas) g f G d v /\
     (!w k l. w IN cball(vec 0,&1) /\ 1 <= k /\ k <= 2 /\ 1 <= l /\ l <= 2
              ==> abs(cml_pull atlas g v stereo2_s_inv w$k$l) <= M) /\
     &1 <= norm z /\ 1 <= a /\ a <= 2 /\ 1 <= b /\ b <= 2
     ==> abs(cml_pull atlas g v stereo2_n_inv z$a$b) <= &4 * M / norm z pow 4`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(z:real^2 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cml_hs]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `g:A->real^3^3`;
                 `G:real^K->real^K^K`; `v:real^3->A`; `stereo2_n_inv`; `stereo2_s_inv`;
                 `z:real^2`; `a:num`; `b:num`] CML_PULL_COMP) THEN
  ASM_REWRITE_TAC[CML_XN_PROPS; CML_XS_PROPS] THEN
  ANTS_TAC THENL [SIMP_TAC[CML_XN_XS]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `cml_inv z IN cball(vec 0:real^2,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL_0] THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_NORM) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * M / norm(z:real^2) pow 4 =
                &4 * (inv(norm z pow 2) * inv(norm z pow 2) * M)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN
    SUBGOAL_THEN `inv(norm(z:real^2) pow 4) = inv(norm z pow 2) * inv(norm z pow 2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_INV_MUL; GSYM REAL_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_2] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs p <= q /\ abs r <= q /\ abs s <= q /\ abs t <= q
    ==> abs((p + r) + (s + t)) <= &4 * q`) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC CML_ABS3 THEN
  ASM_SIMP_TAC[CML_DT_COMPONENT; ARITH]);;

let CML_CONFORMAL_N = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A).
     cml_hs (top,atlas) g f G d v
     ==> !z. cml_pull atlas g v stereo2_n_inv z$1$1 = cml_pull atlas g v stereo2_n_inv z$2$2 /\
             cml_pull atlas g v stereo2_n_inv z$1$2 = &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!X i j. (X = stereo2_n_inv \/ X = stereo2_s_inv) /\ 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
            ==> smooth_map_on (:real^2)
                  (\z. lift(cml_pull atlas (g:A->real^3^3) (v:real^3->A) X z$i$j))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CML_HS_PULL_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[CML_XN_PROPS; CML_XS_PROPS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?M. !w k l. w IN cball(vec 0,&1) /\ 1 <= k /\ k <= 2 /\ 1 <= l /\ l <= 2
                ==> abs(cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_s_inv w$k$l) <= M`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `\w. abs(cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_s_inv w$1$1) +
                      abs(cml_pull atlas g v stereo2_s_inv w$1$2) +
                      abs(cml_pull atlas g v stereo2_s_inv w$2$1) +
                      abs(cml_pull atlas g v stereo2_s_inv w$2$2)` CML_CONT_BOUNDED_CBALL) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[LIFT_ADD] THEN
      REPEAT(MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC) THEN
      REWRITE_TAC[GSYM NORM_LIFT] THEN
      (MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE ORELSE ALL_TAC) THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[ARITH];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN EXISTS_TAC `M:real` THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(k = 1 \/ k = 2) /\ (l = 1 \/ l = 2)` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `w:real^2`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv z$1$1 -
                      cml_pull atlas g v stereo2_n_inv z$2$2`;
                 `\z. -- &2 * cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv z$1$2`;
                 `&8 * M`] CML_LIOUVILLE_ZERO) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CML_SM_SUB THEN ASM_SIMP_TAC[OPEN_UNIV; ARITH];
      MATCH_MP_TAC CML_SM_CMUL THEN ASM_SIMP_TAC[OPEN_UNIV; ARITH];
      X_GEN_TAC `z:real^2` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `z:real^2`]
                    CML_CR_GLOBAL) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `!i. cml_d i (\z. -- &2 * cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv z$1$2) z =
            -- &2 * cml_d i (\z. cml_pull atlas g v stereo2_n_inv z$1$2) z`
      (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN MATCH_MP_TAC CML_D_CMUL THEN EXISTS_TAC `(:real^2)` THEN
        ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; ARITH];
        REAL_ARITH_TAC];
      X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `M:real`;
                     `z:real^2`] CML_PULL_DECAY) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`1`; `1`] (ASSUME `!a b. 1 <= a /\ a <= 2 /\ 1 <= b /\ b <= 2
            ==> abs(cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv z$a$b) <=
                &4 * M / norm z pow 4`)) THEN
      MP_TAC(SPECL [`2`; `2`] (ASSUME `!a b. 1 <= a /\ a <= 2 /\ 1 <= b /\ b <= 2
            ==> abs(cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv z$a$b) <=
                &4 * M / norm z pow 4`)) THEN
      MP_TAC(SPECL [`1`; `2`] (ASSUME `!a b. 1 <= a /\ a <= 2 /\ 1 <= b /\ b <= 2
            ==> abs(cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv z$a$b) <=
                &4 * M / norm z pow 4`)) THEN
      REWRITE_TAC[ARITH] THEN
      REWRITE_TAC[real_div; REAL_ARITH `(&8 * M) * x = &2 * ((&4 * M) * x)`] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_NUM] THEN REAL_ARITH_TAC];
    REWRITE_TAC[REAL_SUB_0; REAL_ENTIRE] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* The south picture is conformal too, the conformal factors are related by *)
(* lam z = lamq(inv z) / |z|^4, and both are nonnegative and smooth.        *)
(* ========================================================================= *)

let CML_HS_TARGET = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A).
     cml_hs (top,atlas) g f G d v
     ==> smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
         (!z. transp(G z) = G z) /\
         (?lam. &0 < lam /\ !z u. lam * norm u pow 2 <= u dot (G z ** u)) /\
         (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
                ==> metric_local atlas c g w =
                    transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                    G(f(chart_inv c w)) **
                    matrix(frechet_derivative (f o chart_inv c) (at w)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cml_hs; cm_emb] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let CML_HS_PULL = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) X z i j.
     cml_hs (top,atlas) g f G d v /\
     smooth_map_on (:real^2) X /\ (!z. norm(X z) = &1) /\
     1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
     ==> cml_pull atlas g v X z$i$j =
         partial_derivative i (\z. wan_rext (f o v) (X z)) z dot
         (G(wan_rext (f o v) (X z)) ** partial_derivative j (\z. wan_rext (f o v) (X z)) z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_HS_TARGET) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cml_hs]) THEN
  MATCH_MP_TAC CML_PULL_EMB THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^3^3`; `G:real^K->real^K^K`; `d:real`] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let CML_PULL_SYM = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) X z.
     cml_hs (top,atlas) g f G d v /\ smooth_map_on (:real^2) X /\ (!z. norm(X z) = &1)
     ==> cml_pull atlas g v X z$2$1 = cml_pull atlas g v X z$1$2 /\
         &0 <= cml_pull atlas g v X z$1$1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_HS_TARGET) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                 `X:real^2->real^3`; `z:real^2`] CML_HS_PULL) THEN
  ASM_SIMP_TAC[ARITH] THEN DISCH_TAC THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM DOT_MATRIX_TRANSP_LMUL] THEN
    ASM_REWRITE_TAC[] THEN MATCH_ACCEPT_TAC DOT_SYM;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lam * norm(partial_derivative 1
                  (\z. wan_rext ((f:A->real^K) o (v:real^3->A)) ((X:real^2->real^3) z)) z) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2]]);;

(* Conformality in the south picture and the relation of the factors.        *)

let CML_CONFORMAL_S = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A).
     cml_hs (top,atlas) g f G d v
     ==> (!z. cml_pull atlas g v stereo2_s_inv z$1$1 = cml_pull atlas g v stereo2_s_inv z$2$2 /\
              cml_pull atlas g v stereo2_s_inv z$1$2 = &0) /\
         (!z. ~(z = vec 0)
              ==> cml_pull atlas g v stereo2_s_inv z$1$1 =
                  cml_pull atlas g v stereo2_n_inv (cml_inv z)$1$1 / norm z pow 4)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CML_CONFORMAL_N) THEN
  SUBGOAL_THEN
   `!z a b. ~(z = vec 0) /\ 1 <= a /\ a <= 2 /\ 1 <= b /\ b <= 2
            ==> cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_s_inv z$a$b =
                cml_pull atlas g v stereo2_n_inv (cml_inv z)$1$1 *
                inv(norm z pow 4) * (basis a dot basis b:real^2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_HS_TARGET) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cml_hs]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `g:A->real^3^3`;
                   `G:real^K->real^K^K`; `v:real^3->A`; `stereo2_s_inv`; `stereo2_n_inv`;
                   `z:real^2`; `a:num`; `b:num`] CML_PULL_COMP) THEN
    ASM_REWRITE_TAC[CML_XN_PROPS; CML_XS_PROPS] THEN
    ANTS_TAC THENL [SIMP_TAC[CML_XN_XS]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                   `stereo2_n_inv`; `cml_inv z`] CML_PULL_SYM) THEN
    ASM_REWRITE_TAC[CML_XN_PROPS] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `cml_inv z` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> t = `stereo2_n_inv`)) (concl th) &&
                       not (can (find_term (fun t -> t = `stereo2_s_inv`)) (concl th)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[SUM_2] THEN
    REWRITE_TAC[GSYM CML_DT_DOT; DOT_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ARITH] THEN
    SIMP_TAC[DOT_BASIS; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[real_div; REAL_MUL_RID]] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
          ==> (\z. lift(cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_s_inv z$i$j))
              continuous at (vec 0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN MATCH_MP_TAC CML_HS_PULL_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[CML_XS_PROPS];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN ASM_CASES_TAC `z:real^2 = vec 0` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[ARITH] THEN SIMP_TAC[DOT_BASIS; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a - b = &0 /\ c = &0 ==> a = b /\ c = &0`) THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\w. cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_s_inv w$1$1 -
                        cml_pull atlas g v stereo2_s_inv w$2$2`; `vec 0:real^2`]
                  CML_CONT_ZERO_EXT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_SUB THEN ASM_SIMP_TAC[ARITH];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ARITH] THEN
      SIMP_TAC[DOT_BASIS; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC];
    MP_TAC(ISPECL [`\w. cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_s_inv w$1$2`;
                   `vec 0:real^2`] CML_CONT_ZERO_EXT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ARITH] THEN
      SIMP_TAC[DOT_BASIS; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* The curvature algebra in dimension 3. For G-orthogonal e, f of equal     *)
(* G-length lam:                                                            *)
(*   Rm(e,f,f,e) = lam (Ric(e,e) + Ric(f,f)) - lam^2 Scal / 2,               *)
(* from the traces of Ric and Scal in a G-orthonormal basis (e,f,n)/sqrt.   *)
(* ========================================================================= *)

let CML_CONJ_ENTRY = prove
 (`!(A:real^N^N) (X:real^N^N) j k.
     1 <= j /\ j <= dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
     ==> (A ** X ** transp A)$j$k = A$j dot (X ** A$k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA; dot; matrix_vector_mul] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[transp; LAMBDA_BETA]);;

let CML_GTRACE = prove
 (`!(G:real^3^3) b1 b2 b3.
     b1 dot (G ** b1) = &1 /\ b2 dot (G ** b2) = &1 /\ b3 dot (G ** b3) = &1 /\
     b1 dot (G ** b2) = &0 /\ b1 dot (G ** b3) = &0 /\ b2 dot (G ** b3) = &0 /\
     b2 dot (G ** b1) = &0 /\ b3 dot (G ** b1) = &0 /\ b3 dot (G ** b2) = &0
     ==> (!N:real^3^3. trace N = b1 dot (G ** N ** b1) + b2 dot (G ** N ** b2) +
                                 b3 dot (G ** N ** b3)) /\
         (!M:real^3^3. sum(1..3) (\i. sum(1..3) (\j. matrix_inv G$i$j * M$i$j)) =
                       b1 dot (M ** b1) + b2 dot (M ** b2) + b3 dot (M ** b3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = vector[b1:real^3;b2;b3]:real^3^3` THEN
  SUBGOAL_THEN `(R:real^3^3)$1 = b1 /\ R$2 = b2 /\ R$3 = b3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[VECTOR_3]; ALL_TAC] THEN
  SUBGOAL_THEN `(R:real^3^3) ** (G:real^3^3) ** transp R = mat 1` ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    SIMP_TAC[CML_CONJ_ENTRY; DIMINDEX_3; ARITH] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[mat; LAMBDA_BETA; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp(R:real^3^3) ** (R ** (G:real^3^3)) = mat 1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MATRIX_LEFT_RIGHT_INVERSE] THEN ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `N:real^3^3` THEN
    SUBGOAL_THEN `trace((R:real^3^3) ** ((G:real^3^3) ** N) ** transp R) = trace(N:real^3^3)`
    (SUBST1_TAC o SYM) THENL
     [GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
      GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
      ASM_REWRITE_TAC[MATRIX_MUL_RID];
      ALL_TAC] THEN
    SIMP_TAC[trace; DIMINDEX_3; SUM_3; CML_CONJ_ENTRY; ARITH] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  X_GEN_TAC `M:real^3^3` THEN
  SUBGOAL_THEN `matrix_inv(G:real^3^3) = transp(R:real^3^3) ** R` SUBST1_TAC THENL
   [MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
    SUBGOAL_THEN `(transp(R:real^3^3) ** R) ** (G:real^3^3) = mat 1` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[MATRIX_LEFT_RIGHT_INVERSE] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..3) (\i. sum(1..3) (\j. (transp(R:real^3^3) ** R)$i$j * (M:real^3^3)$i$j)) =
    trace(R ** M ** transp R)`
  SUBST1_TAC THENL
   [SIMP_TAC[trace; matrix_mul; transp; LAMBDA_BETA; DIMINDEX_3; SUM_3; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[trace; DIMINDEX_3; SUM_3; CML_CONJ_ENTRY; ARITH] THEN ASM_REWRITE_TAC[]);;

(* A G-unit vector G-orthogonal to two G-orthogonal vectors of equal length. *)

let cml_cross = new_definition
 `cml_cross (e:real^3) (f:real^3) =
    vector[e$2 * f$3 - e$3 * f$2; e$3 * f$1 - e$1 * f$3; e$1 * f$2 - e$2 * f$1]:real^3`;;

let CML_CROSS_PROPS = prove
 (`!e f:real^3. e dot cml_cross e f = &0 /\ f dot cml_cross e f = &0 /\
                (cml_cross e f = vec 0 ==> (e dot e) % f = (e dot f) % e)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[cml_cross; DOT_3; VECTOR_3; CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  CONV_TAC REAL_RING);;

let CML_GNORMAL = prove
 (`!V (G:real^3->real^3^3) y e f lam.
     metric_field V G /\ y IN V /\ &0 < lam /\
     e dot (G y ** e) = lam /\ f dot (G y ** f) = lam /\ e dot (G y ** f) = &0
     ==> ?n. n dot (G y ** n) = &1 /\ e dot (G y ** n) = &0 /\ f dot (G y ** n) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible((G:real^3->real^3^3) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  ABBREV_TAC `m = matrix_inv((G:real^3->real^3^3) y) ** cml_cross e f` THEN
  SUBGOAL_THEN `(G:real^3->real^3^3) y ** m = cml_cross e f` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(G:real^3->real^3^3) y ** m = cml_cross e f` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (last(CONJUNCTS(SPEC_ALL CML_CROSS_PROPS))) o SYM) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^3. x dot ((G:real^3->real^3^3) y ** f)`) THEN
    ASM_REWRITE_TAC[DOT_LMUL; REAL_MUL_RZERO] THEN
    REWRITE_TAC[REAL_ENTIRE; DOT_EQ_0] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `vec 0 dot ((G:real^3->real^3^3) y ** vec 0) = lam` THEN
    REWRITE_TAC[DOT_LZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < m dot ((G:real^3->real^3^3) y ** m)` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `V:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `inv(sqrt(m dot ((G:real^3->real^3^3) y ** m))) % m` THEN
  UNDISCH_TAC `&0 < m dot ((G:real^3->real^3^3) y ** m)` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[DOT_LMUL; DOT_RMUL; MATRIX_VECTOR_MUL_RMUL; CML_CROSS_PROPS;
                  REAL_MUL_RZERO] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_2; REAL_POW_INV] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_MUL_LINV; REAL_LT_IMP_NZ]);;

let CML_LRICCI_SCALE = prove
 (`!V (G:real^3->real^3^3) y c a.
     metric_field V G /\ y IN V
     ==> lricci G y (c % a) (c % a) = c * c * lricci G y a a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(BETA_RULE(SPECL [`c:real`; `a:real^3`] (MATCH_MP LINEAR_CMUL
    (SPEC `c % a:real^3` (ASSUME `!b. linear (\a. lift(lricci (G:real^3->real^3^3) y a b))`))))) THEN
  MP_TAC(BETA_RULE(SPECL [`c:real`; `a:real^3`] (MATCH_MP LINEAR_CMUL
    (SPEC `a:real^3` (ASSUME `!a. linear (\b. lift(lricci (G:real^3->real^3^3) y a b))`))))) THEN
  REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN
  DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CML_LRIEMANN_SCALE = prove
 (`!V (G:real^3->real^3^3) y c u v w.
     metric_field V G /\ y IN V
     ==> lriemann G y (c % u) v w = c % lriemann G y u v w /\
         lriemann G y u (c % v) w = c % lriemann G y u v w /\
         lriemann G y u v (c % w) = c % lriemann G y u v w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REPEAT CONJ_TAC THEN
    MP_TAC(BETA_RULE(SPECL [`c:real`] (MATCH_MP LINEAR_CMUL (SPEC_ALL(CONJUNCT1 th))))) THEN
    MP_TAC(BETA_RULE(SPECL [`c:real`] (MATCH_MP LINEAR_CMUL (SPEC_ALL(CONJUNCT1(CONJUNCT2 th)))))) THEN
    MP_TAC(BETA_RULE(SPECL [`c:real`] (MATCH_MP LINEAR_CMUL (SPEC_ALL(CONJUNCT2(CONJUNCT2 th))))))) THEN
  SIMP_TAC[]);;

let CML_RIC_ALG = prove
 (`!V (G:real^3->real^3^3) y e f lam.
     metric_field V G /\ y IN V /\
     e dot (G y ** e) = lam /\ f dot (G y ** f) = lam /\ e dot (G y ** f) = &0
     ==> e dot (G y ** lriemann G y e f f) =
         lam * (lricci G y e e + lricci G y f f) - lam pow 2 * lscalar G y / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `lam = &0` THENL
   [SUBGOAL_THEN `e:real^3 = vec 0` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[CML_GPOS]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL
   [ASM_MESON_TAC[CML_GPOS; REAL_LT_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `e:real^3`; `f:real^3`;
                 `lam:real`] CML_GNORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n:real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `s = inv(sqrt lam)` THEN
  SUBGOAL_THEN `s pow 2 * lam = &1` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[REAL_POW_INV] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. a dot ((G:real^3->real^3^3) y ** b) = b dot (G y ** a)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `f dot ((G:real^3->real^3^3) y ** e) = &0 /\ n dot (G y ** e) = &0 /\
                n dot (G y ** f) = &0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `s % e:real^3`; `s % f:real^3`; `n:real^3`]
                CML_GTRACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DOT_LMUL; DOT_RMUL; MATRIX_VECTOR_MUL_RMUL; REAL_MUL_RZERO] THEN
    UNDISCH_TAC `s pow 2 * lam = &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "TR") (LABEL_TAC "SC"))] THEN
  SUBGOAL_THEN
   `!u w. lricci (G:real^3->real^3^3) y u w =
          (s % e) dot (G y ** lriemann G y (s % e) u w) +
          (s % f) dot (G y ** lriemann G y (s % f) u w) +
          n dot (G y ** lriemann G y n u w)`
  (LABEL_TAC "RIC") THENL
   [REPEAT GEN_TAC THEN
    USE_THEN "TR" (MP_TAC o SPEC `matrix(\x. lriemann (G:real^3->real^3^3) y x u w)`) THEN
    ASM_SIMP_TAC[MATRIX_WORKS; LRG_TRACE_MATRIX] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[lricci];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lscalar (G:real^3->real^3^3) y =
    lricci G y (s % e) (s % e) + lricci G y (s % f) (s % f) + lricci G y n n`
  ASSUME_TAC THENL
   [USE_THEN "SC" (MP_TAC o SPEC `(lambda i j. lricci (G:real^3->real^3^3) y (basis i) (basis j)):real^3^3`) THEN
    REWRITE_TAC[MATCH_MP CMT_LRICCI_MATRIX
      (CONJ (ASSUME `metric_field (V:real^3->bool) (G:real^3->real^3^3)`)
            (ASSUME `(y:real^3) IN V`))] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SIMP_TAC[lscalar; DIMINDEX_3; SUM_3; LAMBDA_BETA; ARITH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CML_LRICCI_SCALE] THEN
  USE_THEN "RIC" (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] CML_LRIEMANN_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN
   `!u w. lriemann (G:real^3->real^3^3) y u u w = vec 0`
  (fun th -> REWRITE_TAC[th; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO]) THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`; `u:real^3`;
                   `w:real^3`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. b dot ((G:real^3->real^3^3) y ** lriemann G y b a a) =
          a dot (G y ** lriemann G y a b b)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `b:real^3`; `a:real^3`;
                   `a:real^3`; `b:real^3`] LRIEMANN_METRIC_ANTISYM) THEN
    MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `a:real^3`; `b:real^3`;
                   `a:real^3`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_RNEG] THEN
    MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `a:real^3`; `b:real^3`;
                   `b:real^3`; `a:real^3`] LRIEMANN_METRIC_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `s pow 2 * lam = &1` THEN CONV_TAC REAL_RING);;

(* ========================================================================= *)
(* The global Bochner inequality.  With                                     *)
(*   lam = pull_n$1$1,  Kg = lam (Ric(e,e) + Ric(f,f)) - lam^2 Scal / 2,     *)
(* (the numerator Rm(e,f,f,e) by CML_RIC_ALG) at every point of the plane:  *)
(*   0 <= Lap lam + 2 Kg  and  |grad lam|^2 <= lam (Lap lam + 2 Kg).        *)
(* ========================================================================= *)

let CML_LAP_LOCAL = prove
 (`!W (u:real^2->real) u' z.
     open W /\ z IN W /\ (!x. x IN W ==> u x = u' x)
     ==> cml_lap u z = cml_lap u' z /\ cml_grad2 u z = cml_grad2 u' z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i x. x IN W ==> cml_d i (u:real^2->real) x = cml_d i u' x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_D_LOCAL THEN EXISTS_TAC `W:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[cml_lap; cml_grad2] THEN ASM_SIMP_TAC[] THEN BINOP_TAC THEN
  MATCH_MP_TAC CML_D_LOCAL THEN EXISTS_TAC `W:real^2->bool` THEN ASM_SIMP_TAC[]);;

(* The chart description of the north picture near a point.                   *)

let CML_NORTH_CHART = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) U phi.
     cml_hs (top,atlas) g f G d v /\ (U,phi) IN atlas
     ==> open {z:real^2 | v(stereo2_n_inv z) IN U} /\
         smooth_map_on {z:real^2 | v(stereo2_n_inv z) IN U} (cml_wc (U,phi) v stereo2_n_inv) /\
         metric_field (IMAGE phi U) (metric_local atlas (U,phi) g) /\
         (!z. z IN {z:real^2 | v(stereo2_n_inv z) IN U}
              ==> cml_wc (U,phi) v stereo2_n_inv z IN IMAGE phi U) /\
         (!z (Q:A->real^3^3) i j.
              v(stereo2_n_inv z) IN U /\ 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
              ==> cml_pull atlas Q v stereo2_n_inv z$i$j =
                  partial_derivative i (cml_wc (U,phi) v stereo2_n_inv) z dot
                  (metric_local atlas (U,phi) Q (cml_wc (U,phi) v stereo2_n_inv z) **
                   partial_derivative j (cml_wc (U,phi) v stereo2_n_inv) z)) /\
         (!z. v(stereo2_n_inv z) IN U
              ==> cml_cov (metric_local atlas (U,phi) g) (cml_wc (U,phi) v stereo2_n_inv)
                          (partial_derivative 1 (cml_wc (U,phi) v stereo2_n_inv)) 1 z +
                  cml_cov (metric_local atlas (U,phi) g) (cml_wc (U,phi) v stereo2_n_inv)
                          (partial_derivative 2 (cml_wc (U,phi) v stereo2_n_inv)) 2 z = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cml_hs]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `v:real^3->A`;
                 `U:A->bool`; `phi:A->real^3`] CML_CHART_REGION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `metric_field (IMAGE (SND(U:A->bool,phi:A->real^3)) (FST(U:A->bool,phi)))
                               (metric_local atlas (U,phi) (g:A->real^3^3))` MP_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; REWRITE_TAC[FST; SND]];
    REPEAT STRIP_TAC THEN REWRITE_TAC[cml_wc; SND] THEN MATCH_MP_TAC CML_PULL_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[CML_XN_PROPS];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_EL_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* The global numerator and the Bochner inequality.                            *)

let cml_kg = new_definition
 `cml_kg (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (v:real^3->A) (z:real^2) =
    cml_pull atlas g v stereo2_n_inv z$1$1 *
    (cml_pull atlas (mfd_ricci_matrix atlas g) v stereo2_n_inv z$1$1 +
     cml_pull atlas (mfd_ricci_matrix atlas g) v stereo2_n_inv z$2$2) -
    cml_pull atlas g v stereo2_n_inv z$1$1 pow 2 * mfd_scalar atlas g (v(stereo2_n_inv z)) / &2`;;

let CML_BOCHNER_AT = prove
 (`!V (Gl:real^3->real^3^3) Wc (w:real^2->real^3) (lam:real^2->real) Kf z0.
     metric_field V Gl /\ open Wc /\ smooth_map_on Wc w /\ (!z. z IN Wc ==> w z IN V) /\
     (!z. z IN Wc ==> cml_cov Gl w (partial_derivative 1 w) 1 z +
                      cml_cov Gl w (partial_derivative 2 w) 2 z = vec 0) /\
     (!z. z IN Wc ==> partial_derivative 2 w z dot (Gl(w z) ** partial_derivative 2 w z) =
                      partial_derivative 1 w z dot (Gl(w z) ** partial_derivative 1 w z) /\
                      partial_derivative 1 w z dot (Gl(w z) ** partial_derivative 2 w z) = &0) /\
     (!z. z IN Wc ==> lam z = cml_lamc Gl w z) /\ Kf = cml_kk Gl w z0 /\ z0 IN Wc
     ==> &0 <= cml_lap lam z0 + &2 * Kf /\
         cml_grad2 lam z0 <= lam z0 * (cml_lap lam z0 + &2 * Kf)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Wc:real^2->bool`; `lam:real^2->real`; `cml_lamc Gl (w:real^2->real^3)`;
                 `z0:real^2`] CML_LAP_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `Gl:real^3->real^3^3`; `Wc:real^2->bool`; `w:real^2->real^3`;
                 `z0:real^2`] CML_BOCHNER) THEN
  ASM_SIMP_TAC[]);;

let CML_BOCHNER_GLOBAL = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) z0.
     cml_hs (top,atlas) g f G d v
     ==> &0 <= cml_lap (\z. cml_pull atlas g v stereo2_n_inv z$1$1) z0 +
               &2 * cml_kg atlas g v z0 /\
         cml_grad2 (\z. cml_pull atlas g v stereo2_n_inv z$1$1) z0 <=
         cml_pull atlas g v stereo2_n_inv z0$1$1 *
         (cml_lap (\z. cml_pull atlas g v stereo2_n_inv z$1$1) z0 + &2 * cml_kg atlas g v z0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                 `stereo2_n_inv z0`] CML_HS_CHART) THEN
  ASM_REWRITE_TAC[IN_SPHERE_0; CML_P_NORM] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `U:A->bool`;
                 `phi:A->real^3`] CML_NORTH_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM]) THEN
  MATCH_MP_TAC CML_BOCHNER_AT THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (phi:A->real^3) U`; `metric_local atlas (U:A->bool,phi:A->real^3) (g:A->real^3^3)`;
    `{z:real^2 | (v:real^3->A)(stereo2_n_inv z) IN U}`;
    `cml_wc (U:A->bool,phi:A->real^3) (v:real^3->A) stereo2_n_inv`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `!z i j. v(stereo2_n_inv z) IN U /\ 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
            ==> cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv z$i$j =
                partial_derivative i (cml_wc (U:A->bool,phi:A->real^3) v stereo2_n_inv) z dot
                (metric_local atlas (U,phi) g (cml_wc (U,phi) v stereo2_n_inv z) **
                 partial_derivative j (cml_wc (U,phi) v stereo2_n_inv) z)`
  (LABEL_TAC "PG") THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "PG" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(v:real^3->A)(stereo2_n_inv z) IN U`) (ARITH_RULE `1 <= 2 /\ 2 <= 2 /\ 1 <= 2 /\ 2 <= 2`))) THEN
                             MP_TAC(MATCH_MP th (CONJ (ASSUME `(v:real^3->A)(stereo2_n_inv z) IN U`) (ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 1 /\ 1 <= 2`))) THEN
                             MP_TAC(MATCH_MP th (CONJ (ASSUME `(v:real^3->A)(stereo2_n_inv z) IN U`) (ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 2 /\ 2 <= 2`)))) THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`]
                  CML_CONFORMAL_N) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN REWRITE_TAC[cml_lamc] THEN
    USE_THEN "PG" (fun th -> ACCEPT_TAC(MATCH_MP th (CONJ (ASSUME `(v:real^3->A)(stereo2_n_inv z) IN U`) (ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 1 /\ 1 <= 2`))));
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cml_hs]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  SUBGOAL_THEN
   `!(Q:A->real^3^3) i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
       ==> cml_pull atlas Q (v:real^3->A) stereo2_n_inv z0$i$j =
           partial_derivative i (cml_wc (U:A->bool,phi:A->real^3) v stereo2_n_inv) z0 dot
           (metric_local atlas (U,phi) Q (cml_wc (U,phi) v stereo2_n_inv z0) **
            partial_derivative j (cml_wc (U,phi) v stereo2_n_inv) z0)`
  (LABEL_TAC "PQ") THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cml_wc (U:A->bool,phi:A->real^3) (v:real^3->A) stereo2_n_inv z0 IN IMAGE phi U`
  ASSUME_TAC THENL [ASM_MESON_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`]
                CML_CONFORMAL_N) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z0:real^2`) THEN
  REWRITE_TAC[cml_kg; cml_kk] THEN
  USE_THEN "PQ" (fun th -> REWRITE_TAC[MATCH_MP th (ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 1 /\ 1 <= 2`);
                                       MATCH_MP th (ARITH_RULE `1 <= 2 /\ 2 <= 2 /\ 1 <= 2 /\ 2 <= 2`);
                                       MATCH_MP th (ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 2 /\ 2 <= 2`)]) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `metric_local atlas (U:A->bool,phi:A->real^3) (g:A->real^3^3)`;
                 `cml_wc (U:A->bool,phi:A->real^3) (v:real^3->A) stereo2_n_inv z0`;
                 `partial_derivative 1 (cml_wc (U:A->bool,phi:A->real^3) (v:real^3->A) stereo2_n_inv) z0`;
                 `partial_derivative 2 (cml_wc (U:A->bool,phi:A->real^3) (v:real^3->A) stereo2_n_inv) z0`;
                 `partial_derivative 1 (cml_wc (U:A->bool,phi:A->real^3) (v:real^3->A) stereo2_n_inv) z0 dot
                  (metric_local atlas (U,phi) (g:A->real^3^3) (cml_wc (U,phi) v stereo2_n_inv z0) **
                   partial_derivative 1 (cml_wc (U,phi) v stereo2_n_inv) z0)`] CML_RIC_ALG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!c w'. c IN atlas /\ w' IN IMAGE (SND c) (FST c)
           ==> metric_local atlas c (mfd_ricci_matrix atlas (g:A->real^3^3)) w' =
               (lambda i j. lricci (metric_local atlas c g) w' (basis i) (basis j))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMT_RICCI_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_local atlas (U:A->bool,phi:A->real^3) (mfd_ricci_matrix atlas (g:A->real^3^3))
      (cml_wc (U,phi) (v:real^3->A) stereo2_n_inv z0) =
    (lambda i j. lricci (metric_local atlas (U,phi) g) (cml_wc (U,phi) v stereo2_n_inv z0)
                        (basis i) (basis j))`
  SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[FST; SND]; ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP CMT_LRICCI_MATRIX
    (CONJ (ASSUME `metric_field (IMAGE (phi:A->real^3) U) (metric_local atlas (U,phi) (g:A->real^3^3))`)
          (ASSUME `cml_wc (U:A->bool,phi:A->real^3) (v:real^3->A) stereo2_n_inv z0 IN IMAGE phi U`))] THEN
  SUBGOAL_THEN
   `mfd_scalar atlas (g:A->real^3^3) ((v:real^3->A)(stereo2_n_inv z0)) =
    lscalar (metric_local atlas (U:A->bool,phi:A->real^3) g) (cml_wc (U,phi) v stereo2_n_inv z0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[cml_wc; SND] THEN MATCH_MP_TAC MFD_SCALAR_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    REFL_TAC]);;

(* ========================================================================= *)
(* A nonconstant harmonic sphere has a positive conformal factor on some    *)
(* disc (if lam vanished identically the map would be constant in both      *)
(* stereographic pictures, hence constant).                                 *)
(* ========================================================================= *)

let CML_XS_0 = prove
 (`stereo2_s_inv (vec 0) = basis 3`,
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; STEX_STEREO2_S_INV_COMPONENTS; NORM_0;
           BASIS_COMPONENT; VEC_COMPONENT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let CML_PULL_ZERO_CONST = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) X.
     cml_hs (top,atlas) g f G d v /\
     smooth_map_on (:real^2) X /\ (!z. norm(X z) = &1) /\
     (!z. cml_pull atlas g v X z$1$1 = &0 /\ cml_pull atlas g v X z$2$2 = &0)
     ==> ?c. !z. f(v(X z)) = c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_HS_TARGET) THEN
  ABBREV_TAC `u = \z. wan_rext ((f:A->real^K) o (v:real^3->A)) ((X:real^2->real^3) z)` THEN
  SUBGOAL_THEN `!z. (u:real^2->real^K) z = f((v:real^3->A)((X:real^2->real^3) z))` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_REWRITE_TAC[wan_rext; o_THM; REAL_INV_1; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (u:real^2->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    SUBGOAL_THEN `(\z. wan_rext ((f:A->real^K) o (v:real^3->A)) ((X:real^2->real^3) z)) =
                  wan_rext (f o v) o X` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; OPEN_NONZERO; SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[cml_hs]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z a. 1 <= a /\ a <= 2 ==> partial_derivative a (u:real^2->real^K) z = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                   `X:real^2->real^3`; `z:real^2`; `a:num`; `a:num`] CML_HS_PULL) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `cml_pull atlas (g:A->real^3^3) (v:real^3->A) (X:real^2->real^3) z$a$a = &0`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `a = 1 \/ a = 2` MP_TAC THENL
       [ASM_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ABBREV_TAC `q = partial_derivative a (u:real^2->real^K) z` THEN
    ABBREV_TAC `p0 = wan_rext ((f:A->real^K) o (v:real^3->A)) ((X:real^2->real^3) z)` THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN
    SUBGOAL_THEN `lam * norm(q:real^K) pow 2 <= &0` MP_TAC THENL
     [FIRST_X_ASSUM(fun th -> ASSUME_TAC th THEN
        MP_TAC(SPECL [`p0:real^K`; `q:real^K`] (ASSUME
          `!z (u:real^K). lam * norm u pow 2 <= u dot ((G:real^K->real^K^K) z ** u)`)) THEN
        REWRITE_TAC[th] THEN DISCH_THEN ACCEPT_TAC);
      ALL_TAC] THEN
    REWRITE_TAC[GSYM NORM_EQ_0] THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
    REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < lam * norm(q:real^K) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `(:real^2)`] HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT) THEN
  REWRITE_TAC[OPEN_UNIV; CONNECTED_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:real^2` THEN
    SUBGOAL_THEN `(u:real^2->real^K) differentiable at z` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    ASM_SIMP_TAC[CML_FRECHET_BASIS2; ARITH; VECTOR_MUL_RZERO; VECTOR_ADD_LID];
    ASM_MESON_TAC[]]);;

let CML_LAM_ZERO_S = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A).
     cml_hs (top,atlas) g f G d v /\
     (!p. cml_pull atlas g v stereo2_n_inv p$1$1 = &0)
     ==> !w. cml_pull atlas g v stereo2_s_inv w$1$1 = &0 /\
             cml_pull atlas g v stereo2_s_inv w$2$2 = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`]
                CML_CONFORMAL_S) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CS") (LABEL_TAC "REL")) THEN
  SUBGOAL_THEN `!w. cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_s_inv w$1$1 = &0`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `w:real^2 = vec 0` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN
      MP_TAC(ISPECL [`\w. cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_s_inv w$1$1`;
                     `vec 0:real^2`] CML_CONT_ZERO_EXT) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
        REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN MATCH_MP_TAC CML_HS_PULL_SMOOTH THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`;
                              `d:real`] THEN
        ASM_REWRITE_TAC[CML_XS_PROPS; ARITH];
        X_GEN_TAC `w':real^2` THEN DISCH_TAC THEN
        USE_THEN "REL" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~(w':real^2 = vec 0)`)]) THEN
        REWRITE_TAC[real_div; REAL_MUL_LZERO]];
      USE_THEN "REL" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~(w:real^2 = vec 0)`)]) THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  GEN_TAC THEN USE_THEN "CS" (MP_TAC o SPEC `w:real^2`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `w:real^2` o check (fun th -> concl th =
    `!w. cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_s_inv w$1$1 = &0`)) THEN
  REAL_ARITH_TAC);;

let CML_LAM_POS_SOMEWHERE = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A).
     cml_hs (top,atlas) g f G d v /\ ~(?x. !y. y IN sphere(vec 0,&1) ==> v y = x)
     ==> ?p r. &0 < r /\
               !z. z IN ball(p,r) ==> &0 < cml_pull atlas g v stereo2_n_inv z$1$1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `!p:real^2. cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv p$1$1 = &0` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_exists(rand(concl th)))) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`]
                  CML_LAM_ZERO_S) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`]
                  CML_CONFORMAL_N) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                   `stereo2_s_inv`] CML_PULL_ZERO_CONST) THEN
    ASM_REWRITE_TAC[CML_XS_PROPS] THEN DISCH_THEN(X_CHOOSE_TAC `c2:real^K`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                   `stereo2_n_inv`] CML_PULL_ZERO_CONST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CML_XN_PROPS] THEN GEN_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `stereo2_n_inv`)) (concl th) &&
        can (find_term (fun t -> t = `2`)) (concl th))) THEN
      FIRST_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th -> concl th =
        `!p:real^2. cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv p$1$1 = &0`)) THEN
      REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_TAC `c1:real^K`)] THEN
    SUBGOAL_THEN `c1:real^K = c2` ASSUME_TAC THENL
     [SUBGOAL_THEN `~(basis 1:real^2 = vec 0)` ASSUME_TAC THENL
       [SIMP_TAC[BASIS_NONZERO; DIMINDEX_2; ARITH]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `basis 1:real^2` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `c1:real^K`)) (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `cml_inv(basis 1:real^2)` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `c2:real^K`)) (concl th))) THEN
      ASM_SIMP_TAC[GSYM CML_XN_XS] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cml_hs]) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_INJECTIVE_MAP o CONJUNCT2 o
      GEN_REWRITE_RULE I [mfd_embedding] o
      check (fun th -> is_comb(concl th) && is_comb(rator(concl th)) &&
                       is_const(rator(rator(concl th))) &&
                       fst(dest_const(rator(rator(concl th)))) = "mfd_embedding")) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(basis 3:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:A->real^K)((v:real^3->A)(basis 3)) = c2` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^2` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `c2:real^K`)) (concl th))) THEN
      REWRITE_TAC[CML_XS_0];
      ALL_TAC] THEN
    EXISTS_TAC `(v:real^3->A)(basis 3)` THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(v:real^3->A) y`; `(v:real^3->A)(basis 3)`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> t = `f:A->real^K`)) (concl th) &&
                       can (find_term (fun t -> t = `topspace:(A)topology->A->bool`)) (concl th))) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_CASES_TAC `y:real^3 = basis 3` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `stereo2_n_inv(stereo2_n y) = y` ASSUME_TAC THENL
     [MATCH_MP_TAC STEX_STEREO2_N_LEFT THEN ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `stereo2_n y` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `c1:real^K`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_TAC `p:real^2` o REWRITE_RULE[NOT_FORALL_THM])] THEN
  SUBGOAL_THEN `&0 < cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv p$1$1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                   `stereo2_n_inv`; `p:real^2`] CML_PULL_SYM) THEN
    ASM_REWRITE_TAC[CML_XN_PROPS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv z$1$1))
                continuous at p` MP_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN MATCH_MP_TAC CML_HS_PULL_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[CML_XN_PROPS; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(MP_TAC o SPEC `cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv p$1$1`) THEN
  ASM_REWRITE_TAC[DIST_LIFT] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`p:real^2`; `r:real`] THEN ASM_REWRITE_TAC[IN_BALL] THEN
  X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2`) THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The area and trace densities at P(z) in terms of the planar pullbacks:   *)
(*   rho(z) density(P z) = lam(z),                                          *)
(*   rho(z) trdensity(P z) = (lam(z) = 0 => 0 | Ric(e,e) + Ric(f,f)),       *)
(* by conjugating the 3x3 Gram matrices with the orthonormal stereographic  *)
(* frame (P z, dP e1 / sqrt rho, dP e2 / sqrt rho).                          *)
(* ========================================================================= *)

let CML_E2_ORTH = prove
 (`!(R:real^3^3) M N.
     R ** transp R = mat 1
     ==> p4_e2 (R ** M ** transp R) = p4_e2 M /\
         p4_e2_pol (R ** M ** transp R) (R ** N ** transp R) = p4_e2_pol M N`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `transp(R:real^3^3) ** R = mat 1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MATRIX_LEFT_RIGHT_INVERSE] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!A:real^3^3. trace((R:real^3^3) ** A ** transp R) = trace A` ASSUME_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!A B:real^3^3. ((R:real^3^3) ** A ** transp R) ** (R ** B ** transp R) =
                               R ** (A ** B) ** transp R` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p4_e2; p4_e2_pol]);;

let CML_E2_BLOCK = prove
 (`!A B:real^3^3.
     A$1$1 = &0 /\ A$1$2 = &0 /\ A$1$3 = &0 /\ A$2$1 = &0 /\ A$3$1 = &0 /\
     B$1$1 = &0 /\ B$1$2 = &0 /\ B$1$3 = &0 /\ B$2$1 = &0 /\ B$3$1 = &0
     ==> p4_e2 A = A$2$2 * A$3$3 - A$2$3 * A$3$2 /\
         p4_e2_pol A B = A$2$2 * B$3$3 + A$3$3 * B$2$2 - A$2$3 * B$3$2 - A$3$2 * B$2$3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC[p4_e2; p4_e2_pol; trace; matrix_mul; LAMBDA_BETA; DIMINDEX_3; SUM_3; ARITH] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The stereographic frame.                                                   *)

let cml_frame = new_definition
 `cml_frame (z:real^2) =
    vector[stereo2_n_inv z;
           inv(sqrt(cml_rho z)) % bel_dP z (basis 1);
           inv(sqrt(cml_rho z)) % bel_dP z (basis 2)]:real^3^3`;;

let CML_RHO_POS_ALL = prove
 (`!z:real^2. &0 < cml_rho z`,
  GEN_TAC THEN REWRITE_TAC[cml_rho] THEN MATCH_MP_TAC REAL_LT_DIV THEN
  REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN MATCH_MP_TAC REAL_POW_LT THEN
  MP_TAC(SPEC `norm(z:real^2)` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let CML_MMT_ENTRY = prove
 (`!(A:real^N^N) j k.
     1 <= j /\ j <= dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
     ==> (A ** transp A)$j$k = A$j dot A$k`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA; dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC[transp; LAMBDA_BETA]);;

let CML_FRAME_ORTH = prove
 (`!z. cml_frame z ** transp(cml_frame z) = mat 1`,
  GEN_TAC THEN
  SUBGOAL_THEN `!h k. bel_dP z h dot bel_dP z k = cml_rho z * (h dot k)` ASSUME_TAC THENL
   [REWRITE_TAC[BEL_P_CONF; cml_rho]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(cml_rho z)) * inv(sqrt(cml_rho z)) * cml_rho z = &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_2; REAL_POW_INV] THEN
    SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; CML_RHO_POS_ALL; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
  SIMP_TAC[CML_MMT_ENTRY; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[cml_frame; VECTOR_3; DOT_LMUL; DOT_RMUL; BEL_P_TANG; BEL_P_NORM] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[BEL_P_TANG] THEN
  SIMP_TAC[DOT_BASIS; BASIS_COMPONENT; DIMINDEX_2; ARITH; mat; LAMBDA_BETA; DIMINDEX_3] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID] THEN
  UNDISCH_TAC `inv(sqrt(cml_rho z)) * inv(sqrt(cml_rho z)) * cml_rho z = &1` THEN
  REAL_ARITH_TAC);;

(* Gram matrices through the embedding: symmetric, killing the radius.       *)

let CML_GRAM_PROPS = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) (R:A->real^3^3)
    (Qa:real^K->real^K^K) y.
     cml_hs (top,atlas) g f G d v /\ (!z. transp(Qa z) = Qa z) /\
     (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
            ==> metric_local atlas c R w =
                transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                Qa(f(chart_inv c w)) **
                matrix(frechet_derivative (f o chart_inv c) (at w))) /\
     y IN sphere(vec 0,&1)
     ==> transp(p4_s2_gram atlas R v y) = p4_s2_gram atlas R v y /\
         p4_s2_gram atlas R v y ** y = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cml_hs]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  SUBGOAL_THEN `smooth_immersion_into (atlas:((A->bool)#(A->real^3))->bool) (f:A->real^K)`
  ASSUME_TAC THENL [ASM_MESON_TAC[mfd_embedding]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `R:A->real^3^3`;
                 `f:A->real^K`; `Qa:real^K->real^K^K`; `v:real^3->A`; `y:real^3`] CM_S2_GRAM) THEN
  ASM_SIMP_TAC[CML_P4_SMOOTH_C1] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; GSYM MATRIX_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `jacobian (wan_rext ((f:A->real^K) o (v:real^3->A))) (at y) ** y = vec 0`
  (fun th -> REWRITE_TAC[th; MATRIX_VECTOR_MUL_RZERO]) THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:A->real^K) o (v:real^3->A)`; `y:real^3`; `&1`] CM_REXT_JACOBIAN) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM];
    SIMP_TAC[]]);;

let CML_PULL_GRAM = prove
 (`!atlas (R:A->real^3^3) (v:real^3->A) z a b.
     1 <= a /\ a <= 2 /\ 1 <= b /\ b <= 2
     ==> cml_pull atlas R v stereo2_n_inv z$a$b =
         bel_dP z (basis a) dot (p4_s2_gram atlas R v (stereo2_n_inv z) ** bel_dP z (basis b))`,
  SIMP_TAC[cml_pull; LAMBDA_BETA; DIMINDEX_2; BEL_P_FRECHET]);;

(* The conjugated Gram matrix in the stereographic frame.                     *)

let CML_FRAME_CONJ = prove
 (`!(M:real^3^3) z.
     transp M = M /\ M ** stereo2_n_inv z = vec 0
     ==> (cml_frame z ** M ** transp(cml_frame z))$1$1 = &0 /\
         (cml_frame z ** M ** transp(cml_frame z))$1$2 = &0 /\
         (cml_frame z ** M ** transp(cml_frame z))$1$3 = &0 /\
         (cml_frame z ** M ** transp(cml_frame z))$2$1 = &0 /\
         (cml_frame z ** M ** transp(cml_frame z))$3$1 = &0 /\
         !a b. 1 <= a /\ a <= 2 /\ 1 <= b /\ b <= 2
               ==> (cml_frame z ** M ** transp(cml_frame z))$(a+1)$(b+1) =
                   inv(cml_rho z) * (bel_dP z (basis a) dot (M ** bel_dP z (basis b)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. stereo2_n_inv z dot ((M:real^3^3) ** x) = &0` ASSUME_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [GSYM(ASSUME `transp(M:real^3^3) = M`)] THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN ASM_REWRITE_TAC[DOT_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(cml_rho z)) * inv(sqrt(cml_rho z)) = inv(cml_rho z)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_2; REAL_POW_INV] THEN
    SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; CML_RHO_POS_ALL];
    ALL_TAC] THEN
  SIMP_TAC[CML_CONJ_ENTRY; DIMINDEX_3; ARITH] THEN
  ASM_REWRITE_TAC[cml_frame; VECTOR_3; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; DOT_LMUL; DOT_RMUL;
                  MATRIX_VECTOR_MUL_RMUL; REAL_MUL_RZERO] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a = 1 \/ a = 2) /\ (b = 1 \/ b = 2)` MP_TAC THENL
   [ASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  SIMP_TAC[CML_CONJ_ENTRY; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[cml_frame; VECTOR_3; DOT_LMUL; DOT_RMUL; MATRIX_VECTOR_MUL_RMUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[]);;

let CML_E2_PLANE = prove
 (`!(M:real^3^3) (N:real^3^3) z.
     transp M = M /\ M ** stereo2_n_inv z = vec 0 /\
     transp N = N /\ N ** stereo2_n_inv z = vec 0
     ==> p4_e2 M =
         inv(cml_rho z) pow 2 *
         ((bel_dP z (basis 1) dot (M ** bel_dP z (basis 1))) *
          (bel_dP z (basis 2) dot (M ** bel_dP z (basis 2))) -
          (bel_dP z (basis 1) dot (M ** bel_dP z (basis 2))) *
          (bel_dP z (basis 2) dot (M ** bel_dP z (basis 1)))) /\
         p4_e2_pol M N =
         inv(cml_rho z) pow 2 *
         ((bel_dP z (basis 1) dot (M ** bel_dP z (basis 1))) *
          (bel_dP z (basis 2) dot (N ** bel_dP z (basis 2))) +
          (bel_dP z (basis 2) dot (M ** bel_dP z (basis 2))) *
          (bel_dP z (basis 1) dot (N ** bel_dP z (basis 1))) -
          (bel_dP z (basis 1) dot (M ** bel_dP z (basis 2))) *
          (bel_dP z (basis 2) dot (N ** bel_dP z (basis 1))) -
          (bel_dP z (basis 2) dot (M ** bel_dP z (basis 1))) *
          (bel_dP z (basis 1) dot (N ** bel_dP z (basis 2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cml_frame z`; `M:real^3^3`; `N:real^3^3`] CML_E2_ORTH) THEN
  REWRITE_TAC[CML_FRAME_ORTH] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL [`M:real^3^3`; `z:real^2`] CML_FRAME_CONJ) THEN
  MP_TAC(ISPECL [`N:real^3^3`; `z:real^2`] CML_FRAME_CONJ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N")))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M")))))) THEN
  MP_TAC(ISPECL [`cml_frame z ** (M:real^3^3) ** transp(cml_frame z)`;
                 `cml_frame z ** (N:real^3^3) ** transp(cml_frame z)`] CML_E2_BLOCK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  USE_THEN "M" (fun thm -> USE_THEN "N" (fun thn ->
    MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)
      (REWRITE_RULE[ARITH] (CONJ (SPECL [`1`; `1`] thm) (CONJ (SPECL [`2`; `2`] thm)
        (CONJ (SPECL [`1`; `2`] thm) (CONJ (SPECL [`2`; `1`] thm)
        (CONJ (SPECL [`1`; `1`] thn) (CONJ (SPECL [`2`; `2`] thn)
        (CONJ (SPECL [`1`; `2`] thn) (SPECL [`2`; `1`] thn)))))))))))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING);;

let CML_DENSITY_PLANE = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) z.
     cml_hs (top,atlas) g f G d v
     ==> cml_rho z * p4_s2_density atlas g v (stereo2_n_inv z) =
         cml_pull atlas g v stereo2_n_inv z$1$1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_HS_TARGET) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `g:A->real^3^3`;
                 `G:real^K->real^K^K`; `stereo2_n_inv z`] CML_GRAM_PROPS) THEN
  ASM_REWRITE_TAC[IN_SPHERE_0; CML_P_NORM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p4_s2_gram atlas (g:A->real^3^3) (v:real^3->A) (stereo2_n_inv z)`;
                 `p4_s2_gram atlas (g:A->real^3^3) (v:real^3->A) (stereo2_n_inv z)`; `z:real^2`]
                CML_E2_PLANE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SIMP_TAC[GSYM CML_PULL_GRAM; ARITH] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`]
                CML_CONFORMAL_N) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                 `stereo2_n_inv`; `z:real^2`] CML_PULL_SYM) THEN
  ASM_REWRITE_TAC[CML_XN_PROPS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[p4_s2_density] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `inv(cml_rho z) pow 2 *
    (cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv z$2$2 *
     cml_pull atlas g v stereo2_n_inv z$2$2 - &0 * &0) =
    (inv(cml_rho z) * cml_pull atlas g v stereo2_n_inv z$2$2) pow 2`
  SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(cml_rho z) * cml_pull atlas (g:A->real^3^3) (v:real^3->A)
                                                    stereo2_n_inv z$2$2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; CML_RHO_POS_ALL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; CML_RHO_POS_ALL;
               REAL_MUL_LID]);;

let CML_TRDENSITY_PLANE = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) z.
     cml_hs (top,atlas) g f G d v
     ==> cml_rho z * p4_s2_trdensity atlas g (mfd_ricci_matrix atlas g) v (stereo2_n_inv z) =
         if cml_pull atlas g v stereo2_n_inv z$1$1 = &0 then &0
         else cml_pull atlas (mfd_ricci_matrix atlas g) v stereo2_n_inv z$1$1 +
              cml_pull atlas (mfd_ricci_matrix atlas g) v stereo2_n_inv z$2$2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_HS_TARGET) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cml_hs]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] CM_AMBIENT_RICCI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Q:real^K->real^K^K` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `g:A->real^3^3`;
                 `G:real^K->real^K^K`; `stereo2_n_inv z`] CML_GRAM_PROPS) THEN
  ASM_REWRITE_TAC[IN_SPHERE_0; CML_P_NORM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                 `mfd_ricci_matrix atlas (g:A->real^3^3)`; `Q:real^K->real^K^K`;
                 `stereo2_n_inv z`] CML_GRAM_PROPS) THEN
  ASM_REWRITE_TAC[IN_SPHERE_0; CML_P_NORM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p4_s2_gram atlas (g:A->real^3^3) (v:real^3->A) (stereo2_n_inv z)`;
                 `p4_s2_gram atlas (mfd_ricci_matrix atlas (g:A->real^3^3)) (v:real^3->A)
                                (stereo2_n_inv z)`; `z:real^2`]
                CML_E2_PLANE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[GSYM CML_PULL_GRAM; ARITH] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`]
                CML_CONFORMAL_N) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                 `stereo2_n_inv`; `z:real^2`] CML_PULL_SYM) THEN
  ASM_REWRITE_TAC[CML_XN_PROPS] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[p4_s2_trdensity] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `lz = cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv z$2$2` THEN
  ABBREV_TAC `ir = inv(cml_rho z)` THEN
  SUBGOAL_THEN `&0 < ir` ASSUME_TAC THENL
   [EXPAND_TAC "ir" THEN SIMP_TAC[REAL_LT_INV_EQ; CML_RHO_POS_ALL]; ALL_TAC] THEN
  SUBGOAL_THEN `cml_rho z * ir = &1` ASSUME_TAC THENL
   [EXPAND_TAC "ir" THEN SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; CML_RHO_POS_ALL]; ALL_TAC] THEN
  SUBGOAL_THEN `ir pow 2 * (lz * lz - &0 * &0) = (ir * lz) pow 2` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_CASES_TAC `lz = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_POW_ZERO; ARITH_EQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_POW_EQ_0; REAL_ENTIRE; ARITH_EQ] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  SUBGOAL_THEN `&0 <= ir * lz` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT] THEN
  UNDISCH_TAC `cml_rho z * ir = &1` THEN UNDISCH_TAC `~(lz = &0)` THEN
  UNDISCH_TAC `&0 < ir` THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* Regularity and bounds of the radial extensions of the area density, the  *)
(* trace density and the scalar curvature along the sphere (continuity,     *)
(* measurability, boundedness), so that their radial extensions are         *)
(* integrable on the unit ball.                                             *)
(* ========================================================================= *)

let CML_RADIAL_ABSINT = prove
 (`!h:real^3->real.
     (\x. lift(h(inv(norm x) % x))) measurable_on (:real^3) /\
     (?B. !y. y IN sphere(vec 0,&1) ==> abs(h y) <= B)
     ==> (\x. lift(h(inv(norm x) % x))) absolutely_integrable_on ball(vec 0,&1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `B:real`)) THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real^3. lift(max B (abs((h:real^3->real)(vec 0))))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_BALL];
    REWRITE_TAC[INTEGRABLE_ON_CONST; MEASURABLE_BALL];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
    ASM_CASES_TAC `x:real^3 = vec 0` THENL
     [ASM_REWRITE_TAC[NORM_0; REAL_INV_0; VECTOR_MUL_LZERO] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= max b c`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE]]]);;

let CML_HS_REXT = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A).
     cml_hs (top,atlas) g f G d v
     ==> wan_rext (f o v) continuous_on {x:real^3 | ~(x = vec 0)} /\
         (!x. ~(x = vec 0) ==> wan_rext (f o v) differentiable at x) /\
         (!i x. ~(x = vec 0)
                ==> partial_derivative i (wan_rext (f o v)) x =
                    jacobian (wan_rext (f o v)) (at x) ** basis i) /\
         (!i. (\x. partial_derivative i (wan_rext (f o v)) x) continuous_on
              {x:real^3 | ~(x = vec 0)})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`; `wan_rext ((f:A->real^K) o (v:real^3->A))`]
                CMT_C1_FACTS) THEN
  REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [cml_hs]) THEN
  SIMP_TAC[smooth_map_on]);;

let CML_NRM_CONT = prove
 (`(\x:real^3. inv(norm x) % x) continuous_on {x | ~(x = vec 0)} /\
   IMAGE (\x:real^3. inv(norm x) % x) {x | ~(x = vec 0)} SUBSET {x | ~(x = vec 0)}`,
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0] THEN MESON_TAC[]]);;

let CML_RAD_PD_CONT = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) k.
     cml_hs (top,atlas) g f G d v
     ==> (\x. partial_derivative k (wan_rext (f o v)) (inv(norm x) % x)) continuous_on
         {x:real^3 | ~(x = vec 0)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_HS_REXT) THEN
  SUBGOAL_THEN `(\x:real^3. partial_derivative k (wan_rext ((f:A->real^K) o (v:real^3->A)))
                              (inv(norm x) % x)) =
                (\x. partial_derivative k (wan_rext (f o v)) x) o (\x. inv(norm x) % x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CML_NRM_CONT] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
  ASM_REWRITE_TAC[CML_NRM_CONT]);;

let CML_RAD_GRAM_CONT = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) (Qa:real^K->real^K^K) i j.
     cml_hs (top,atlas) g f G d v /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Qa) /\
     1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
     ==> (\x. lift((transp(jacobian (wan_rext (f o v)) (at (inv(norm x) % x))) **
                    Qa(f(v(inv(norm x) % x))) **
                    jacobian (wan_rext (f o v)) (at (inv(norm x) % x)))$i$j))
         continuous_on {x:real^3 | ~(x = vec 0)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_HS_REXT) THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\x:real^3. lift(partial_derivative i (wan_rext ((f:A->real^K) o (v:real^3->A)))
                                (inv(norm x) % x) dot
                              ((Qa:real^K->real^K^K)(wan_rext (f o v) x) **
                               partial_derivative j (wan_rext (f o v)) (inv(norm x) % x)))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(inv(norm x) % x:real^3 = vec 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0]; ALL_TAC] THEN
    ASM_SIMP_TAC[CMT_GRAM_ENTRY; DIMINDEX_3] THEN REWRITE_TAC[wan_rext; o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^3 | ~(x = vec 0)}`; `Qa:real^K->real^K^K`;
                 `wan_rext ((f:A->real^K) o (v:real^3->A))`;
                 `\x:real^3. partial_derivative i (wan_rext ((f:A->real^K) o (v:real^3->A)))
                                                (inv(norm x) % x)`;
                 `\x:real^3. partial_derivative j (wan_rext ((f:A->real^K) o (v:real^3->A)))
                                                (inv(norm x) % x)`] CMT_CONT_QUAD) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
  CONJ_TAC THEN MATCH_MP_TAC CML_RAD_PD_CONT THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `G:real^K->real^K^K`; `d:real`] THEN
  ASM_REWRITE_TAC[]);;

(* The Gram matrices along the radial extension.                              *)

let CML_GRAM_RAD_EQ = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) (R:A->real^3^3)
    (Qa:real^K->real^K^K) x.
     cml_hs (top,atlas) g f G d v /\
     (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
            ==> metric_local atlas c R w =
                transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                Qa(f(chart_inv c w)) **
                matrix(frechet_derivative (f o chart_inv c) (at w))) /\
     ~(x = vec 0)
     ==> p4_s2_gram atlas R v (inv(norm x) % x) =
         transp(jacobian (wan_rext (f o v)) (at (inv(norm x) % x))) **
         Qa(f(v(inv(norm x) % x))) **
         jacobian (wan_rext (f o v)) (at (inv(norm x) % x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cml_hs]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  MATCH_MP_TAC CM_S2_GRAM THEN EXISTS_TAC `top:A topology` THEN
  ASM_SIMP_TAC[CML_P4_SMOOTH_C1; P4_RADIAL_SPHERE] THEN ASM_MESON_TAC[mfd_embedding]);;

let CML_DENS_RAD_CONT = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A).
     cml_hs (top,atlas) g f G d v
     ==> (\x. lift(p4_s2_density atlas g v (inv(norm x) % x))) continuous_on
         {x:real^3 | ~(x = vec 0)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_HS_TARGET) THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\x:real^3. lift(sqrt(p4_e2
     (transp(jacobian (wan_rext ((f:A->real^K) o (v:real^3->A))) (at (inv(norm x) % x))) **
      (G:real^K->real^K^K)(f(v(inv(norm x) % x))) **
      jacobian (wan_rext (f o v)) (at (inv(norm x) % x)))))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[p4_s2_density] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CML_GRAM_RAD_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^3^3`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [o_DEF] THEN BETA_TAC THEN
  MATCH_MP_TAC CMT_CONT_E2 THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_RAD_GRAM_CONT THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `G:real^K->real^K^K`; `d:real`] THEN
  ASM_REWRITE_TAC[]);;

(* The trace density: measurable and bounded on the sphere.                   *)

let CML_TRDENS_RAD = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A).
     cml_hs (top,atlas) g f G d v
     ==> (\x. lift(p4_s2_trdensity atlas g (mfd_ricci_matrix atlas g) v (inv(norm x) % x)))
         measurable_on (:real^3) /\
         ?C. !y. y IN sphere(vec 0,&1)
                 ==> abs(p4_s2_trdensity atlas g (mfd_ricci_matrix atlas g) v y) <= C`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_HS_TARGET) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cml_hs]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] CM_AMBIENT_RICCI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Q:real^K->real^K^K` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `J = \x:real^3. jacobian (wan_rext ((f:A->real^K) o (v:real^3->A))) (at x)` THEN
  SUBGOAL_THEN
   `!x. ~(x = vec 0)
        ==> p4_s2_trdensity atlas (g:A->real^3^3) (mfd_ricci_matrix atlas g) (v:real^3->A)
                            (inv(norm x) % x) =
            (if p4_e2(transp((J:real^3->real^3^K)(inv(norm x) % x)) ** (G:real^K->real^K^K)((f:A->real^K)((v:real^3->A)(inv(norm x) % x))) **
                      J(inv(norm x) % x)) = &0 then &0
             else p4_e2_pol (transp((J:real^3->real^3^K)(inv(norm x) % x)) ** G(f(v(inv(norm x) % x))) **
                             J(inv(norm x) % x))
                            (transp((J:real^3->real^3^K)(inv(norm x) % x)) **
                             (Q:real^K->real^K^K)((f:A->real^K)((v:real^3->A)(inv(norm x) % x))) ** J(inv(norm x) % x)) /
                  sqrt(p4_e2(transp((J:real^3->real^3^K)(inv(norm x) % x)) ** G(f(v(inv(norm x) % x))) **
                             J(inv(norm x) % x))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "J" THEN REWRITE_TAC[p4_s2_trdensity] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `g:A->real^3^3`;
                   `G:real^K->real^K^K`; `x:real^3`] CML_GRAM_RAD_EQ) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                   `mfd_ricci_matrix atlas (g:A->real^3^3)`; `Q:real^K->real^K^K`; `x:real^3`]
                  CML_GRAM_RAD_EQ) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE) THEN
    EXISTS_TAC `\x:real^3. lift(if p4_e2(transp((J:real^3->real^3^K)(inv(norm x) % x)) **
                                          (G:real^K->real^K^K)((f:A->real^K)((v:real^3->A)(inv(norm x) % x))) **
                                          J(inv(norm x) % x)) = &0 then &0
                               else p4_e2_pol (transp((J:real^3->real^3^K)(inv(norm x) % x)) **
                                               G(f(v(inv(norm x) % x))) ** J(inv(norm x) % x))
                                              (transp((J:real^3->real^3^K)(inv(norm x) % x)) **
                                               (Q:real^K->real^K^K)((f:A->real^K)((v:real^3->A)(inv(norm x) % x))) **
                                               J(inv(norm x) % x)) /
                                    sqrt(p4_e2(transp((J:real^3->real^3^K)(inv(norm x) % x)) **
                                               G(f(v(inv(norm x) % x))) **
                                               J(inv(norm x) % x))))` THEN
    EXISTS_TAC `{vec 0:real^3}` THEN REWRITE_TAC[NEGLIGIBLE_SING] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING] THEN
      DISCH_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\x:real^3. transp((J:real^3->real^3^K)(inv(norm x) % x)) **
                               (G:real^K->real^K^K)((f:A->real^K)((v:real^3->A)(inv(norm x) % x))) **
                               J(inv(norm x) % x)`;
                   `\x:real^3. transp((J:real^3->real^3^K)(inv(norm x) % x)) **
                               (Q:real^K->real^K^K)((f:A->real^K)((v:real^3->A)(inv(norm x) % x))) **
                               J(inv(norm x) % x)`] CMT_TRDENS_MEASURABLE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXPAND_TAC "J" THEN BETA_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CML_RAD_GRAM_CONT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\x:real^3. p4_s2_density atlas (g:A->real^3^3) (v:real^3->A) (inv(norm x) % x)`
               CMT_CONT_SPHERE_BOUND) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN MATCH_MP_TAC CML_DENS_RAD_CONT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Bd:real`)] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target] o
    check (fun th -> is_comb(concl th) && is_comb(rator(concl th)) &&
                     is_comb(rator(rator(concl th))) &&
                     is_const(rator(rator(rator(concl th)))) &&
                     fst(dest_const(rator(rator(rator(concl th))))) = "cm_target")) THEN
  MP_TAC(ISPECL [`Q:real^K->real^K^K`; `IMAGE (f:A->real^K) (topspace top)`] CMT_QUAD_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CONTINUOUS_ON_SUBSET; SUBSET_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    DISCH_THEN(X_CHOOSE_THEN `MQ:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `&2 * MQ / lam * max Bd (&0)` THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0) /\ inv(norm y) % y = y` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    SIMP_TAC[REAL_INV_1; VECTOR_MUL_LID; GSYM NORM_EQ_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `p4_s2_trdensity:((A->bool)#(A->real^3)->bool)->(A->real^3^3)->(A->real^3^3)->(real^3->A)->real^3->real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * MQ / lam *
              sqrt(p4_e2(transp((J:real^3->real^3^K)(y:real^3)) ** (G:real^K->real^K^K)(f((v:real^3->A) y)) ** J y))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMT_TRDENS_BOUND THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `Bd:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[p4_s2_density] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `g:A->real^3^3`;
                 `G:real^K->real^K^K`; `y:real^3`] CML_GRAM_RAD_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "J" THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* The scalar curvature along the radial extension.                           *)

let CML_SCAL_RAD_CONT = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A).
     cml_hs (top,atlas) g f G d v
     ==> (\x. lift(mfd_scalar atlas g (v(inv(norm x) % x)))) continuous_on
         {x:real^3 | ~(x = vec 0)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cml_hs]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p4_s2_smooth]) THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_NONZERO; IN_ELIM_THM] THEN
  X_GEN_TAC `x0:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                 `inv(norm x0) % x0:real^3`] CML_HS_CHART) THEN
  ASM_SIMP_TAC[P4_RADIAL_SPHERE] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `C = {x:real^3 | ~(x = vec 0) /\ (v:real^3->A)(inv(norm x) % x) IN U}` THEN
  SUBGOAL_THEN `open(C:real^3->bool) /\ (x0:real^3) IN C` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `v:real^3->A`;
                   `(U:A->bool,phi:A->real^3)`] P4_RADIAL_CHART_OPEN) THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^3) U) (metric_local atlas (U,phi) (g:A->real^3^3))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `metric_field (IMAGE (SND(U:A->bool,phi:A->real^3)) (FST(U:A->bool,phi)))
                               (metric_local atlas (U,phi) (g:A->real^3^3))` MP_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; REWRITE_TAC[FST; SND]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
  EXISTS_TAC `(\y. lift(lscalar (metric_local atlas (U:A->bool,phi:A->real^3) (g:A->real^3^3)) y)) o
              (\x:real^3. (phi:A->real^3)((v:real^3->A)(inv(norm x) % x)))` THEN
  SUBGOAL_THEN `?e. &0 < e /\ ball(x0:real^3,e) SUBSET C` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN C` MP_TAC THENL
     [UNDISCH_TAC `ball(x0:real^3,e) SUBSET C` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "C" THEN REWRITE_TAC[IN_ELIM_THM; o_THM] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MFD_SCALAR_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `C:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `smooth_map_on:(real^3->bool)->(real^3->real^3)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[FST; SND];
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN
    ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN UNDISCH_TAC `(x0:real^3) IN C` THEN EXPAND_TAC "C" THEN
    SIMP_TAC[IN_ELIM_THM]]);;

(* ========================================================================= *)
(* Assembly.  The planar core CML_CORE_POS applied to lam = pull_n$1$1, K = *)
(* cml_kg; the area and the Ricci trace integral are plane integrals        *)
(* (CML_S2_TRANSFER with the density identities), and Ric(e,e) + Ric(f,f) = *)
(* K / lam + lam Scal / 2.                                                  *)
(* ========================================================================= *)

let CML_SCAL_PLANE = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A).
     cml_hs (top,atlas) g f G d v
     ==> (\z. lift(mfd_scalar atlas g (v(stereo2_n_inv z)))) continuous_on (:real^2) /\
         ?BS. !z. abs(mfd_scalar atlas g (v(stereo2_n_inv z))) <= BS`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!z. mfd_scalar atlas (g:A->real^3^3) ((v:real^3->A)(stereo2_n_inv z)) =
                    (\x. mfd_scalar atlas g (v(inv(norm x) % x))) (stereo2_n_inv z)`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[CML_P_NORM; REAL_INV_1; VECTOR_MUL_LID]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(\z. lift((\x. mfd_scalar atlas (g:A->real^3^3) ((v:real^3->A)(inv(norm x) % x)))
                             (stereo2_n_inv z))) =
                  (\x. lift(mfd_scalar atlas g (v(inv(norm x) % x)))) o stereo2_n_inv`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[CML_XN_PROPS]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CML_SCAL_RAD_CONT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; GSYM NORM_EQ_0; CML_P_NORM] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\x:real^3. mfd_scalar atlas (g:A->real^3^3) ((v:real^3->A)(inv(norm x) % x))`
               CMT_CONT_SPHERE_BOUND) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN MATCH_MP_TAC CML_SCAL_RAD_CONT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `BS:real`) THEN EXISTS_TAC `BS:real` THEN
  GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_SPHERE_0; CML_P_NORM]);;

let CML_KG_CONT_FORM = prove
 (`!s (a:real^2->real) b c e.
     (\z. lift(a z)) continuous_on s /\ (\z. lift(b z)) continuous_on s /\
     (\z. lift(c z)) continuous_on s /\ (\z. lift(e z)) continuous_on s
     ==> (\z. lift(a z * (b z + c z) - a z pow 2 * e z / &2)) continuous_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift((a:real^2->real) z * (b z + c z) - a z pow 2 * e z / &2)) =
                (\z. a z % (lift(b z) + lift(c z)) - (inv(&2) * a z pow 2) % lift(e z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; GSYM LIFT_ADD; GSYM LIFT_SUB; LIFT_EQ] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  ASM_REWRITE_TAC[o_DEF] THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN ASM_REWRITE_TAC[]]);;

let CML_LEMMA122_HS = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d (v:real^3->A) U r0.
     cml_hs (top,atlas) g f G d v /\ ~(?x. !y. y IN sphere(vec 0,&1) ==> v y = x) /\
     (!y. y IN sphere(vec 0,&1) ==> v y IN U) /\ (!x. x IN U ==> r0 <= mfd_scalar atlas g x)
     ==> &4 * pi + r0 / &2 * p4_s2_area atlas g v <=
         p4_s2_trint atlas g (mfd_ricci_matrix atlas g) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `lam = \z. cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_n_inv z$1$1` THEN
  ABBREV_TAC `lamq = \z. cml_pull atlas (g:A->real^3^3) (v:real^3->A) stereo2_s_inv z$1$1` THEN
  ABBREV_TAC `Tr = \z. if (lam:real^2->real) z = &0 then &0
                      else cml_pull atlas (mfd_ricci_matrix atlas (g:A->real^3^3)) (v:real^3->A)
                                    stereo2_n_inv z$1$1 +
                           cml_pull atlas (mfd_ricci_matrix atlas g) v stereo2_n_inv z$2$2` THEN
  (* the area and the trace integral in the plane *)
  MP_TAC(ISPEC `p4_s2_density atlas (g:A->real^3^3) (v:real^3->A)` CML_S2_TRANSFER) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC CML_RADIAL_ABSINT THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMT_CONT_NONZERO_MEASURABLE THEN MATCH_MP_TAC CML_DENS_RAD_CONT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `\x:real^3. p4_s2_density atlas (g:A->real^3^3) (v:real^3->A) (inv(norm x) % x)`
                   CMT_CONT_SPHERE_BOUND) THEN
      ANTS_TAC THENL
       [BETA_TAC THEN MATCH_MP_TAC CML_DENS_RAD_CONT THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[] THEN MESON_TAC[P4_RADIAL_FIX]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. cml_rho z * p4_s2_density atlas (g:A->real^3^3) (v:real^3->A) (stereo2_n_inv z) =
                    (lam:real^2->real) z` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "lam" THEN REWRITE_TAC[] THEN MATCH_MP_TAC CML_DENSITY_PLANE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM p4_s2_area] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `p4_s2_trdensity atlas (g:A->real^3^3) (mfd_ricci_matrix atlas g) (v:real^3->A)`
               CML_S2_TRANSFER) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC CML_RADIAL_ABSINT THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`] CML_TRDENS_RAD) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. cml_rho z * p4_s2_trdensity atlas (g:A->real^3^3) (mfd_ricci_matrix atlas g)
                                   (v:real^3->A) (stereo2_n_inv z) = (Tr:real^2->real) z`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "Tr" THEN EXPAND_TAC "lam" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CML_TRDENSITY_PLANE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM p4_s2_trint] THEN STRIP_TAC THEN
  (* scalar curvature along the map *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`] CML_SCAL_PLANE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `BS:real`)) THEN
  (* the products lam * S *)
  SUBGOAL_THEN `(\z. lift(mfd_scalar atlas (g:A->real^3^3) ((v:real^3->A)(stereo2_n_inv z)) *
                          (lam:real^2->real) z))
                absolutely_integrable_on (:real^2)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^1 y:real^1. drop x % y`;
                   `\z. lift(mfd_scalar atlas (g:A->real^3^3) ((v:real^3->A)(stereo2_n_inv z)))`;
                   `\z. lift((lam:real^2->real) z)`; `(:real^2)`]
                  ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
    REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP; GSYM LIFT_CMUL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV; NORM_LIFT] THEN
      EXISTS_TAC `abs BS + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* a disc where lam > 0 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`]
                CML_LAM_POS_SOMEWHERE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
  (* the hypotheses of the planar core, one by one *)
  SUBGOAL_THEN
   `smooth_map_on (:real^2) (\z. lift((lam:real^2->real) z)) /\ (!z. &0 <= lam z) /\
    smooth_map_on (:real^2) (\z. lift((lamq:real^2->real) z)) /\ (!z. &0 <= lamq z) /\
    (!z. ~(z = vec 0) ==> lam z = lamq(cml_inv z) / norm z pow 4)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN EXPAND_TAC "lamq" THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CML_HS_PULL_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
      ASM_REWRITE_TAC[CML_XN_PROPS; ARITH];
      X_GEN_TAC `z:real^2` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                     `stereo2_n_inv`; `z:real^2`] CML_PULL_SYM) THEN
      ASM_REWRITE_TAC[CML_XN_PROPS] THEN SIMP_TAC[];
      MATCH_MP_TAC CML_HS_PULL_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
      ASM_REWRITE_TAC[CML_XS_PROPS; ARITH];
      X_GEN_TAC `z:real^2` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                     `stereo2_s_inv`; `z:real^2`] CML_PULL_SYM) THEN
      ASM_REWRITE_TAC[CML_XS_PROPS] THEN SIMP_TAC[];
      X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CML_INV_NORM) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`]
                    CML_CONFORMAL_S) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `cml_inv z` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `&0 < norm(z:real^2)` MP_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(cml_kg atlas (g:A->real^3^3) (v:real^3->A) z)) continuous_on (:real^2)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cml_hs]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] CM_AMBIENT_RICCI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Q:real^K->real^K^K` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[cml_kg] THEN MATCH_MP_TAC CML_KG_CONT_FORM THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC CML_HS_PULL_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`] THEN
      ASM_REWRITE_TAC[CML_XN_PROPS; ARITH];
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC CML_PULL_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^3^3`; `f:A->real^K`;
                            `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`] THEN
      ASM_REWRITE_TAC[CML_XN_PROPS; ARITH];
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC CML_PULL_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^3^3`; `f:A->real^K`;
                            `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`] THEN
      ASM_REWRITE_TAC[CML_XN_PROPS; ARITH];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. &0 <= cml_lap (lam:real^2->real) z + &2 * cml_kg atlas (g:A->real^3^3) (v:real^3->A) z /\
        cml_lap lam z = (cml_lap lam z + &2 * cml_kg atlas g v z) - &2 * cml_kg atlas g v z /\
        cml_grad2 lam z <= lam z * (cml_lap lam z + &2 * cml_kg atlas g v z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN EXPAND_TAC "lam" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`; `z:real^2`]
                  CML_BOCHNER_GLOBAL) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. (lam:real^2->real) z = &0
                    ==> cml_kg atlas (g:A->real^3^3) (v:real^3->A) z = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN EXPAND_TAC "lam" THEN REWRITE_TAC[cml_kg] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN ball(p:real^2,r) ==> &0 < (lam:real^2->real) z` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* K / lam = Tr - lam S / 2 *)
  SUBGOAL_THEN
   `!z. (if (lam:real^2->real) z = &0 then &0
         else cml_kg atlas (g:A->real^3^3) (v:real^3->A) z / lam z) =
        (Tr:real^2->real) z - inv(&2) * (mfd_scalar atlas g (v(stereo2_n_inv z)) * lam z)`
  (LABEL_TAC "PW") THENL
   [X_GEN_TAC `z:real^2` THEN EXPAND_TAC "Tr" THEN EXPAND_TAC "lam" THEN
    REWRITE_TAC[cml_kg] THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(if (lam:real^2->real) z = &0 then &0
              else cml_kg atlas (g:A->real^3^3) (v:real^3->A) z / lam z)) =
    (\z. lift((Tr:real^2->real) z) -
         inv(&2) % lift(mfd_scalar atlas g (v(stereo2_n_inv z)) * lam z))`
  (LABEL_TAC "FE") THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; GSYM LIFT_SUB] THEN X_GEN_TAC `z:real^2` THEN
    USE_THEN "PW" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(if (lam:real^2->real) z = &0 then &0
              else cml_kg atlas (g:A->real^3^3) (v:real^3->A) z / lam z))
    absolutely_integrable_on (:real^2)`
  ASSUME_TAC THENL
   [USE_THEN "FE" SUBST1_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* r0 Area <= int S lam *)
  SUBGOAL_THEN
   `r0 * drop(integral (:real^2) (\z. lift((lam:real^2->real) z))) <=
    drop(integral (:real^2) (\z. lift(mfd_scalar atlas (g:A->real^3^3)
                                        ((v:real^3->A)(stereo2_n_inv z)) * lam z)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\z. lift((lam:real^2->real) z)) integrable_on (:real^2) /\
      (\z. lift(mfd_scalar atlas (g:A->real^3^3) ((v:real^3->A)(stereo2_n_inv z)) * lam z))
      integrable_on (:real^2)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\z. lift((lam:real^2->real) z)`; `r0:real`; `(:real^2)`] INTEGRAL_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
    REWRITE_TAC[DROP_CMUL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN REWRITE_TAC[IN_UNIV; DROP_CMUL; LIFT_DROP] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^2` THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `r0:real`)) (concl th))) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_SPHERE_0; CML_P_NORM]];
    ALL_TAC] THEN
  (* the planar core *)
  MP_TAC(ISPECL [`lam:real^2->real`; `lamq:real^2->real`;
                 `cml_kg atlas (g:A->real^3^3) (v:real^3->A)`;
                 `\z. cml_lap (lam:real^2->real) z +
                      &2 * cml_kg atlas (g:A->real^3^3) (v:real^3->A) z`;
                 `p:real^2`; `r:real`] CML_CORE_POS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  USE_THEN "FE" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `integral (:real^2) (\z. lift((Tr:real^2->real) z) -
                            inv(&2) % lift(mfd_scalar atlas (g:A->real^3^3)
                                             ((v:real^3->A)(stereo2_n_inv z)) *
                                           (lam:real^2->real) z)) =
    integral (:real^2) (\z. lift(Tr z)) -
    inv(&2) % integral (:real^2) (\z. lift(mfd_scalar atlas g (v(stereo2_n_inv z)) * lam z))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\z. lift((Tr:real^2->real) z)`;
                   `\z. inv(&2) % lift(mfd_scalar atlas (g:A->real^3^3)
                                         ((v:real^3->A)(stereo2_n_inv z)) *
                                       (lam:real^2->real) z)`;
                   `(:real^2)`] INTEGRAL_SUB) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THENL
       [ASM_REWRITE_TAC[]; MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_CMUL THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DROP_SUB; DROP_CMUL] THEN
  SUBGOAL_THEN `p4_s2_area atlas (g:A->real^3^3) (v:real^3->A) =
                drop(integral (:real^2) (\z. lift((lam:real^2->real) z)))` SUBST1_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p4_s2_trint atlas (g:A->real^3^3) (mfd_ricci_matrix atlas g) (v:real^3->A) =
                drop(integral (:real^2) (\z. lift((Tr:real^2->real) z)))` SUBST1_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  UNDISCH_TAC
   `r0 * drop(integral (:real^2) (\z. lift((lam:real^2->real) z))) <=
    drop(integral (:real^2) (\z. lift(mfd_scalar atlas (g:A->real^3^3)
                                        ((v:real^3->A)(stereo2_n_inv z)) * lam z)))` THEN
  REAL_ARITH_TAC);;

(* The headline: CM Lemma 1.22 for harmonic spheres in a component U.        *)
(* Embed the manifold in real^7 (CM_EMB_EXISTS); a harmonic sphere in U is   *)
(* one in topspace top, hence G-harmonic (CM_SHARMONIC_EQ), i.e. cml_hs.     *)

let CML_HARMONIC_SPHERE = prove
 (`CM_HARMONIC_SPHERE_STATEMENT (:A)`,
  REWRITE_TAC[CM_HARMONIC_SPHERE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `U:A->bool`; `v:real^3->A`; `r0:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(topspace (top:A topology) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] NONEMPTY_CONNECTED_COMPONENTS_OF) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`] (INST_TYPE [`:7`,`:K`] CM_EMB_EXISTS)) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; DIMINDEX_CONV `dimindex(:7)`] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real^7` (X_CHOOSE_THEN `G:real^7->real^7^7`
    (X_CHOOSE_TAC `d:real`))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p4_harmonic_sphere]) THEN
  SUBGOAL_THEN `!y. y IN sphere(vec 0,&1) ==> (v:real^3->A) y IN topspace top`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p4_harmonic_sphere (top,atlas) (g:A->real^3^3) (topspace top) (v:real^3->A)`
  MP_TAC THENL [ASM_REWRITE_TAC[p4_harmonic_sphere]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real^7`; `G:real^7->real^7^7`; `d:real`; `v:real^3->A`]
                CM_SHARMONIC_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[cm_sharmonic] THEN STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:7`,`:K`] CML_LEMMA122_HS) THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^7`; `G:real^7->real^7^7`; `d:real`;
                        `U:A->bool`] THEN
  ASM_REWRITE_TAC[cml_hs]);;

let CM_CHAIN_CM_LEMMA122 = prove
 (`!aa:A->bool. CM_CHAIN_CM_LEMMA122_STATEMENT aa`,
  REWRITE_TAC[CM_CHAIN_CM_LEMMA122_STATEMENT; CML_HARMONIC_SPHERE]);;

let CM_CHAIN_CM_LEMMA122_A = prove
 (`CM_CHAIN_CM_LEMMA122_STATEMENT (:A)`,
  REWRITE_TAC[CM_CHAIN_CM_LEMMA122]);;


(* ========================================================================= *)
(* Local Riemannian geometry on open subsets of real^N: the Christoffel      *)
(* symbols and the Levi-Civita connection, the curvature tensor and its      *)
(* symmetries, Ricci and scalar curvature, their naturality under pullback   *)
(* by diffeomorphisms, and a convention test (the round sphere has sectional *)
(* curvature 1).                                                             *)
(* ========================================================================= *)

needs "src/poincare_statement.ml";;
needs "src/ns_smooth_elem.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Definitions: local Riemannian geometry on open subsets of real^N.         *)
(* A metric is a matrix field G : real^N -> real^N^N; vector fields are maps *)
(* real^N -> real^N.  Conventions (Morgan-Tian, Chow-Knopf):                 *)
(*   R(u,v)w = nabla_u nabla_v w - nabla_v nabla_u w - nabla_[u,v] w,        *)
(*   Ric(v,w) = trace of (u |-> R(u,v)w),  R = trace_G Ric,                 *)
(*   sectional curvature K(u,v) = <R(u,v)v,u> / (|u|^2 |v|^2 - <u,v>^2).     *)
(* ========================================================================= *)

(* Derivative of a matrix field in the direction w. *)

let mderiv = new_definition
 `mderiv (G:real^N->real^N^N) (y:real^N) (w:real^N) =
    (matrify:real^(N,N)finite_prod->real^N^N)
    (frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                        (at y) w)`;;

(* Christoffel symbols: G(y) christoffel(u,v) has k-th component            *)
(* 1/2 (d_u g(v,e_k) + d_v g(u,e_k) - d_k g(u,v)).                          *)

let christoffel = new_definition
 `christoffel (G:real^N->real^N^N) (y:real^N) (u:real^N) (v:real^N) =
    matrix_inv(G y) **
    ((lambda k. inv(&2) *
                ((mderiv G y u ** v)$k + (mderiv G y v ** u)$k -
                 u dot (mderiv G y (basis k) ** v))):real^N)`;;

(* Covariant derivative of the vector field Y along X. *)

let lcovd = new_definition
 `lcovd (G:real^N->real^N^N) (X:real^N->real^N) (Y:real^N->real^N) (y:real^N) =
    frechet_derivative Y (at y) (X y) + christoffel G y (X y) (Y y)`;;

(* Lie bracket of vector fields. *)

let lbracket = new_definition
 `lbracket (X:real^N->real^N) (Y:real^N->real^N) (y:real^N) =
    frechet_derivative Y (at y) (X y) - frechet_derivative X (at y) (Y y)`;;

(* The (1,3) curvature tensor at y, computed with constant vector fields. *)

let lriemann = new_definition
 `lriemann (G:real^N->real^N^N) (y:real^N) (u:real^N) (v:real^N) (w:real^N) =
    frechet_derivative (\z. christoffel G z v w) (at y) u -
    frechet_derivative (\z. christoffel G z u w) (at y) v +
    christoffel G y u (christoffel G y v w) -
    christoffel G y v (christoffel G y u w)`;;

let lricci = new_definition
 `lricci (G:real^N->real^N^N) (y:real^N) (v:real^N) (w:real^N) =
    sum(1..dimindex(:N)) (\k. (lriemann G y (basis k) v w)$k)`;;

let lscalar = new_definition
 `lscalar (G:real^N->real^N^N) (y:real^N) =
    sum(1..dimindex(:N))
     (\i. sum(1..dimindex(:N))
            (\j. matrix_inv(G y)$i$j * lricci G y (basis i) (basis j)))`;;

let lsectional = new_definition
 `lsectional (G:real^N->real^N^N) (y:real^N) (u:real^N) (v:real^N) =
    (u dot (G y ** lriemann G y u v v)) /
    ((u dot (G y ** u)) * (v dot (G y ** v)) - (u dot (G y ** v)) pow 2)`;;

(* Metric fields on an open set: smooth, symmetric, positive definite. *)

let metric_field = new_definition
 `metric_field (U:real^N->bool) (G:real^N->real^N^N) <=>
    open U /\
    smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
    !y. y IN U ==> transp(G y) = G y /\
                   !v. ~(v = vec 0) ==> &0 < v dot (G y ** v)`;;

(* Pullback of a matrix field by a map h. *)

let mpullback = new_definition
 `mpullback (h:real^N->real^N) (G:real^N->real^N^N) (y:real^N) =
    transp(matrix(frechet_derivative h (at y))) ** G(h y) **
    matrix(frechet_derivative h (at y))`;;

(* Second derivative of a map h at y in directions u, v. *)

let dd2 = new_definition
 `dd2 (h:real^N->real^N) (y:real^N) (u:real^N) (v:real^N) =
    frechet_derivative (\z. frechet_derivative h (at z) v) (at y) u`;;


(* ========================================================================= *)
(* Generic calculus lemmas (derivatives of matrix-vector products, families  *)
(* of linear and bilinear maps, second derivatives).                         *)
(* ========================================================================= *)

let LRG_HAS_DERIVATIVE_IMP_LINEAR = prove
 (`!(f:real^M->real^N) f' net. (f has_derivative f') net ==> linear f'`,
  SIMP_TAC[has_derivative]);;

let LRG_FRECHET_DERIVATIVE_EQ_OPEN = prove
 (`!(f:real^M->real^N) g s y.
        open s /\ y IN s /\ (!z. z IN s ==> f z = g z)
        ==> frechet_derivative f (at y) = frechet_derivative g (at y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_LOCAL THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_MESON_TAC[DIST_SYM]);;

let LRG_HAS_DERIVATIVE_UNIQUE_OPEN = prove
 (`!(f:real^M->real^N) g f' g' s y.
        open s /\ y IN s /\ (!z. z IN s ==> f z = g z) /\
        (f has_derivative f') (at y) /\ (g has_derivative g') (at y)
        ==> f' = g'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC [`g:real^M->real^N`; `y:real^M`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `s:real^M->bool`] THEN
  ASM_REWRITE_TAC[]);;

let LRG_HAS_DERIVATIVE_COMPONENT = prove
 (`!(a:real^M->real^N) a' y i.
        (a has_derivative a') (at y)
        ==> ((\z. lift(a z$i)) has_derivative (\u. lift(a' u$i))) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^M->real^N`; `\x:real^N. lift(x$i)`;
                 `a':real^M->real^N`; `\x:real^N. lift(x$i)`; `y:real^M`]
         DIFF_CHAIN_AT) THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_LIFT_COMPONENT; o_DEF]);;

let LRG_BILINEAR_MATRIFY_MUL = prove
 (`bilinear (\(m:real^(N,N)finite_prod) (v:real^N). (matrify m:real^N^N) ** v)`,
  REWRITE_TAC[bilinear; linear; MATRIFY_ADD; MATRIFY_CMUL;
              MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_RMUL]);;

let LRG_HAS_DERIVATIVE_MATVEC = prove
 (`!(A:real^M->real^N^N) A' (b:real^M->real^N) b' y.
        ((vectorize o A) has_derivative A') (at y) /\
        (b has_derivative b') (at y)
        ==> ((\z. A z ** b z) has_derivative
             (\w. matrify(A' w) ** b y + A y ** b' w)) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(m:real^(N,N)finite_prod) (v:real^N). (matrify m:real^N^N) ** v`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (A:real^M->real^N^N)`;
                 `b:real^M->real^N`;
                 `A':real^M->real^(N,N)finite_prod`; `b':real^M->real^N`;
                 `y:real^M`] HAS_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; o_THM; MATRIFY_VECTORIZE] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATCH_ACCEPT_TAC VECTOR_ADD_SYM);;

let LRG_HAS_DERIVATIVE_DOT_MATVEC = prove
 (`!(A:real^M->real^N^N) A' (a:real^M->real^N) a' b b' y.
        ((vectorize o A) has_derivative A') (at y) /\
        (a has_derivative a') (at y) /\ (b has_derivative b') (at y)
        ==> ((\z. lift(a z dot (A z ** b z))) has_derivative
             (\w. lift(a' w dot (A y ** b y) +
                       a y dot (matrify(A' w) ** b y + A y ** b' w)))) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(x:real^N) (y:real^N). lift(x dot y)`; `a:real^M->real^N`;
                 `\z. (A:real^M->real^N^N) z ** (b:real^M->real^N) z`;
                 `a':real^M->real^N`;
                 `\w. matrify((A':real^M->real^(N,N)finite_prod) w) **
                      (b:real^M->real^N) y + (A:real^M->real^N^N) y **
                      (b':real^M->real^N) w`;
                 `y:real^M`] HAS_DERIVATIVE_BILINEAR_AT) THEN
  ASM_SIMP_TAC[BILINEAR_DOT; LRG_HAS_DERIVATIVE_MATVEC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; LIFT_ADD] THEN GEN_TAC THEN
  MATCH_ACCEPT_TAC VECTOR_ADD_SYM);;

(* Families of linear maps L z depending on a parameter z. *)

let LRG_HAS_DERIVATIVE_LINFAM_CONST = prove
 (`!(L:real^M->real^N->real^P) s y c.
        open s /\ y IN s /\ (!z. z IN s ==> linear (L z)) /\
        (!i. 1 <= i /\ i <= dimindex(:N)
             ==> (\z. L z (basis i)) differentiable at y)
        ==> ((\z. L z c) has_derivative
             (\u. vsum (1..dimindex(:N))
                    (\i. c$i % frechet_derivative (\z. L z (basis i)) (at y) u)))
            (at y)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC
   [`\z. vsum (1..dimindex(:N))
          (\i. (c:real^N)$i % (L:real^M->real^N->real^P) z (basis i))`;
    `s:real^M->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LINEAR_APPLY_EXPAND THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_SIMP_TAC[]);;

let LRG_DIFFERENTIABLE_LINFAM_CONST = prove
 (`!(L:real^M->real^N->real^P) s y c.
        open s /\ y IN s /\ (!z. z IN s ==> linear (L z)) /\
        (!i. 1 <= i /\ i <= dimindex(:N)
             ==> (\z. L z (basis i)) differentiable at y)
        ==> (\z. L z c) differentiable at y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:real^M->real^N->real^P`; `s:real^M->bool`; `y:real^M`;
                 `c:real^N`] LRG_HAS_DERIVATIVE_LINFAM_CONST) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[differentiable]);;

let LRG_HAS_DERIVATIVE_LINFAM = prove
 (`!(L:real^M->real^N->real^P) (a:real^M->real^N) a' s y.
        open s /\ y IN s /\ (!z. z IN s ==> linear (L z)) /\
        (!i. 1 <= i /\ i <= dimindex(:N)
             ==> (\z. L z (basis i)) differentiable at y) /\
        (a has_derivative a') (at y)
        ==> ((\z. L z (a z)) has_derivative
             (\u. L y (a' u) + frechet_derivative (\z. L z (a y)) (at y) u))
            (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear((L:real^M->real^N->real^P) y)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\u. (L:real^M->real^N->real^P) y ((a':real^M->real^N) u) +
         frechet_derivative (\z. L z ((a:real^M->real^N) y)) (at y) u) =
    (\u. vsum (1..dimindex(:N))
           (\i. a y$i % frechet_derivative (\z. L z (basis i)) (at y) u +
                a' u$i % L y (basis i)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `u:real^M` THEN
    SIMP_TAC[VSUM_ADD; FINITE_NUMSEG] THEN
    MP_TAC(ISPECL [`L:real^M->real^N->real^P`; `s:real^M->bool`; `y:real^M`;
                   `(a:real^M->real^N) y`] LRG_HAS_DERIVATIVE_LINFAM_CONST) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    BETA_TAC THEN
    MP_TAC(ISPEC `(a':real^M->real^N) u`
      (MATCH_MP LINEAR_APPLY_EXPAND
         (ASSUME `linear((L:real^M->real^N->real^P) y)`))) THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC VECTOR_ADD_SYM;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC
   [`\z. vsum (1..dimindex(:N))
          (\i. (a:real^M->real^N) z$i % (L:real^M->real^N->real^P) z (basis i))`;
    `s:real^M->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LINEAR_APPLY_EXPAND THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. (a:real^M->real^N) z$i`; `\u. (a':real^M->real^N) u$i`;
                 `\z. (L:real^M->real^N->real^P) z (basis i)`;
                 `frechet_derivative (\z. (L:real^M->real^N->real^P) z (basis i))
                                     (at y)`;
                 `y:real^M`] HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LRG_HAS_DERIVATIVE_COMPONENT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[]]);;

(* Families of bilinear maps B z depending on a parameter z. *)

let LRG_HAS_DERIVATIVE_BILFAM = prove
 (`!(B:real^M->real^N->real^Q->real^P) (a:real^M->real^N) a'
    (b:real^M->real^Q) b' s y.
        open s /\ y IN s /\ (!z. z IN s ==> bilinear (B z)) /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:Q)
               ==> (\z. B z (basis i) (basis j)) differentiable at y) /\
        (a has_derivative a') (at y) /\ (b has_derivative b') (at y)
        ==> ((\z. B z (a z) (b z)) has_derivative
             (\u. B y (a' u) (b y) + B y (a y) (b' u) +
                  frechet_derivative (\z. B z (a y) (b y)) (at y) u)) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(!z (x:real^N). z IN s
        ==> linear ((B:real^M->real^N->real^Q->real^P) z x)) /\
    (!z (w:real^Q). z IN s
        ==> linear (\x. (B:real^M->real^N->real^Q->real^P) z x w))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M`) THEN
    ASM_REWRITE_TAC[bilinear; ETA_AX] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:Q)
        ==> (\z. (B:real^M->real^N->real^Q->real^P) z
                   ((a:real^M->real^N) z) (basis j)) differentiable at y`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\z v. (B:real^M->real^N->real^Q->real^P) z v (basis j)`;
                   `a:real^M->real^N`; `a':real^M->real^N`;
                   `s:real^M->bool`; `y:real^M`] LRG_HAS_DERIVATIVE_LINFAM) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[]; MESON_TAC[differentiable]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. (B:real^M->real^N->real^Q->real^P) z ((a:real^M->real^N) z)`;
                 `b:real^M->real^Q`; `b':real^M->real^Q`;
                 `s:real^M->bool`; `y:real^M`] LRG_HAS_DERIVATIVE_LINFAM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z v. (B:real^M->real^N->real^Q->real^P) z v
                          ((b:real^M->real^Q) y)`;
                 `a:real^M->real^N`; `a':real^M->real^N`;
                 `s:real^M->bool`; `y:real^M`] LRG_HAS_DERIVATIVE_LINFAM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC LRG_DIFFERENTIABLE_LINFAM_CONST THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC);;

let LRG_DIFFERENTIABLE_BILFAM_CONST = prove
 (`!(B:real^M->real^N->real^Q->real^P) s y c d.
        open s /\ y IN s /\ (!z. z IN s ==> bilinear (B z)) /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:Q)
               ==> (\z. B z (basis i) (basis j)) differentiable at y)
        ==> (\z. B z c d) differentiable at y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`B:real^M->real^N->real^Q->real^P`;
                 `(\z. c):real^M->real^N`; `(\u. vec 0):real^M->real^N`;
                 `(\z. d):real^M->real^Q`; `(\u. vec 0):real^M->real^Q`;
                 `s:real^M->bool`; `y:real^M`] LRG_HAS_DERIVATIVE_BILFAM) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN MESON_TAC[differentiable]);;

(* Symmetry of second derivatives of smooth maps (from SCHWARZ_C2). *)

let LRG_LINEAR_VSUM_COMPONENTS = prove
 (`!(X:num->real^P). linear (\c:real^N. vsum (1..dimindex(:N)) (\i. c$i % X i))`,
  REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VECTOR_ADD_RDISTRIB; GSYM VECTOR_MUL_ASSOC] THEN
  SIMP_TAC[VSUM_ADD; FINITE_NUMSEG; VSUM_LMUL]);;

let LRG_SMOOTH_FRECHET_DIFFERENTIABLE = prove
 (`!s (f:real^M->real^P) y v.
        open s /\ smooth_map_on s f /\ y IN s
        ==> f differentiable at y /\
            (\z. frechet_derivative f (at z) v) differentiable at y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `s:real^M->bool` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]);;

let LRG_SECOND_DERIVATIVE_SYM = prove
 (`!s (f:real^M->real^P) y u v.
        open s /\ smooth_map_on s f /\ y IN s
        ==> frechet_derivative (\z. frechet_derivative f (at z) v) (at y) u =
            frechet_derivative (\z. frechet_derivative f (at z) u) (at y) v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `bilinear (\u v. frechet_derivative
                      (\z. frechet_derivative (f:real^M->real^P) (at z) v) (at y) u)`
  ASSUME_TAC THENL
   [REWRITE_TAC[bilinear] THEN CONJ_TAC THEN X_GEN_TAC `w:real^M` THENL
     [SUBGOAL_THEN
       `!c. frechet_derivative (\z. frechet_derivative (f:real^M->real^P) (at z) c)
                               (at y) =
            (\u. vsum (1..dimindex(:M))
                   (\i. c$i % frechet_derivative
                                (\z. frechet_derivative f (at z) (basis i))
                                (at y) u))`
      (fun th -> ONCE_REWRITE_TAC[th]) THENL
       [GEN_TAC THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
        MP_TAC(ISPECL [`\z. frechet_derivative (f:real^M->real^P) (at z)`;
                       `s:real^M->bool`; `y:real^M`; `c:real^M`]
               LRG_HAS_DERIVATIVE_LINFAM_CONST) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
          MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
          MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real^P`; `z:real^M`;
                         `c:real^M`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
          ASM_SIMP_TAC[];
          X_GEN_TAC `i:num` THEN DISCH_TAC THEN
          MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real^P`; `y:real^M`;
                         `basis i:real^M`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
          ASM_SIMP_TAC[]];
        BETA_TAC THEN REWRITE_TAC[LRG_LINEAR_VSUM_COMPONENTS]];
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real^P`; `y:real^M`;
                     `w:real^M`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\u v. frechet_derivative
             (\z. frechet_derivative (f:real^M->real^P) (at z) v) (at y) u) =
    (\u v. frechet_derivative
             (\z. frechet_derivative (f:real^M->real^P) (at z) u) (at y) v)`
  (fun th -> MP_TAC(AP_THM (AP_THM th `u:real^M`) `v:real^M`) THEN
             REWRITE_TAC[]) THEN
  MATCH_MP_TAC BILINEAR_EQ_STDBASIS THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM BILINEAR_SWAP] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCHWARZ_C2 THEN
    EXISTS_TAC `s:real^M->bool` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[smooth_map_on]) THEN
    ASM_REWRITE_TAC[IN_NUMSEG]]);;

(* ========================================================================= *)
(* Smoothness of matrix fields (entries, products, transposes, inverses,     *)
(* Jacobian matrices, derivatives).                                          *)
(* ========================================================================= *)

let LRG_LINEAR_MATRIFY_ENTRY = prove
 (`!i j. linear (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j))`,
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT;
              MATRIX_CMUL_COMPONENT; LIFT_ADD; LIFT_CMUL]);;

let LRG_SMOOTH_VECTORIZE = prove
 (`!s (A:real^M->real^N^N).
        open s
        ==> (smooth_map_on s (vectorize o A) <=>
             !i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                   ==> smooth_map_on s (\z. lift(A z$i$j)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(\z. lift((A:real^M->real^N^N) z$i$j)) =
      (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) o
      ((vectorize:real^N^N->real^(N,N)finite_prod) o A)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY];
    DISCH_TAC THEN
    GEN_REWRITE_TAC I
     [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE (ASSUME `open(s:real^M->bool)`)] THEN
    REWRITE_TAC[DIMINDEX_FINITE_PROD; o_THM] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[VECTORIZE_COMPONENT] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `~(dimindex(:N) = 0)` ASSUME_TAC THENL
     [REWRITE_TAC[DIMINDEX_NONZERO]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `1 <= 1 + a`;
                 ARITH_RULE `1 + a <= n <=> a < n`; RDIV_LT_EQ] THEN
    ASM_ARITH_TAC]);;

let LRG_BILINEAR_MATRIX_MUL = prove
 (`bilinear (\(m1:real^(N,N)finite_prod) (m2:real^(N,N)finite_prod).
               (vectorize:real^N^N->real^(N,N)finite_prod)
                 ((matrify m1:real^N^N) ** (matrify m2:real^N^N)))`,
  REWRITE_TAC[bilinear; linear; MATRIFY_ADD; MATRIFY_CMUL;
              MATRIX_ADD_LDISTRIB; MATRIX_ADD_RDISTRIB;
              MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; VECTORIZE_ADD; VECTORIZE_CMUL]);;

let LRG_SMOOTH_MATMUL = prove
 (`!s (A:real^M->real^N^N) (B:real^M->real^N^N).
        open s /\ smooth_map_on s (vectorize o A) /\
        smooth_map_on s (vectorize o B)
        ==> smooth_map_on s (vectorize o (\z. A z ** B z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`s:real^M->bool`;
    `\(m1:real^(N,N)finite_prod) (m2:real^(N,N)finite_prod).
        (vectorize:real^N^N->real^(N,N)finite_prod)
          ((matrify m1:real^N^N) ** (matrify m2:real^N^N))`;
    `(vectorize:real^N^N->real^(N,N)finite_prod) o (A:real^M->real^N^N)`;
    `(vectorize:real^N^N->real^(N,N)finite_prod) o (B:real^M->real^N^N)`]
   SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[LRG_BILINEAR_MATRIX_MUL; o_THM; MATRIFY_VECTORIZE] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let LRG_SMOOTH_MATVEC = prove
 (`!s (A:real^M->real^N^N) (b:real^M->real^N).
        open s /\ smooth_map_on s (vectorize o A) /\ smooth_map_on s b
        ==> smooth_map_on s (\z. A z ** b z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`s:real^M->bool`;
    `\(m:real^(N,N)finite_prod) (v:real^N). (matrify m:real^N^N) ** v`;
    `(vectorize:real^N^N->real^(N,N)finite_prod) o (A:real^M->real^N^N)`;
    `b:real^M->real^N`]
   SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; o_THM; MATRIFY_VECTORIZE]);;

let LRG_SMOOTH_TRANSP = prove
 (`!s (A:real^M->real^N^N).
        open s /\ smooth_map_on s (vectorize o A)
        ==> smooth_map_on s (vectorize o (\z. transp(A z)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod) o (\z. transp((A:real^M->real^N^N) z)) =
    ((vectorize:real^N^N->real^(N,N)finite_prod) o transp o matrify) o
    ((vectorize:real^N^N->real^(N,N)finite_prod) o A)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LINEAR_TRANSP]);;

let LRG_SMOOTH_MATRIX_INV = prove
 (`!s (A:real^M->real^N^N).
        open s /\ smooth_map_on s (vectorize o A) /\
        (!z. z IN s ==> ~(det(A z) = &0))
        ==> smooth_map_on s (vectorize o (\z. matrix_inv(A z)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> smooth_map_on s (\z. lift((A:real^M->real^N^N) z$i$j))`
  MP_TAC THENL [ASM_MESON_TAC[LRG_SMOOTH_VECTORIZE]; ALL_TAC] THEN
  ASM_SIMP_TAC[LRG_SMOOTH_VECTORIZE] THEN REWRITE_TAC[smooth_map_on] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MATRIX_INV_ENTRY_OPEN THEN
  ASM_SIMP_TAC[]);;

let LRG_SMOOTH_JACOBIAN = prove
 (`!s (h:real^N->real^N).
        open s /\ smooth_map_on s h
        ==> smooth_map_on s
              (vectorize o (\z. matrix(frechet_derivative h (at z))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LRG_SMOOTH_VECTORIZE] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_COMPONENT] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]);;

let LRG_SMOOTH_MDERIV = prove
 (`!s (G:real^N->real^N^N) w.
        open s /\ smooth_map_on s (vectorize o G)
        ==> smooth_map_on s (vectorize o (\z. mderiv G z w))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mderiv; o_DEF; VECTORIZE_MATRIFY] THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE; o_DEF]);;

(* ========================================================================= *)
(* Metric fields: basic facts, symmetry of the derivative of the metric, the *)
(* Christoffel symbols (dot form, symmetry, bilinearity, locality,           *)
(* smoothness).                                                              *)
(* ========================================================================= *)

let METRIC_FIELD_SUBSET = prove
 (`!U V (G:real^N->real^N^N).
        metric_field U G /\ open V /\ V SUBSET U ==> metric_field V G`,
  REWRITE_TAC[metric_field] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[SMOOTH_MAP_ON_SUBSET; SUBSET]);;

let LRG_METRIC_FIELD_DIFF = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> (vectorize o G) differentiable at y /\
            ((vectorize o G) has_derivative
             frechet_derivative (vectorize o G) (at y)) (at y)`,
  REWRITE_TAC[metric_field; GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE]);;

let LRG_METRIC_SYM = prove
 (`!U (G:real^N->real^N^N) y a b.
        metric_field U G /\ y IN U
        ==> a dot (G y ** b) = b dot (G y ** a)`,
  REWRITE_TAC[metric_field] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM DOT_MATRIX_TRANSP_LMUL] THEN
  ASM_SIMP_TAC[] THEN MATCH_ACCEPT_TAC DOT_SYM);;

let LRG_METRIC_POS = prove
 (`!U (G:real^N->real^N^N) y v.
        metric_field U G /\ y IN U /\ ~(v = vec 0)
        ==> &0 < v dot (G y ** v)`,
  REWRITE_TAC[metric_field] THEN MESON_TAC[]);;

let LRG_METRIC_INVERTIBLE = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> invertible(G y) /\ ~(det(G y) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM INVERTIBLE_DET_NZ] THEN
  REWRITE_TAC[INVERTIBLE_DET_NZ; GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `x:real^N`] LRG_METRIC_POS) THEN
  ASM_REWRITE_TAC[DOT_RZERO; REAL_LT_REFL]);;

let LRG_METRIC_DOT_EQ = prove
 (`!U (G:real^N->real^N^N) y c1 c2.
        metric_field U G /\ y IN U /\
        (!w. w dot (G y ** c1) = w dot (G y ** c2))
        ==> c1 = c2`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c1 - c2:real^N`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `a:real = b ==> a - b = &0`)) THEN
  REWRITE_TAC[GSYM DOT_RSUB; GSYM MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `c1 - c2:real^N`] LRG_METRIC_POS) THEN
  ASM_REWRITE_TAC[REAL_LT_REFL]);;

(* The derivative of the metric. *)

let LRG_MDERIV_LINEAR = prove
 (`!(G:real^N->real^N^N) y.
        (vectorize o G) differentiable at y
        ==> (!a b. mderiv G y (a + b) = mderiv G y a + mderiv G y b) /\
            (!c a. mderiv G y (c % a) = c %% mderiv G y a)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  SIMP_TAC[mderiv; LINEAR_ADD; LINEAR_CMUL; MATRIFY_ADD; MATRIFY_CMUL]);;

let LRG_HAS_DERIVATIVE_GDOT = prove
 (`!(G:real^N->real^N^N) y a b.
        (vectorize o G) differentiable at y
        ==> ((\z. lift(a dot (G z ** b))) has_derivative
             (\w. lift(a dot (mderiv G y w ** b)))) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`;
                 `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                      (G:real^N->real^N^N)) (at y)`;
                 `(\z. a):real^N->real^N`; `(\w. vec 0):real^N->real^N`;
                 `(\z. b):real^N->real^N`; `(\w. vec 0):real^N->real^N`;
                 `y:real^N`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST; GSYM FRECHET_DERIVATIVE_WORKS] THEN
  REWRITE_TAC[mderiv; DOT_LZERO; MATRIX_VECTOR_MUL_RZERO; VECTOR_ADD_RID;
              REAL_ADD_LID]);;

let LRG_MDERIV_DOT_LINEAR = prove
 (`!(G:real^N->real^N^N) y a b.
        (vectorize o G) differentiable at y
        ==> linear (\w. lift(a dot (mderiv G y w ** b)))`,
  MESON_TAC[LRG_HAS_DERIVATIVE_GDOT; LRG_HAS_DERIVATIVE_IMP_LINEAR]);;

let LRG_MDERIV_SYM = prove
 (`!U (G:real^N->real^N^N) y w a b.
        metric_field U G /\ y IN U
        ==> a dot (mderiv G y w ** b) = b dot (mderiv G y w ** a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(vectorize o (G:real^N->real^N^N)) differentiable at y`
  ASSUME_TAC THENL [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. lift(a dot ((G:real^N->real^N^N) z ** b))`;
    `\z. lift(b dot ((G:real^N->real^N^N) z ** a))`;
    `\w. lift(a dot (mderiv (G:real^N->real^N^N) y w ** b))`;
    `\w. lift(b dot (mderiv (G:real^N->real^N^N) y w ** a))`;
    `U:real^N->bool`; `y:real^N`] LRG_HAS_DERIVATIVE_UNIQUE_OPEN) THEN
  ASM_SIMP_TAC[LRG_HAS_DERIVATIVE_GDOT] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LRG_METRIC_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o C AP_THM `w:real^N`) THEN REWRITE_TAC[LIFT_EQ]]);;

let LRG_LINEAR_DROP_EXPAND = prove
 (`!(L:real^N->real^1) w.
        linear L
        ==> sum (1..dimindex(:N)) (\k. w$k * drop(L(basis k))) = drop(L w)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
                         [MATCH_MP LINEAR_APPLY_EXPAND th]) THEN
  REWRITE_TAC[DROP_VSUM; o_DEF; DROP_CMUL]);;

(* The Christoffel symbols. *)

let LRG_CHRISTOFFEL_DOT = prove
 (`!U (G:real^N->real^N^N) y u v w.
        metric_field U G /\ y IN U
        ==> w dot (G y ** christoffel G y u v) =
            inv(&2) * (w dot (mderiv G y u ** v) + w dot (mderiv G y v ** u) -
                       u dot (mderiv G y w ** v))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `(vectorize o (G:real^N->real^N^N)) differentiable at y`
  ASSUME_TAC THENL [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF]; ALL_TAC] THEN
  REWRITE_TAC[christoffel] THEN
  SUBGOAL_THEN
   `(lambda k. inv(&2) * ((mderiv (G:real^N->real^N^N) y u ** v)$k +
                          (mderiv G y v ** u)$k -
                          u dot (mderiv G y (basis k) ** v))):real^N =
    inv(&2) % (mderiv G y u ** v + mderiv G y v ** u -
               (lambda k. u dot (mderiv G y (basis k) ** v)))`
  SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT;
             VECTOR_SUB_COMPONENT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
  REWRITE_TAC[DOT_RMUL; DOT_RADD; DOT_RSUB] THEN
  SUBGOAL_THEN
   `w dot ((lambda k. u dot (mderiv (G:real^N->real^N^N) y (basis k) ** v)):real^N) =
    u dot (mderiv G y w ** v)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\w. lift(u dot (mderiv (G:real^N->real^N^N) y w ** v))`;
                   `w:real^N`] LRG_LINEAR_DROP_EXPAND) THEN
    ASM_SIMP_TAC[LRG_MDERIV_DOT_LINEAR; LIFT_DROP] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC LAND_CONV [dot] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA];
    REWRITE_TAC[]]);;

let CHRISTOFFEL_SYM = prove
 (`!U (G:real^N->real^N^N) y u v.
        metric_field U G /\ y IN U
        ==> christoffel G y u v = christoffel G y v u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_METRIC_DOT_EQ THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `u:real^N`; `v:real^N`; `w:real^N`] LRG_CHRISTOFFEL_DOT) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `v:real^N`; `u:real^N`; `w:real^N`] LRG_CHRISTOFFEL_DOT) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `w:real^N`; `u:real^N`; `v:real^N`] LRG_MDERIV_SYM) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CHRISTOFFEL_BILINEAR = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U ==> bilinear (christoffel G y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(vectorize o (G:real^N->real^N^N)) differentiable at y`
  ASSUME_TAC THENL [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_CHRISTOFFEL_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[bilinear; linear] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LRG_METRIC_DOT_EQ THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                  DOT_RADD; DOT_RMUL] THEN
  ASM_SIMP_TAC[LRG_MDERIV_LINEAR; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
               MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_LMUL;
               MATRIX_VECTOR_MUL_RMUL; DOT_RADD; DOT_LADD; DOT_RMUL; DOT_LMUL] THEN
  REAL_ARITH_TAC);;

let CHRISTOFFEL_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 s y u v.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
        ==> christoffel G1 y u v = christoffel G2 y u v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!w. mderiv (G1:real^N->real^N^N) y w = mderiv G2 y w`
  ASSUME_TAC THENL
   [REWRITE_TAC[mderiv] THEN GEN_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[o_THM];
    ASM_SIMP_TAC[christoffel]]);;

let LRG_CHRISTOFFEL_SMOOTH = prove
 (`!U (G:real^N->real^N^N) u v.
        metric_field U G ==> smooth_map_on U (\z. christoffel G z u v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  REWRITE_TAC[christoffel] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[LRG_METRIC_INVERTIBLE];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I
   [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE (ASSUME `open(U:real^N->bool)`)] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_ADD; LIFT_SUB] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT; SMOOTH_MAP_ON_DOT_OPEN;
               LRG_SMOOTH_MATVEC; LRG_SMOOTH_MDERIV; SMOOTH_MAP_ON_CONST]);;

(* ========================================================================= *)
(* The Levi-Civita connection: metric compatibility and torsion freeness.    *)
(* ========================================================================= *)

let LRG_CHRISTOFFEL_DIFF = prove
 (`!U (G:real^N->real^N^N) y u v.
        metric_field U G /\ y IN U
        ==> (\z. christoffel G z u v) differentiable at y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `U:real^N->bool` THEN
  ASM_MESON_TAC[LRG_CHRISTOFFEL_SMOOTH; metric_field]);;

(* Metric compatibility at a point, for constant vectors. *)

let LRG_MDERIV_CHRISTOFFEL = prove
 (`!U (G:real^N->real^N^N) y a c b.
        metric_field U G /\ y IN U
        ==> a dot (mderiv G y c ** b) =
            b dot (G y ** christoffel G y c a) +
            a dot (G y ** christoffel G y c b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `c:real^N`; `a:real^N`; `b:real^N`] LRG_CHRISTOFFEL_DOT) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `c:real^N`; `b:real^N`; `a:real^N`] LRG_CHRISTOFFEL_DOT) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `c:real^N`; `a:real^N`; `b:real^N`] LRG_MDERIV_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `a:real^N`; `b:real^N`; `c:real^N`] LRG_MDERIV_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `b:real^N`; `a:real^N`; `c:real^N`] LRG_MDERIV_SYM) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let LCOVD_METRIC = prove
 (`!U (G:real^N->real^N^N) X Y Z y.
        metric_field U G /\ smooth_map_on U X /\ smooth_map_on U Y /\
        smooth_map_on U Z /\ y IN U
        ==> frechet_derivative (\z. lift(Y z dot (G z ** Z z))) (at y) (X y) =
            lift(lcovd G X Y y dot (G y ** Z y) +
                 Y y dot (G y ** lcovd G X Z y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`;
                 `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                      (G:real^N->real^N^N)) (at y)`;
                 `Y:real^N->real^N`; `frechet_derivative (Y:real^N->real^N) (at y)`;
                 `Z:real^N->real^N`; `frechet_derivative (Z:real^N->real^N) (at y)`;
                 `y:real^N`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF];
      ASM_MESON_TAC[SMOOTH_MAP_ON_HAS_DERIVATIVE];
      ASM_MESON_TAC[SMOOTH_MAP_ON_HAS_DERIVATIVE]];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[lcovd; GSYM mderiv] THEN AP_TERM_TAC THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `christoffel (G:real^N->real^N^N) y ((X:real^N->real^N) y)
                                ((Y:real^N->real^N) y)`;
                 `(Z:real^N->real^N) y`] LRG_METRIC_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `(Y:real^N->real^N) y`; `(X:real^N->real^N) y`;
                 `(Z:real^N->real^N) y`] LRG_MDERIV_CHRISTOFFEL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let LCOVD_TORSION_FREE = prove
 (`!U (G:real^N->real^N^N) X Y y.
        metric_field U G /\ smooth_map_on U X /\ smooth_map_on U Y /\ y IN U
        ==> lcovd G X Y y - lcovd G Y X y = lbracket X Y y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lcovd; lbracket] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `(X:real^N->real^N) y`; `(Y:real^N->real^N) y`]
         CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* Pullbacks of metric fields by diffeomorphisms: derivative facts,          *)
(* METRIC_FIELD_PULLBACK, the derivative of a pulled back metric, symmetry   *)
(* of second derivatives (dd2).                                              *)
(* ========================================================================= *)

let LRG_DIFFEO_DERIV = prove
 (`!U U' (h:real^N->real^N) h' y.
        diffeomorphism_on U' U h h' /\ y IN U'
        ==> h y IN U /\ h'(h y) = y /\
            (h has_derivative frechet_derivative h (at y)) (at y) /\
            linear(frechet_derivative h (at y)) /\
            (!v. frechet_derivative h' (at (h y))
                   (frechet_derivative h (at y) v) = v) /\
            (!w. frechet_derivative h (at y)
                   (frechet_derivative h' (at (h y)) w) = w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^N) y IN U` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(h':real^N->real^N) ((h:real^N->real^N) y) = y` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((h:real^N->real^N) has_derivative frechet_derivative h (at y)) (at y)`
  ASSUME_TAC THENL [ASM_MESON_TAC[SMOOTH_MAP_ON_HAS_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((h':real^N->real^N) has_derivative frechet_derivative h' (at (h y)))
    (at ((h:real^N->real^N) y))`
  ASSUME_TAC THENL [ASM_MESON_TAC[SMOOTH_MAP_ON_HAS_DERIVATIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`(h':real^N->real^N) o (h:real^N->real^N)`; `\x:real^N. x`;
      `frechet_derivative (h':real^N->real^N) (at ((h:real^N->real^N) y)) o
       frechet_derivative h (at y)`;
      `\x:real^N. x`; `U':real^N->bool`; `y:real^N`]
     LRG_HAS_DERIVATIVE_UNIQUE_OPEN) THEN
    ASM_SIMP_TAC[o_THM; HAS_DERIVATIVE_ID; DIFF_CHAIN_AT] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM];
    MP_TAC(ISPECL
     [`(h:real^N->real^N) o (h':real^N->real^N)`; `\x:real^N. x`;
      `frechet_derivative (h:real^N->real^N) (at y) o
       frechet_derivative (h':real^N->real^N) (at ((h:real^N->real^N) y))`;
      `\x:real^N. x`; `U:real^N->bool`; `(h:real^N->real^N) y`]
     LRG_HAS_DERIVATIVE_UNIQUE_OPEN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[o_THM; HAS_DERIVATIVE_ID] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FUN_EQ_THM; o_THM]]]);;

let LRG_MPULLBACK_DOT = prove
 (`!(h:real^N->real^N) G z a b.
        linear(frechet_derivative h (at z))
        ==> a dot (mpullback h G z ** b) =
            frechet_derivative h (at z) a dot
            (G (h z) ** frechet_derivative h (at z) b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let LRG_MPULLBACK_EQ = prove
 (`!(h:real^N->real^N) (G:real^N->real^N^N).
        mpullback h G =
        (\z. transp(matrix(frechet_derivative h (at z))) ** G(h z) **
             matrix(frechet_derivative h (at z)))`,
  REWRITE_TAC[FUN_EQ_THM; mpullback]);;

let METRIC_FIELD_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G.
        metric_field U G /\ diffeomorphism_on U' U h h'
        ==> metric_field U' (mpullback h G)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  REWRITE_TAC[metric_field] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[LRG_MPULLBACK_EQ] THEN
    MATCH_MP_TAC LRG_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LRG_SMOOTH_TRANSP THEN ASM_SIMP_TAC[LRG_SMOOTH_JACOBIAN];
      MATCH_MP_TAC LRG_SMOOTH_MATMUL THEN ASM_SIMP_TAC[LRG_SMOOTH_JACOBIAN] THEN
      SUBGOAL_THEN
       `(vectorize:real^N^N->real^(N,N)finite_prod) o
        (\z. (G:real^N->real^N^N) ((h:real^N->real^N) z)) =
        (vectorize o G) o h`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `z:real^N`] LRG_DIFFEO_DERIV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[mpullback; MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC] THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[LRG_MPULLBACK_DOT] THEN
      MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(v:real^N = vec 0)` THEN REWRITE_TAC[] THEN
      ASM_MESON_TAC[LINEAR_0]]]);;

let LRG_DD2_SYM = prove
 (`!s (h:real^N->real^N) y u v.
        open s /\ smooth_map_on s h /\ y IN s
        ==> dd2 h y u v = dd2 h y v u`,
  REWRITE_TAC[dd2] THEN MESON_TAC[LRG_SECOND_DERIVATIVE_SYM]);;

let LRG_DIFFEO_LINEAR_AT = prove
 (`!U U' (h:real^N->real^N) h' z.
        diffeomorphism_on U' U h h' /\ z IN U'
        ==> linear(frechet_derivative h (at z))`,
  MESON_TAC[LRG_DIFFEO_DERIV]);;

let LRG_MDERIV_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G y a b c.
        metric_field U G /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> a dot (mderiv (mpullback h G) y c ** b) =
            dd2 h y c a dot (G (h y) ** frechet_derivative h (at y) b) +
            frechet_derivative h (at y) a dot
              (mderiv G (h y) (frechet_derivative h (at y) c) **
               frechet_derivative h (at y) b) +
            frechet_derivative h (at y) a dot (G (h y) ** dd2 h y c b)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U' (mpullback (h:real^N->real^N) G)` ASSUME_TAC
  THENL [ASM_MESON_TAC[METRIC_FIELD_PULLBACK]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. lift(a dot (mpullback (h:real^N->real^N) G z ** b))`;
    `\z. lift(frechet_derivative (h:real^N->real^N) (at z) a dot
              ((G:real^N->real^N^N) (h z) ** frechet_derivative h (at z) b))`;
    `\w. lift(a dot (mderiv (mpullback (h:real^N->real^N) G) y w ** b))`;
    `\w. lift(dd2 (h:real^N->real^N) y w a dot
                ((G:real^N->real^N^N) (h y) ** frechet_derivative h (at y) b) +
              frechet_derivative h (at y) a dot
                (mderiv G (h y) (frechet_derivative h (at y) w) **
                 frechet_derivative h (at y) b +
                 G (h y) ** dd2 h y w b))`;
    `U':real^N->bool`; `y:real^N`] LRG_HAS_DERIVATIVE_UNIQUE_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC LRG_MPULLBACK_DOT THEN
      MATCH_MP_TAC LRG_DIFFEO_LINEAR_AT THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                            `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LRG_HAS_DERIVATIVE_GDOT THEN
      ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF];
      MP_TAC(ISPECL
       [`\z. (G:real^N->real^N^N) ((h:real^N->real^N) z)`;
        `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                             (G:real^N->real^N^N)) (at ((h:real^N->real^N) y)) o
         frechet_derivative h (at y)`;
        `\z. frechet_derivative (h:real^N->real^N) (at z) a`;
        `frechet_derivative (\z. frechet_derivative (h:real^N->real^N) (at z) a)
                            (at y)`;
        `\z. frechet_derivative (h:real^N->real^N) (at z) b`;
        `frechet_derivative (\z. frechet_derivative (h:real^N->real^N) (at z) b)
                            (at y)`;
        `y:real^N`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [SUBGOAL_THEN
           `(vectorize:real^N^N->real^(N,N)finite_prod) o
            (\z. (G:real^N->real^N^N) ((h:real^N->real^N) z)) =
            (vectorize o G) o h`
          SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
          MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF];
          REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
          ASM_MESON_TAC[LRG_SMOOTH_FRECHET_DIFFERENTIABLE];
          REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
          ASM_MESON_TAC[LRG_SMOOTH_FRECHET_DIFFERENTIABLE]];
        REWRITE_TAC[dd2; o_THM; mderiv]]];
    DISCH_THEN(MP_TAC o C AP_THM `c:real^N`) THEN
    REWRITE_TAC[LIFT_EQ; DOT_RADD]]);;

(* The transformation law of the Christoffel symbols. *)

let LCHRISTOFFEL_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G y u v.
        metric_field U G /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> frechet_derivative h (at y) (christoffel (mpullback h G) y u v) =
            christoffel G (h y) (frechet_derivative h (at y) u)
                                (frechet_derivative h (at y) v) +
            dd2 h y u v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U' (mpullback (h:real^N->real^N) G)` ASSUME_TAC
  THENL [ASM_MESON_TAC[METRIC_FIELD_PULLBACK]; ALL_TAC] THEN
  MATCH_MP_TAC LRG_METRIC_DOT_EQ THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `G:real^N->real^N^N`;
                        `(h:real^N->real^N) y`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!w'. frechet_derivative (h:real^N->real^N) (at y) w' dot
         ((G:real^N->real^N^N) (h y) ** frechet_derivative h (at y)
             (christoffel (mpullback h G) y u v)) =
         frechet_derivative h (at y) w' dot
         (G (h y) ** (christoffel G (h y) (frechet_derivative h (at y) u)
                                          (frechet_derivative h (at y) v) +
                      dd2 h y u v))`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN
    MP_TAC(ISPECL [`h:real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`;
                   `w:real^N`;
                   `christoffel (mpullback (h:real^N->real^N) G) y u v`]
           LRG_MPULLBACK_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`U':real^N->bool`; `mpullback (h:real^N->real^N) G`;
                   `y:real^N`; `u:real^N`; `v:real^N`; `w:real^N`]
           LRG_CHRISTOFFEL_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`]
           LRG_MDERIV_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_RADD] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                   `(h:real^N->real^N) y`;
                   `frechet_derivative (h:real^N->real^N) (at y) u`;
                   `frechet_derivative (h:real^N->real^N) (at y) v`;
                   `frechet_derivative (h:real^N->real^N) (at y) w`]
           LRG_CHRISTOFFEL_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U':real^N->bool`; `h:real^N->real^N`; `y:real^N`;
                   `u:real^N`; `w:real^N`] LRG_DD2_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U':real^N->bool`; `h:real^N->real^N`; `y:real^N`;
                   `v:real^N`; `u:real^N`] LRG_DD2_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U':real^N->bool`; `h:real^N->real^N`; `y:real^N`;
                   `v:real^N`; `w:real^N`] LRG_DD2_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                   `(h:real^N->real^N) y`; `dd2 (h:real^N->real^N) y w v`;
                   `frechet_derivative (h:real^N->real^N) (at y) u`]
           LRG_METRIC_SYM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `w:real^N` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `frechet_derivative (h':real^N->real^N) (at ((h:real^N->real^N) y)) w`) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Naturality of the curvature tensor under pullback by a diffeomorphism     *)
(* (LRIEMANN_PULLBACK), via the derivative of the transformation law of the  *)
(* Christoffel symbols.                                                      *)
(* ========================================================================= *)

let LRG_FRECHET_DERIVATIVE_CHAIN = prove
 (`!(f:real^M->real^N) (g:real^N->real^P) y u.
        f differentiable at y /\ g differentiable at (f y)
        ==> frechet_derivative (\z. g (f z)) (at y) u =
            frechet_derivative g (at (f y)) (frechet_derivative f (at y) u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (g:real^N->real^P) ((f:real^M->real^N) z)) = g o f`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative ((g:real^N->real^P) o (f:real^M->real^N)) (at y) =
    frechet_derivative g (at (f y)) o frechet_derivative f (at y)`
  (fun th -> REWRITE_TAC[th; o_THM]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

let LRG_DD2_DERIV_SYM = prove
 (`!s (h:real^N->real^N) y u v w.
        open s /\ smooth_map_on s h /\ y IN s
        ==> frechet_derivative (\z. dd2 h z v w) (at y) u =
            frechet_derivative (\z. dd2 h z u w) (at y) v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dd2] THEN
  MATCH_MP_TAC LRG_SECOND_DERIVATIVE_SYM THEN
  EXISTS_TAC `s:real^N->bool` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]);;

let LRG_DCHRISTOFFEL_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G y u v w.
        metric_field U G /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> frechet_derivative h (at y)
              (frechet_derivative (\z. christoffel (mpullback h G) z v w)
                                  (at y) u) +
            dd2 h y u (christoffel (mpullback h G) y v w) =
            christoffel G (h y) (dd2 h y u v) (frechet_derivative h (at y) w) +
            christoffel G (h y) (frechet_derivative h (at y) v) (dd2 h y u w) +
            frechet_derivative
              (\z. christoffel G z (frechet_derivative h (at y) v)
                                   (frechet_derivative h (at y) w))
              (at (h y)) (frechet_derivative h (at y) u) +
            frechet_derivative (\z. dd2 h z v w) (at y) u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U' (mpullback (h:real^N->real^N) G)` ASSUME_TAC
  THENL
   [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. frechet_derivative (h:real^N->real^N) (at z)`;
    `\z. christoffel (mpullback (h:real^N->real^N) G) z v w`;
    `frechet_derivative (\z. christoffel (mpullback (h:real^N->real^N) G) z v w)
                        (at y)`;
    `U':real^N->bool`; `y:real^N`] LRG_HAS_DERIVATIVE_LINFAM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC LRG_DIFFEO_LINEAR_AT THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                            `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`U':real^N->bool`; `h:real^N->real^N`; `y:real^N`;
                     `basis i:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN EXISTS_TAC `U':real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM dd2] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\z. christoffel (G:real^N->real^N^N) ((h:real^N->real^N) z)`;
    `\z. frechet_derivative (h:real^N->real^N) (at z) v`;
    `\u. dd2 (h:real^N->real^N) y u v`;
    `\z. frechet_derivative (h:real^N->real^N) (at z) w`;
    `\u. dd2 (h:real^N->real^N) y u w`;
    `U':real^N->bool`; `y:real^N`] LRG_HAS_DERIVATIVE_BILFAM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `(\z. christoffel (G:real^N->real^N^N) ((h:real^N->real^N) z)
                         (basis i) (basis j)) =
        (\x. christoffel G x (basis i) (basis j)) o h`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
       [REWRITE_TAC[differentiable] THEN
        EXISTS_TAC `frechet_derivative (h:real^N->real^N) (at y)` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[dd2; ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MP_TAC(ISPECL [`U':real^N->bool`; `h:real^N->real^N`; `y:real^N`;
                     `v:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[dd2; ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MP_TAC(ISPECL [`U':real^N->bool`; `h:real^N->real^N`; `y:real^N`;
                     `w:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `((\z. dd2 (h:real^N->real^N) z v w) has_derivative
     frechet_derivative (\z. dd2 h z v w) (at y)) (at y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN REWRITE_TAC[dd2] THEN
    MP_TAC(ISPECL [`U':real^N->bool`;
                   `\z. frechet_derivative (h:real^N->real^N) (at z) w`;
                   `y:real^N`; `v:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c d. frechet_derivative
            (\z. christoffel (G:real^N->real^N^N) ((h:real^N->real^N) z) c d)
            (at y) u =
          frechet_derivative (\z. christoffel G z c d) (at (h y))
                             (frechet_derivative h (at y) u)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`h:real^N->real^N`;
                   `\z. christoffel (G:real^N->real^N^N) z c d`;
                   `y:real^N`; `u:real^N`] LRG_FRECHET_DERIVATIVE_CHAIN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `frechet_derivative (h:real^N->real^N) (at y)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. frechet_derivative (h:real^N->real^N) (at z)
           (christoffel (mpullback h G) z v w)`;
    `\z. christoffel (G:real^N->real^N^N) ((h:real^N->real^N) z)
           (frechet_derivative h (at z) v) (frechet_derivative h (at z) w) +
         dd2 h z v w`;
    `\u. frechet_derivative (h:real^N->real^N) (at y)
           (frechet_derivative (\z. christoffel (mpullback h G) z v w) (at y) u) +
         dd2 h y u (christoffel (mpullback h G) y v w)`;
    `\u. (christoffel (G:real^N->real^N^N) ((h:real^N->real^N) y)
            (dd2 h y u v) (frechet_derivative h (at y) w) +
          christoffel G (h y) (frechet_derivative h (at y) v) (dd2 h y u w) +
          frechet_derivative
            (\z. christoffel G (h z) (frechet_derivative h (at y) v)
                                     (frechet_derivative h (at y) w))
            (at y) u) +
         frechet_derivative (\z. dd2 h z v w) (at y) u`;
    `U':real^N->bool`; `y:real^N`] LRG_HAS_DERIVATIVE_UNIQUE_OPEN) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC LCHRISTOFFEL_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`;
                            `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `u:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC);;

let LRIEMANN_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G y u v w.
        metric_field U G /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> frechet_derivative h (at y) (lriemann (mpullback h G) y u v w) =
            lriemann G (h y) (frechet_derivative h (at y) u)
                             (frechet_derivative h (at y) v)
                             (frechet_derivative h (at y) w)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[lriemann] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_SUB] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `u:real^N`; `v:real^N`; `w:real^N`]
         LRG_DCHRISTOFFEL_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP
    (VECTOR_ARITH `x + y = z ==> x = z - y:real^N`)) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `v:real^N`; `u:real^N`; `w:real^N`]
         LRG_DCHRISTOFFEL_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP
    (VECTOR_ARITH `x + y = z ==> x = z - y:real^N`)) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `u:real^N`;
                 `christoffel (mpullback (h:real^N->real^N) G) y v w`]
         LCHRISTOFFEL_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `v:real^N`;
                 `christoffel (mpullback (h:real^N->real^N) G) y u w`]
         LCHRISTOFFEL_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `v:real^N`; `w:real^N`] LCHRISTOFFEL_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `u:real^N`; `w:real^N`] LCHRISTOFFEL_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                 `(h:real^N->real^N) y`] CHRISTOFFEL_BILINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BILINEAR_RADD] THEN
  MP_TAC(ISPECL [`U':real^N->bool`; `h:real^N->real^N`; `y:real^N`;
                 `v:real^N`; `u:real^N`] LRG_DD2_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U':real^N->bool`; `h:real^N->real^N`; `y:real^N`;
                 `v:real^N`; `u:real^N`; `w:real^N`] LRG_DD2_DERIV_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* Algebraic symmetries of the curvature tensor, linearity, flat metrics,    *)
(* locality of the curvature quantities.                                     *)
(* ========================================================================= *)

let LRIEMANN_ANTISYM = prove
 (`!U (G:real^N->real^N^N) y u v w.
        metric_field U G /\ y IN U
        ==> lriemann G y v u w = --(lriemann G y u v w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lriemann] THEN VECTOR_ARITH_TAC);;

let LRG_DCHRISTOFFEL_SYM = prove
 (`!U (G:real^N->real^N^N) y a b.
        metric_field U G /\ y IN U
        ==> frechet_derivative (\z. christoffel G z a b) (at y) =
            frechet_derivative (\z. christoffel G z b a) (at y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
  EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[metric_field];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CHRISTOFFEL_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let LRIEMANN_BIANCHI1 = prove
 (`!U (G:real^N->real^N^N) y u v w.
        metric_field U G /\ y IN U
        ==> lriemann G y u v w + lriemann G y v w u + lriemann G y w u v =
            vec 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lriemann] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `w:real^N`; `v:real^N`] LRG_DCHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `w:real^N`; `u:real^N`] LRG_DCHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `v:real^N`; `u:real^N`] LRG_DCHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `w:real^N`; `v:real^N`] CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `w:real^N`; `u:real^N`] CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `v:real^N`; `u:real^N`] CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  VECTOR_ARITH_TAC);;

(* Linearity of the curvature tensor in each argument. *)

let LRG_LINEAR_COMPOSE_LAMBDA = prove
 (`!(f:real^N->real^P) (g:real^M->real^N).
        linear f /\ linear g ==> linear (\x. f (g x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (f:real^N->real^P) ((g:real^M->real^N) x)) = f o g`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[]);;

let LRG_CHRISTOFFEL_LINEAR = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> (!a. linear (christoffel G y a)) /\
            (!b. linear (\a. christoffel G y a b))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CHRISTOFFEL_BILINEAR) THEN
  REWRITE_TAC[bilinear; ETA_AX]);;

let LRG_DCHRISTOFFEL_LINEAR = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> (!b c. linear (frechet_derivative (\z. christoffel G z b c) (at y))) /\
            (!a c. linear (\b. frechet_derivative (\z. christoffel G z b c)
                                                  (at y) a)) /\
            (!a b. linear (\c. frechet_derivative (\z. christoffel G z b c)
                                                  (at y) a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN U ==> (!a. linear (christoffel (G:real^N->real^N^N) z a)) /\
                   (!b. linear (\a. christoffel G z a b))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
      `z:real^N`] LRG_CHRISTOFFEL_LINEAR) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. (\z. christoffel (G:real^N->real^N^N) z a b) differentiable at y`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `!b. frechet_derivative (\z. christoffel (G:real^N->real^N^N) z b c) (at y) =
          (\u. vsum (1..dimindex(:N))
                 (\i. b$i % frechet_derivative
                              (\z. christoffel G z (basis i) c) (at y) u))`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MP_TAC(ISPECL [`\z b. christoffel (G:real^N->real^N^N) z b c`;
                     `U:real^N->bool`; `y:real^N`; `b:real^N`]
             LRG_HAS_DERIVATIVE_LINFAM_CONST) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      BETA_TAC THEN REWRITE_TAC[LRG_LINEAR_VSUM_COMPONENTS]];
    SUBGOAL_THEN
     `!c. frechet_derivative (\z. christoffel (G:real^N->real^N^N) z b c) (at y) =
          (\u. vsum (1..dimindex(:N))
                 (\i. c$i % frechet_derivative
                              (\z. christoffel G z b (basis i)) (at y) u))`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MP_TAC(ISPECL [`\z. christoffel (G:real^N->real^N^N) z b`;
                     `U:real^N->bool`; `y:real^N`; `c:real^N`]
             LRG_HAS_DERIVATIVE_LINFAM_CONST) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      BETA_TAC THEN REWRITE_TAC[LRG_LINEAR_VSUM_COMPONENTS]]]);;

let LRIEMANN_TRILINEAR = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> (!v w. linear (\u. lriemann G y u v w)) /\
            (!u w. linear (\v. lriemann G y u v w)) /\
            (!u v. linear (\w. lriemann G y u v w))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_CHRISTOFFEL_LINEAR) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_DCHRISTOFFEL_LINEAR) THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[lriemann] THEN
  MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN CONJ_TAC THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN ASM_REWRITE_TAC[ETA_AX]);;

(* Flat metrics and locality. *)

let LRIEMANN_FLAT = prove
 (`!(A:real^N^N) y u v w. lriemann (\z. A) y u v w = vec 0`,
  SUBGOAL_THEN `!(A:real^N^N) z u v. christoffel (\z. A) z u v = vec 0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[christoffel; mderiv; o_DEF; FRECHET_DERIVATIVE_CONST_AT;
                MATRIFY_0; MATRIX_VECTOR_MUL_LZERO; DOT_RZERO; VEC_COMPONENT;
                REAL_ADD_LID; REAL_SUB_REFL; REAL_MUL_RZERO] THEN
    SUBGOAL_THEN `(lambda k. &0):real^N = vec 0` SUBST1_TAC THENL
     [SIMP_TAC[CART_EQ; LAMBDA_BETA; VEC_COMPONENT]; ALL_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO];
    ASM_REWRITE_TAC[lriemann; FRECHET_DERIVATIVE_CONST_AT] THEN
    VECTOR_ARITH_TAC]);;

let LRIEMANN_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 s y u v w.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
        ==> lriemann G1 y u v w = lriemann G2 y u v w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b z. z IN s ==> christoffel (G1:real^N->real^N^N) z a b =
                       christoffel G2 z a b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. frechet_derivative (\z. christoffel (G1:real^N->real^N^N) z a b) (at y) =
          frechet_derivative (\z. christoffel G2 z a b) (at y)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[lriemann]]);;

let LRICCI_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 s y u v.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
        ==> lricci G1 y u v = lricci G2 y u v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b c. lriemann (G1:real^N->real^N^N) y a b c = lriemann G2 y a b c`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LRIEMANN_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[lricci]]);;

let LSCALAR_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 s y.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
        ==> lscalar G1 y = lscalar G2 y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. lricci (G1:real^N->real^N^N) y a b = lricci G2 y a b`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LRICCI_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[lscalar]]);;

(* ========================================================================= *)
(* Metric antisymmetry of the curvature tensor (from symmetry of second      *)
(* derivatives of the metric), pair symmetry, symmetry of Ricci.             *)
(* ========================================================================= *)

let LRG_D2_METRIC = prove
 (`!U (G:real^N->real^N^N) y a b c d.
        metric_field U G /\ y IN U
        ==> frechet_derivative
              (\z. frechet_derivative (\x. lift(c dot (G x ** d))) (at z) b)
              (at y) a =
            lift(d dot (mderiv G y a ** christoffel G y b c) +
                 d dot (G y ** frechet_derivative (\z. christoffel G z b c)
                                                  (at y) a) +
                 c dot (mderiv G y a ** christoffel G y b d) +
                 c dot (G y ** frechet_derivative (\z. christoffel G z b d)
                                                  (at y) a))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative
      (\z. frechet_derivative (\x. lift(c dot ((G:real^N->real^N^N) x ** d)))
                              (at z) b) (at y) =
    frechet_derivative
      (\z. lift(d dot (G z ** christoffel G z b c)) +
           lift(c dot (G z ** christoffel G z b d))) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`G:real^N->real^N^N`; `x:real^N`; `c:real^N`; `d:real^N`]
           LRG_HAS_DERIVATIVE_GDOT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    BETA_TAC THEN REWRITE_TAC[GSYM LIFT_ADD] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LRG_MDERIV_CHRISTOFFEL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q r. ((\z. lift(p dot ((G:real^N->real^N^N) z ** christoffel G z q r)))
             has_derivative
             (\w. lift(p dot (mderiv G y w ** christoffel G y q r) +
                       p dot (G y ** frechet_derivative
                                      (\z. christoffel G z q r) (at y) w))))
            (at y)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL
     [`G:real^N->real^N^N`;
      `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                           (G:real^N->real^N^N)) (at y)`;
      `(\z. p):real^N->real^N`; `(\w. vec 0):real^N->real^N`;
      `\z. christoffel (G:real^N->real^N^N) z q r`;
      `frechet_derivative (\z. christoffel (G:real^N->real^N^N) z q r) (at y)`;
      `y:real^N`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF];
        REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
        MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[mderiv; DOT_LZERO; REAL_ADD_LID; DOT_RADD]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. lift(d dot ((G:real^N->real^N^N) z ** christoffel G z b c))`;
    `\w. lift(d dot (mderiv (G:real^N->real^N^N) y w ** christoffel G y b c) +
              d dot (G y ** frechet_derivative (\z. christoffel G z b c) (at y) w))`;
    `\z. lift(c dot ((G:real^N->real^N^N) z ** christoffel G z b d))`;
    `\w. lift(c dot (mderiv (G:real^N->real^N^N) y w ** christoffel G y b d) +
              c dot (G y ** frechet_derivative (\z. christoffel G z b d) (at y) w))`;
    `at (y:real^N)`] HAS_DERIVATIVE_ADD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[LIFT_ADD] THEN VECTOR_ARITH_TAC);;

let LRG_DOT_METRIC_SMOOTH = prove
 (`!U (G:real^N->real^N^N) c d.
        metric_field U G ==> smooth_map_on U (\x. lift(c dot (G x ** d)))`,
  REWRITE_TAC[metric_field] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; LRG_SMOOTH_MATVEC]);;

let LRG_RM_ANTISYM = prove
 (`!U (G:real^N->real^N^N) y a b c d.
        metric_field U G /\ y IN U
        ==> d dot (G y ** lriemann G y a b c) =
            --(c dot (G y ** lriemann G y a b d))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
                 `\x. lift(c dot ((G:real^N->real^N^N) x ** d))`;
                 `y:real^N`; `a:real^N`; `b:real^N`]
         LRG_SECOND_DERIVATIVE_SYM) THEN
  ASM_SIMP_TAC[LRG_DOT_METRIC_SMOOTH] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_D2_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[LIFT_EQ] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `d:real^N`; `a:real^N`;
                 `christoffel (G:real^N->real^N^N) y b c`]
         LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `c:real^N`; `a:real^N`;
                 `christoffel (G:real^N->real^N^N) y b d`]
         LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `d:real^N`; `b:real^N`;
                 `christoffel (G:real^N->real^N^N) y a c`]
         LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `c:real^N`; `b:real^N`;
                 `christoffel (G:real^N->real^N^N) y a d`]
         LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `christoffel (G:real^N->real^N^N) y b c`;
                 `christoffel (G:real^N->real^N^N) y a d`] LRG_METRIC_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `christoffel (G:real^N->real^N^N) y b d`;
                 `christoffel (G:real^N->real^N^N) y a c`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lriemann; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_RADD; DOT_RSUB] THEN
  REAL_ARITH_TAC);;

let LRIEMANN_METRIC_ANTISYM = prove
 (`!U (G:real^N->real^N^N) y u v w z.
        metric_field U G /\ y IN U
        ==> z dot (G y ** lriemann G y u v w) =
            --(w dot (G y ** lriemann G y u v z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_RM_ANTISYM THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* Pair symmetry, from the two antisymmetries and the Bianchi identity. *)

let LRG_RM_ANTI1 = prove
 (`!U (G:real^N->real^N^N) y a b c d.
        metric_field U G /\ y IN U
        ==> d dot (G y ** lriemann G y b a c) =
            --(d dot (G y ** lriemann G y a b c))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `a:real^N`; `b:real^N`; `c:real^N`] LRIEMANN_ANTISYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_RNEG]);;

let LRG_RM_BIANCHI = prove
 (`!U (G:real^N->real^N^N) y a b c d.
        metric_field U G /\ y IN U
        ==> d dot (G y ** lriemann G y a b c) +
            d dot (G y ** lriemann G y b c a) +
            d dot (G y ** lriemann G y c a b) = &0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM DOT_RADD; GSYM MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `a:real^N`; `b:real^N`; `c:real^N`] LRIEMANN_BIANCHI1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO]);;

let LRIEMANN_PAIR_SYM = prove
 (`!U (G:real^N->real^N^N) y u v w z.
        metric_field U G /\ y IN U
        ==> z dot (G y ** lriemann G y u v w) =
            u dot (G y ** lriemann G y z w v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U (G:real^N->real^N^N) /\ y IN U`
   (fun th -> LABEL_TAC "a1" (MATCH_MP LRG_RM_ANTI1 th) THEN
              LABEL_TAC "a2" (MATCH_MP LRG_RM_ANTISYM th) THEN
              LABEL_TAC "b" (MATCH_MP LRG_RM_BIANCHI th)) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "b" (MP_TAC o SPECL [`u:real^N`; `v:real^N`; `w:real^N`; `z:real^N`]) THEN
  USE_THEN "b" (MP_TAC o SPECL [`v:real^N`; `w:real^N`; `z:real^N`; `u:real^N`]) THEN
  USE_THEN "b" (MP_TAC o SPECL [`w:real^N`; `z:real^N`; `u:real^N`; `v:real^N`]) THEN
  USE_THEN "b" (MP_TAC o SPECL [`z:real^N`; `u:real^N`; `v:real^N`; `w:real^N`]) THEN
  USE_THEN "a1" (SUBST1_TAC o SPECL [`u:real^N`; `w:real^N`; `v:real^N`; `z:real^N`]) THEN
  USE_THEN "a2" (SUBST1_TAC o SPECL [`v:real^N`; `w:real^N`; `z:real^N`; `u:real^N`]) THEN
  USE_THEN "a1" (SUBST1_TAC o SPECL [`v:real^N`; `z:real^N`; `w:real^N`; `u:real^N`]) THEN
  USE_THEN "a2" (SUBST1_TAC o SPECL [`v:real^N`; `z:real^N`; `w:real^N`; `u:real^N`]) THEN
  USE_THEN "a1" (SUBST1_TAC o SPECL [`u:real^N`; `z:real^N`; `w:real^N`; `v:real^N`]) THEN
  USE_THEN "a2" (SUBST1_TAC o SPECL [`u:real^N`; `z:real^N`; `w:real^N`; `v:real^N`]) THEN
  USE_THEN "a2" (SUBST1_TAC o SPECL [`u:real^N`; `w:real^N`; `z:real^N`; `v:real^N`]) THEN
  USE_THEN "a1" (SUBST1_TAC o SPECL [`u:real^N`; `z:real^N`; `v:real^N`; `w:real^N`]) THEN
  USE_THEN "a2" (SUBST1_TAC o SPECL [`u:real^N`; `v:real^N`; `z:real^N`; `w:real^N`]) THEN
  USE_THEN "a1" (SUBST1_TAC o SPECL [`w:real^N`; `z:real^N`; `v:real^N`; `u:real^N`]) THEN
  USE_THEN "a2" (SUBST1_TAC o SPECL [`w:real^N`; `z:real^N`; `v:real^N`; `u:real^N`]) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN REAL_ARITH_TAC);;

(* Symmetry of the Ricci tensor. *)

let LRG_COMPONENT_METRIC = prove
 (`!U (G:real^N->real^N^N) y x k.
        metric_field U G /\ y IN U /\ 1 <= k /\ k <= dimindex(:N)
        ==> x$k = sum (1..dimindex(:N))
                    (\j. matrix_inv(G y)$k$j * (basis j dot (G y ** x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `x = matrix_inv((G:real^N->real^N^N) y) ** (G y ** x)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT] THEN
  GEN_REWRITE_TAC LAND_CONV [dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[DOT_BASIS]);;

let LRG_MATRIX_INV_SYM = prove
 (`!U (G:real^N->real^N^N) y i j.
        metric_field U G /\ y IN U
        ==> matrix_inv(G y)$i$j = matrix_inv(G y)$j$i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `transp(matrix_inv((G:real^N->real^N^N) y)) = matrix_inv(G y)`
  MP_TAC THENL
   [REWRITE_TAC[GSYM MATRIX_INV_TRANSP] THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[metric_field];
    DISCH_THEN(MP_TAC o AP_TERM `\A:real^N^N. A$j$i`) THEN
    REWRITE_TAC[TRANSP_COMPONENT]]);;

let LRICCI_SYM = prove
 (`!U (G:real^N->real^N^N) y u v.
        metric_field U G /\ y IN U
        ==> lricci G y u v = lricci G y v u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. lricci (G:real^N->real^N^N) y a b =
          sum (1..dimindex(:N))
           (\k. sum (1..dimindex(:N))
                 (\j. matrix_inv(G y)$k$j *
                      (basis j dot (G y ** lriemann G y (basis k) a b))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[lricci] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LRG_COMPONENT_METRIC THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRIEMANN_PAIR_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Ricci and scalar curvature under pullback.                                *)
(* ========================================================================= *)

let LRG_TRACE_MATRIX = prove
 (`!f:real^N->real^N.
        trace(matrix f) = sum (1..dimindex(:N)) (\k. f(basis k)$k)`,
  GEN_TAC THEN REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  SIMP_TAC[MATRIX_COMPONENT]);;

let LRG_TRACE_CONJ = prove
 (`!(A:real^N->real^N) (J:real^N->real^N) (K:real^N->real^N).
        linear A /\ linear J /\ linear K /\ (!w. J (K w) = w)
        ==> trace(matrix (\x. K (A (J x)))) = trace(matrix A)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `matrix (\x. (K:real^N->real^N) ((A:real^N->real^N) ((J:real^N->real^N) x))) =
    matrix K ** (matrix A ** matrix J)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `(\x. (K:real^N->real^N) ((A:real^N->real^N) ((J:real^N->real^N) x))) =
      K o (A o J)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_COMPOSE];
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix (J:real^N->real^N) ** matrix (K:real^N->real^N) = mat 1`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM MATRIX_COMPOSE] THEN
    SUBGOAL_THEN `(J:real^N->real^N) o (K:real^N->real^N) = (\x. x)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; REWRITE_TAC[MATRIX_ID]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN
  ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_MUL_RID]);;

let LRG_DIFFEO_INV_LINEAR = prove
 (`!U U' (h:real^N->real^N) h' y.
        diffeomorphism_on U' U h h' /\ y IN U'
        ==> linear(frechet_derivative h' (at (h y)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U':real^N->bool`; `U:real^N->bool`; `h':real^N->real^N`;
                 `h:real^N->real^N`; `(h:real^N->real^N) y`] LRG_DIFFEO_DERIV) THEN
  ASM_SIMP_TAC[DIFFEOMORPHISM_ON_SYM] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LRG_DIFFEO_DERIV]; SIMP_TAC[]]);;

let LRICCI_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G y u v.
        metric_field U G /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> lricci (mpullback h G) y u v =
            lricci G (h y) (frechet_derivative h (at y) u)
                           (frechet_derivative h (at y) v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (h':real^N->real^N)
                                          (at ((h:real^N->real^N) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_DIFFEO_INV_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. lriemann (mpullback (h:real^N->real^N) G) y a u v =
        frechet_derivative h' (at (h y))
          (lriemann G (h y) (frechet_derivative h (at y) a)
                            (frechet_derivative h (at y) u)
                            (frechet_derivative h (at y) v))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`;
                   `a:real^N`; `u:real^N`; `v:real^N`] LRIEMANN_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[lricci] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC
   `\x. frechet_derivative (h':real^N->real^N) (at ((h:real^N->real^N) y))
          (lriemann G (h y) (frechet_derivative h (at y) x)
                            (frechet_derivative h (at y) u)
                            (frechet_derivative h (at y) v))`
   LRG_TRACE_MATRIX) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC
   `\b. lriemann (G:real^N->real^N^N) ((h:real^N->real^N) y) b
          (frechet_derivative h (at y) u) (frechet_derivative h (at y) v)`
   LRG_TRACE_MATRIX) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL
   [`\b. lriemann (G:real^N->real^N^N) ((h:real^N->real^N) y) b
           (frechet_derivative h (at y) u) (frechet_derivative h (at y) v)`;
    `frechet_derivative (h:real^N->real^N) (at y)`;
    `frechet_derivative (h':real^N->real^N) (at ((h:real^N->real^N) y))`]
   LRG_TRACE_CONJ) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(h:real^N->real^N) y`]
         LRIEMANN_TRILINEAR) THEN
  ASM_SIMP_TAC[]);;

(* Bilinearity of the Ricci tensor, entrywise sums, traces. *)

let LRG_LINEAR_LIFT_COMPONENT_COMPOSE = prove
 (`!(f:real^M->real^N) k. linear f ==> linear (\x. lift(f x$k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift((f:real^M->real^N) x$k)) = (\z:real^N. lift(z$k)) o f`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT]);;

let LRG_LRICCI_LINEAR = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> (!b. linear (\a. lift(lricci G y a b))) /\
            (!a. linear (\b. lift(lricci G y a b)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRIEMANN_TRILINEAR) THEN
  REWRITE_TAC[lricci; LIFT_SUM; o_DEF] THEN
  CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC LRG_LINEAR_LIFT_COMPONENT_COMPOSE THEN
  ASM_REWRITE_TAC[]);;

let LRG_LRICCI_EXPAND = prove
 (`!U (G:real^N->real^N^N) y a b.
        metric_field U G /\ y IN U
        ==> lricci G y a b =
            sum (1..dimindex(:N))
              (\p. a$p * sum (1..dimindex(:N))
                           (\q. b$q * lricci G y (basis p) (basis q)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LRICCI_LINEAR) THEN
  MP_TAC(ISPECL [`\a. lift(lricci (G:real^N->real^N^N) y a b)`; `a:real^N`]
         LRG_LINEAR_DROP_EXPAND) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  BETA_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`\b. lift(lricci (G:real^N->real^N^N) y (basis p) b)`;
                 `b:real^N`] LRG_LINEAR_DROP_EXPAND) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[]);;

let LRG_SUM_ENTRYWISE = prove
 (`!X Y:real^N^N.
        sum (1..dimindex(:N)) (\i. sum (1..dimindex(:N)) (\j. X$i$j * Y$i$j)) =
        trace(X ** transp Y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  SIMP_TAC[matrix_mul; LAMBDA_BETA; TRANSP_COMPONENT]);;

let LRG_TRACE_CONGRUENCE = prove
 (`!(J:real^N^N) (A:real^N^N) (B:real^N^N).
        invertible J
        ==> trace((matrix_inv J ** A ** matrix_inv(transp J)) **
                  (transp J ** B ** J)) =
            trace(A ** B)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible(transp(J:real^N^N))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INVERTIBLE_TRANSP]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  SUBGOAL_THEN
   `!X:real^N^N. matrix_inv(transp(J:real^N^N)) ** transp J ** X = X`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[MATRIX_MUL_ASSOC; MATRIX_INV; MATRIX_MUL_LID]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_RID]);;

let LRG_MATRIX_MUL_COMPONENT = prove
 (`!(A:real^N^N) (B:real^N^N) i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (A ** B)$i$j = sum (1..dimindex(:N)) (\k. A$i$k * B$k$j)`,
  SIMP_TAC[matrix_mul; LAMBDA_BETA]);;

let LSCALAR_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G y.
        metric_field U G /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> lscalar (mpullback h G) y = lscalar G (h y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (h':real^N->real^N)
                                          (at ((h:real^N->real^N) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_DIFFEO_INV_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible(matrix(frechet_derivative (h:real^N->real^N) (at y)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
    EXISTS_TAC `matrix(frechet_derivative (h':real^N->real^N)
                                          (at ((h:real^N->real^N) y)))` THEN
    ASM_SIMP_TAC[GSYM MATRIX_COMPOSE] THEN
    SUBGOAL_THEN
     `frechet_derivative (h':real^N->real^N) (at ((h:real^N->real^N) y)) o
      frechet_derivative h (at y) = (\x. x)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; REWRITE_TAC[MATRIX_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) ((h:real^N->real^N) y))`
  ASSUME_TAC THENL [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> lricci (mpullback (h:real^N->real^N) G) y (basis i) (basis j) =
              (transp(matrix(frechet_derivative h (at y))) **
               ((lambda p q. lricci (G:real^N->real^N^N) (h y)
                                    (basis p) (basis q)):real^N^N) **
               matrix(frechet_derivative h (at y)))$i$j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`;
                   `basis i:real^N`; `basis j:real^N`] LRICCI_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                   `(h:real^N->real^N) y`;
                   `frechet_derivative (h:real^N->real^N) (at y) (basis i)`;
                   `frechet_derivative (h:real^N->real^N) (at y) (basis j)`]
           LRG_LRICCI_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT; TRANSP_COMPONENT; MATRIX_COMPONENT] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA; MATRIX_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[lscalar] THEN
  SUBGOAL_THEN
   `sum (1..dimindex(:N))
     (\i. sum (1..dimindex(:N))
       (\j. matrix_inv(mpullback (h:real^N->real^N) G y)$i$j *
            lricci (mpullback h G) y (basis i) (basis j))) =
    sum (1..dimindex(:N))
     (\i. sum (1..dimindex(:N))
       (\j. matrix_inv(mpullback h G y)$i$j *
            (transp(matrix(frechet_derivative h (at y))) **
             ((lambda p q. lricci (G:real^N->real^N^N) (h y)
                                  (basis p) (basis q)):real^N^N) **
             matrix(frechet_derivative h (at y)))$i$j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN
    STRIP_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (1..dimindex(:N))
     (\i. sum (1..dimindex(:N))
       (\j. matrix_inv((G:real^N->real^N^N) ((h:real^N->real^N) y))$i$j *
            lricci G (h y) (basis i) (basis j))) =
    sum (1..dimindex(:N))
     (\i. sum (1..dimindex(:N))
       (\j. matrix_inv(G (h y))$i$j *
            ((lambda p q. lricci (G:real^N->real^N^N) (h y)
                                 (basis p) (basis q)):real^N^N)$i$j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN
    STRIP_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA];
    ALL_TAC] THEN
  REWRITE_TAC[LRG_SUM_ENTRYWISE; mpullback] THEN
  SUBGOAL_THEN
   `matrix_inv(transp(matrix(frechet_derivative (h:real^N->real^N) (at y))) **
               (G:real^N->real^N^N) (h y) ** matrix(frechet_derivative h (at y))) =
    matrix_inv(matrix(frechet_derivative h (at y))) ** matrix_inv(G (h y)) **
    matrix_inv(transp(matrix(frechet_derivative h (at y))))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_MATRIX_MUL; INVERTIBLE_TRANSP;
                 MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  MP_TAC(ISPECL [`matrix(frechet_derivative (h:real^N->real^N) (at y))`;
                 `matrix_inv((G:real^N->real^N^N) ((h:real^N->real^N) y))`;
                 `transp((lambda p q. lricci (G:real^N->real^N^N)
                                       ((h:real^N->real^N) y)
                                       (basis p) (basis q)):real^N^N)`]
         LRG_TRACE_CONGRUENCE) THEN
  ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC]);;

(* ========================================================================= *)
(* Convention test.  The metric 4/(1+|z|^2)^2 times the identity             *)
(* (stereographic coordinates of the round unit sphere) has sectional        *)
(* curvature 1.  The computation is done in any dimension and specialised to *)
(* real^2 at the end.                                                        *)
(* ========================================================================= *)

let LRG_HAS_DERIVATIVE_REAL_COMPOSE = prove
 (`!(q:real->real) q' (p:real^N->real^1) p' z.
        (q has_real_derivative q') (atreal (drop(p z))) /\
        (p has_derivative p') (at z)
        ==> ((\x. lift(q(drop(p x)))) has_derivative (\h. q' % p' h)) (at z)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_REAL_FRECHET_DERIVATIVE_AT]) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:real^N->real^1`; `lift o (q:real->real) o drop`;
                 `p':real^N->real^1`; `\x:real^1. q' % x`; `z:real^N`]
         DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[o_DEF]);;

let LRG_SPH_Q1 = prove
 (`!t. &0 <= t
       ==> ((\t. &4 / (&1 + t) pow 2) has_real_derivative
            (--(&8) / (&1 + t) pow 3)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(DISCH_ALL(REAL_DIFF_CONV
    `((\t. &4 / (&1 + t) pow 2) has_real_derivative f') (atreal t)`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(&1 + t = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_FIELD]);;

let LRG_SPH_Q2 = prove
 (`!t. &0 <= t
       ==> ((\t. --(&2) / (&1 + t)) has_real_derivative
            (&2 / (&1 + t) pow 2)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(DISCH_ALL(REAL_DIFF_CONV
    `((\t. --(&2) / (&1 + t)) has_real_derivative f') (atreal t)`)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(&1 + t = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let LRG_SPH_C_DERIV = prove
 (`!z:real^N.
        ((\x. lift(&4 / (&1 + norm x pow 2) pow 2)) has_derivative
         (\h. lift(--(&16) * (z dot h) / (&1 + norm z pow 2) pow 3))) (at z)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\t. &4 / (&1 + t) pow 2`;
                 `--(&8) / (&1 + norm(z:real^N) pow 2) pow 3`;
                 `\x:real^N. lift(norm x pow 2)`;
                 `\h:real^N. &2 % lift(z dot h)`; `z:real^N`]
         LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  REWRITE_TAC[LIFT_DROP; HAS_DERIVATIVE_SQNORM_AT] THEN
  SIMP_TAC[LRG_SPH_Q1; REAL_LE_POW_2] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC; GSYM LIFT_CMUL] THEN
  GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let LRG_SPH_G_DERIV = prove
 (`!z:real^N.
        ((\x. lift(--(&2) / (&1 + norm x pow 2))) has_derivative
         (\h. lift(&4 * (z dot h) / (&1 + norm z pow 2) pow 2))) (at z)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\t. --(&2) / (&1 + t)`;
                 `&2 / (&1 + norm(z:real^N) pow 2) pow 2`;
                 `\x:real^N. lift(norm x pow 2)`;
                 `\h:real^N. &2 % lift(z dot h)`; `z:real^N`]
         LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  REWRITE_TAC[LIFT_DROP; HAS_DERIVATIVE_SQNORM_AT] THEN
  SIMP_TAC[LRG_SPH_Q2; REAL_LE_POW_2] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC; GSYM LIFT_CMUL] THEN
  GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let LRG_SPH_POS = prove
 (`!z:real^N. &0 < &1 + norm z pow 2`,
  GEN_TAC THEN MP_TAC(SPEC `norm(z:real^N)` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let LRG_SPH_SMOOTH_C = prove
 (`smooth_map_on (:real^N) (\x. lift(&4 / (&1 + norm x pow 2) pow 2))`,
  SUBGOAL_THEN `smooth_map_on (:real^N) (\x. lift(norm x pow 2))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. x`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (\x. lift(&1 + norm x pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. lift(&1)`;
                   `\x:real^N. lift(norm x pow 2)`] SMOOTH_MAP_ON_LIFT_ADD) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (\x. lift((&1 + norm x pow 2) pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. lift(&1 + norm x pow 2)`; `2`]
           SMOOTH_MAP_ON_LIFT_POW) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^N)`; `\x:real^N. lift(&4)`;
                 `\x:real^N. lift((&1 + norm x pow 2) pow 2)`]
         SMOOTH_MAP_ON_LIFT_DIV) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; LIFT_DROP; IN_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_POW_LT THEN
  REWRITE_TAC[LRG_SPH_POS]);;

let LRG_SPH_METRIC = prove
 (`metric_field (:real^N) (\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1)`,
  REWRITE_TAC[metric_field; OPEN_UNIV; IN_UNIV] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\z:real^N. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1) =
      (\z. drop((\x:real^N. lift(&4 / (&1 + norm x pow 2) pow 2)) z) %
           vectorize(mat 1:real^N^N))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; LRG_SPH_SMOOTH_C];
    X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[TRANSP_MATRIX_CMUL; TRANSP_MAT; MATRIX_VECTOR_LMUL;
                MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[DOT_POS_LT] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[LRG_SPH_POS]]);;

let LRG_SPH_MDERIV = prove
 (`!z a:real^N.
        mderiv (\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1) z a =
        (--(&16) * (z dot a) / (&1 + norm z pow 2) pow 3) %% mat 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mderiv] THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod) o
    (\z:real^N. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1) =
    (\x. (&4 / (&1 + norm x pow 2) pow 2) % vectorize(mat 1:real^N^N))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL]; ALL_TAC] THEN
  MP_TAC(ISPEC `vectorize(mat 1:real^N^N)`
    (MATCH_MP HAS_DERIVATIVE_VMUL_DROP (SPEC `z:real^N` LRG_SPH_C_DERIV))) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[MATRIFY_CMUL; MATRIFY_VECTORIZE]);;

let LRG_SPH_CHRISTOFFEL = prove
 (`!z a b:real^N.
        christoffel (\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1) z a b =
        (--(&2) / (&1 + norm z pow 2)) %
        ((z dot a) % b + (z dot b) % a - (a dot b) % z)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_DOT_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`(:real^N)`;
    `(\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1):real^N->real^N^N`;
    `z:real^N`] THEN
  REWRITE_TAC[LRG_SPH_METRIC; IN_UNIV] THEN X_GEN_TAC `w:real^N` THEN
  MP_TAC(ISPECL
   [`(:real^N)`;
    `(\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1):real^N->real^N^N`;
    `z:real^N`; `a:real^N`; `b:real^N`; `w:real^N`] LRG_CHRISTOFFEL_DOT) THEN
  REWRITE_TAC[LRG_SPH_METRIC; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LRG_SPH_MDERIV; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID] THEN
  REWRITE_TAC[DOT_RMUL; DOT_RADD; DOT_RSUB] THEN
  REWRITE_TAC[DOT_SYM] THEN
  MP_TAC(SPEC `z:real^N` LRG_SPH_POS) THEN CONV_TAC REAL_FIELD);;

let LRG_LINEAR_DOT_SCALE = prove
 (`!a b:real^N. linear (\x:real^N. (x dot a) % b)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\x:real^N. (x dot a) % (b:real^N)) =
                (\x. drop((\x. lift(a dot x)) x) % b)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_DROP] THEN MESON_TAC[DOT_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_LIFT_DOT]);;

let LRG_SPH_DCHRISTOFFEL = prove
 (`!y a b u:real^N.
        frechet_derivative
          (\z. christoffel (\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1)
                           z a b) (at y) u =
        (--(&2) / (&1 + norm y pow 2)) %
        ((u dot a) % b + (u dot b) % a - (a dot b) % u) +
        (&4 * (y dot u) / (&1 + norm y pow 2) pow 2) %
        ((y dot a) % b + (y dot b) % a - (a dot b) % y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LRG_SPH_CHRISTOFFEL] THEN
  MP_TAC(ISPECL
   [`\x:real^N. --(&2) / (&1 + norm x pow 2)`;
    `\h:real^N. &4 * (y dot h) / (&1 + norm y pow 2) pow 2`;
    `\x:real^N. (x dot a) % b + (x dot b) % a - (a dot b) % x`;
    `\x:real^N. (x dot a) % b + (x dot b) % a - (a dot b) % x`;
    `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[o_DEF; LRG_SPH_G_DERIV] THEN ANTS_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN REWRITE_TAC[LRG_LINEAR_DOT_SCALE] THEN
    MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN REWRITE_TAC[LRG_LINEAR_DOT_SCALE] THEN
    MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]));;

let LRG_SPH_RIEMANN_DOT = prove
 (`!y u v:real^N.
        u dot lriemann (\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1) y u v v =
        (&4 / (&1 + norm y pow 2) pow 2) *
        ((u dot u) * (v dot v) - (u dot v) pow 2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[lriemann; LRG_SPH_DCHRISTOFFEL] THEN
  REWRITE_TAC[LRG_SPH_CHRISTOFFEL] THEN
  REWRITE_TAC[DOT_RADD; DOT_RSUB; DOT_RMUL; DOT_LADD; DOT_LSUB; DOT_LMUL] THEN
  REWRITE_TAC[NORM_POW_2] THEN REWRITE_TAC[DOT_SYM] THEN
  MP_TAC(SPEC `y:real^N` LRG_SPH_POS) THEN REWRITE_TAC[NORM_POW_2] THEN
  CONV_TAC REAL_FIELD);;

let LRG_SPH_SECTIONAL = prove
 (`!y u v:real^N.
        ~collinear {vec 0, u, v}
        ==> lsectional (\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1) y u v =
            &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((u:real^N) dot (v:real^N)) pow 2 < (u dot u) * (v dot v)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `abs((u:real^N) dot (v:real^N)) < norm u * norm v`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[NORM_CAUCHY_SCHWARZ_EQUAL; NORM_CAUCHY_SCHWARZ_ABS;
                    REAL_LT_LE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`2`; `abs((u:real^N) dot (v:real^N))`;
                   `norm(u:real^N) * norm(v:real^N)`]
           REAL_POW_LT2) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; ARITH_EQ; REAL_POW2_ABS; REAL_POW_MUL;
                    NORM_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[lsectional; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
  REWRITE_TAC[LRG_SPH_RIEMANN_DOT] THEN
  MP_TAC(SPEC `y:real^N` LRG_SPH_POS) THEN
  UNDISCH_TAC `((u:real^N) dot (v:real^N)) pow 2 < (u dot u) * (v dot v)` THEN
  CONV_TAC REAL_FIELD);;

(* The convention test: the stereographic metric of the unit 2-sphere has   *)
(* sectional curvature 1.                                                   *)

let LSECTIONAL_ROUND_SPHERE_2 = prove
 (`!y u v:real^2.
        ~collinear {vec 0, u, v}
        ==> lsectional (\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1) y u v = &1`,
  MATCH_ACCEPT_TAC LRG_SPH_SECTIONAL);;


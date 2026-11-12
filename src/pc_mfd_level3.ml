(* ========================================================================= *)
(* pc_mfd_level3: the Gauss equation in adapted coordinates.  G is a         *)
(* metric field on an open set of real^3 and lvs_hslice G its restriction    *)
(* to the slice y3 = 0 (the 2x2 block of G at (z,0)).  Results: the lowered  *)
(* curvature formula (generic N), the tangential Christoffel symbols and the *)
(* block inverse of G, the lowered Gauss equation, frame traces (with        *)
(* pc_rfa_pevol), the local scalar Gauss equation                            *)
(*   R_h = R_G - 2 Ric_G(n,n) + 2 det(h^-1 II)                               *)
(* with II = Hess(y3)/|grad y3|, and the Hessian of restrictions.            *)
(* Sources: Petersen, Riemannian Geometry, Thm 3.2.4; MT p. 215.             *)
(* ========================================================================= *)

needs "src/pc_mfd_level.ml";;
needs "src/pc_rfa_pevol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The slice metric lvs_hslice G (z) = upper 2x2 block of G(z,0); its        *)
(* bilinear form, its J^T G J form and its metric property.                  *)
(* ------------------------------------------------------------------------- *)

let lvs_hslice = new_definition
 `lvs_hslice (G:real^3->real^3^3) =
    \z:real^2. (lambda i j. G(lvs_iota z)$i$j):real^2^2`;;

let LVS_HSLICE_COMPONENT = prove
 (`!G z i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
             ==> (lvs_hslice G z)$i$j = (G:real^3->real^3^3)(lvs_iota z)$i$j`,
  SIMP_TAC[lvs_hslice; LAMBDA_BETA; DIMINDEX_2]);;

let LVS_HSLICE_DOT = prove
 (`!(G:real^3->real^3^3) z a b.
     a dot (lvs_hslice G z ** b) = lvs_iota a dot (G(lvs_iota z) ** lvs_iota b)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[dot; matrix_vector_mul; LAMBDA_BETA; DIMINDEX_2; DIMINDEX_3;
           SUM_2; SUM_3; ARITH; LVS_IOTA_COMPONENT; lvs_hslice] THEN
  REAL_ARITH_TAC);;

let LVS_HSLICE_TRANSP = prove
 (`!(G:real^3->real^3^3) z.
     lvs_hslice G z = transp(matrix lvs_iota) ** G(lvs_iota z) ** matrix lvs_iota`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MATRIX_EQ] THEN X_GEN_TAC `b:real^2` THEN
  REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN X_GEN_TAC `a:real^2` THEN
  REWRITE_TAC[LVS_HSLICE_DOT; GSYM MATRIX_VECTOR_MUL_ASSOC;
              DOT_MATRIX_TRANSP_RMUL] THEN
  SIMP_TAC[MATRIX_WORKS; LVS_IOTA_LINEAR]);;

let LVS_IOTA_EQ_0 = prove
 (`!z:real^2. lvs_iota z = vec 0 <=> z = vec 0`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3;
              LVS_IOTA_COMPONENT; VEC_COMPONENT]);;

let LVS_HSLICE_METRIC = prove
 (`!S (G:real^3->real^3^3).
     metric_field S G ==> metric_field {z | lvs_iota z IN S} (lvs_hslice G)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  REWRITE_TAC[metric_field] THEN ASM_SIMP_TAC[LVS_OPEN_IOTA_PREIMAGE] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[LRG_SMOOTH_VECTORIZE; LVS_OPEN_IOTA_PREIMAGE; DIMINDEX_2] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\z. lift(lvs_hslice G z$i$j)) =
      (\y. lift((G:real^3->real^3^3) y$i$j)) o lvs_iota`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[FUN_EQ_THM; o_THM; LVS_HSLICE_COMPONENT]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `S:real^3->bool` THEN
    ASM_SIMP_TAC[LVS_OPEN_IOTA_PREIMAGE; LVS_IOTA_SMOOTH] THEN CONJ_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `smooth_map_on S ((vectorize:real^3^3->real^(3,3)finite_prod) o
                                  (G:real^3->real^3^3))` THEN
    ASM_SIMP_TAC[LRG_SMOOTH_VECTORIZE; DIMINDEX_3] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LVS_HSLICE_TRANSP; MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lvs_iota z`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN REWRITE_TAC[MATRIX_MUL_ASSOC];
    X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN REWRITE_TAC[LVS_HSLICE_DOT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lvs_iota z`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[LVS_IOTA_EQ_0]]);;

(* ------------------------------------------------------------------------- *)
(* Generic N: the derivative of the lowered Christoffel                      *)
(* symbols z |-> p.G(z) Gamma(z)(q,r), and the lowered curvature in terms of *)
(* them:  w.G R(a,b)c = D_a(w.G Gamma(b,c)) - D_b(w.G Gamma(a,c))            *)
(*                      - (G Gamma(a,w)).Gamma(b,c) + (G Gamma(b,w)).Gamma(a,c).  *)
(* ------------------------------------------------------------------------- *)

let LVS_GDOT_CHRIST_DERIV = prove
 (`!U (G:real^N->real^N^N) y p q r.
     metric_field U G /\ y IN U
     ==> ((\z. lift(p dot (G z ** christoffel G z q r))) has_derivative
          (\v. lift(p dot (mderiv G y v ** christoffel G y q r) +
                    p dot (G y ** frechet_derivative (\z. christoffel G z q r)
                                                     (at y) v))))
         (at y)`,
  REPEAT STRIP_TAC THEN
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
    REWRITE_TAC[mderiv; DOT_LZERO; REAL_ADD_LID; DOT_RADD]]);;

let LVS_LRIEMANN_LOWER = prove
 (`!U (G:real^N->real^N^N) y a b c w.
     metric_field U G /\ y IN U
     ==> w dot (G y ** lriemann G y a b c) =
         drop(frechet_derivative (\z. lift(w dot (G z ** christoffel G z b c)))
                                 (at y) a) -
         drop(frechet_derivative (\z. lift(w dot (G z ** christoffel G z a c)))
                                 (at y) b) -
         (G y ** christoffel G y a w) dot christoffel G y b c +
         (G y ** christoffel G y b w) dot christoffel G y a c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `w:real^N`; `b:real^N`; `c:real^N`] LVS_GDOT_CHRIST_DERIV) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `w:real^N`; `a:real^N`; `c:real^N`] LVS_GDOT_CHRIST_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `w:real^N`; `a:real^N`;
                 `christoffel (G:real^N->real^N^N) y b c`]
                LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `w:real^N`; `b:real^N`;
                 `christoffel (G:real^N->real^N^N) y a c`]
                LRG_MDERIV_CHRISTOFFEL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y ** christoffel G y a w`;
                 `christoffel (G:real^N->real^N^N) y b c`] DOT_SYM) THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y ** christoffel G y b w`;
                 `christoffel (G:real^N->real^N^N) y a c`] DOT_SYM) THEN
  REWRITE_TAC[lriemann; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_RADD; DOT_RSUB] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The slice metric's derivative and Christoffel symbols are the tangential  *)
(* parts of those of G: a.(D_u h) b = (Pa).(D_Pu G)(Pb) and                  *)
(* w.h Gamma_h(a,b) = (Pw).G Gamma_G(Pa,Pb), P = lvs_iota.                   *)
(* ------------------------------------------------------------------------- *)

let LVS_HSLICE_MDERIV = prove
 (`!S (G:real^3->real^3^3) z u a b.
     metric_field S G /\ lvs_iota z IN S
     ==> a dot (mderiv (lvs_hslice G) z u ** b) =
         lvs_iota a dot (mderiv G (lvs_iota z) (lvs_iota u) ** lvs_iota b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field {z:real^2 | lvs_iota z IN S} (lvs_hslice G)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LVS_HSLICE_METRIC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. lift(a dot (lvs_hslice (G:real^3->real^3^3) x ** b))) has_derivative
     (\w. lift(a dot (mderiv (lvs_hslice G) z w ** b)))) (at z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_HAS_DERIVATIVE_GDOT THEN
    MP_TAC(ISPECL [`{z:real^2 | lvs_iota z IN S}`;
                   `lvs_hslice (G:real^3->real^3^3)`; `z:real^2`]
                  LRG_METRIC_FIELD_DIFF) THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. lift(a dot (lvs_hslice (G:real^3->real^3^3) x ** b))) has_derivative
     ((\w. lift(lvs_iota a dot (mderiv G (lvs_iota z) w ** lvs_iota b))) o
      lvs_iota)) (at z)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\x. lift(a dot (lvs_hslice (G:real^3->real^3^3) x ** b))) =
      (\y. lift(lvs_iota a dot (G y ** lvs_iota b))) o lvs_iota`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LVS_HSLICE_DOT]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    SIMP_TAC[HAS_DERIVATIVE_LINEAR; LVS_IOTA_LINEAR] THEN
    MATCH_MP_TAC LRG_HAS_DERIVATIVE_GDOT THEN
    ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. lift(a dot (lvs_hslice (G:real^3->real^3^3) x ** b))`;
    `\w. lift(a dot (mderiv (lvs_hslice (G:real^3->real^3^3)) z w ** b))`;
    `(\w. lift(lvs_iota a dot (mderiv (G:real^3->real^3^3) (lvs_iota z) w **
                                lvs_iota b))) o lvs_iota`;
    `z:real^2`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `u:real^2`) THEN
  REWRITE_TAC[o_THM; LIFT_EQ]);;

let LVS_HSLICE_CHRISTOFFEL = prove
 (`!S (G:real^3->real^3^3) z a b w.
     metric_field S G /\ lvs_iota z IN S
     ==> w dot (lvs_hslice G z ** christoffel (lvs_hslice G) z a b) =
         lvs_iota w dot (G(lvs_iota z) **
                         christoffel G (lvs_iota z) (lvs_iota a) (lvs_iota b))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{z:real^2 | lvs_iota z IN S}`;
                 `lvs_hslice (G:real^3->real^3^3)`; `z:real^2`;
                 `a:real^2`; `b:real^2`; `w:real^2`] LRG_CHRISTOFFEL_DOT) THEN
  ASM_SIMP_TAC[LVS_HSLICE_METRIC; IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `lvs_iota z`;
                 `lvs_iota a`; `lvs_iota b`; `lvs_iota w`] LRG_CHRISTOFFEL_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `z:real^2`]
                LVS_HSLICE_MDERIV) THEN
  ASM_SIMP_TAC[]);;

let LVS_HSLICE_GCHRIST_VEC = prove
 (`!S (G:real^3->real^3^3) z a b.
     metric_field S G /\ lvs_iota z IN S
     ==> lvs_hslice G z ** christoffel (lvs_hslice G) z a b =
         transp(matrix lvs_iota) **
         (G(lvs_iota z) ** christoffel G (lvs_iota z) (lvs_iota a) (lvs_iota b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN
  X_GEN_TAC `w:real^2` THEN REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN
  SIMP_TAC[MATRIX_WORKS; LVS_IOTA_LINEAR] THEN
  MATCH_MP_TAC LVS_HSLICE_CHRISTOFFEL THEN EXISTS_TAC `S:real^3->bool` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The block inverse of G (G^-1 = P h^-1 P^T + nu nu^T / g33,                *)
(* nu = G^-1 e3, g33 = e3.nu, in bilinear form) and the splitting of the     *)
(* Christoffel symbols of G on tangent vectors into the slice Christoffel    *)
(* symbols and a multiple of nu.                                             *)
(* ------------------------------------------------------------------------- *)

let LVS_POSDEF_INVERTIBLE = prove
 (`!A:real^N^N. (!v. ~(v = vec 0) ==> &0 < v dot (A ** v)) ==> invertible A`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[INVERTIBLE_DET_NZ; GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
  ASM_REWRITE_TAC[DOT_RZERO; REAL_LT_REFL]);;

let LVS_IOTA_TRANSP_E3 = prove
 (`transp(matrix lvs_iota) ** basis 3 = vec 0`,
  REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN X_GEN_TAC `w:real^2` THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL; DOT_RZERO] THEN
  SIMP_TAC[MATRIX_WORKS; LVS_IOTA_LINEAR; DOT_BASIS; DIMINDEX_3; ARITH;
           LVS_IOTA_COMPONENT]);;

let LVS_SYM_DOT = prove
 (`!(G0:real^N^N) a b. transp G0 = G0 ==> a dot (G0 ** b) = (G0 ** a) dot b`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV)
    [GSYM(ASSUME `transp(G0:real^N^N) = G0`)] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL]);;

let LVS_BLOCK_INV = prove
 (`!(G0:real^3^3) X Y.
     transp G0 = G0 /\ (!v. ~(v = vec 0) ==> &0 < v dot (G0 ** v))
     ==> X dot (matrix_inv G0 ** Y) =
         (transp(matrix lvs_iota) ** X) dot
         (matrix_inv(transp(matrix lvs_iota) ** G0 ** matrix lvs_iota) **
          (transp(matrix lvs_iota) ** Y)) +
         ((matrix_inv G0 ** basis 3) dot X) *
         ((matrix_inv G0 ** basis 3) dot Y) /
         (basis 3 dot (matrix_inv G0 ** basis 3))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible(G0:real^3^3)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LVS_POSDEF_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^2. matrix lvs_iota ** w = lvs_iota w` ASSUME_TAC THENL
   [SIMP_TAC[MATRIX_WORKS; LVS_IOTA_LINEAR]; ALL_TAC] THEN
  ABBREV_TAC `nu = matrix_inv(G0:real^3^3) ** basis 3` THEN
  SUBGOAL_THEN `(G0:real^3^3) ** nu = basis 3` ASSUME_TAC THENL
   [EXPAND_TAC "nu" THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(basis 3:real^3 = vec 0)` ASSUME_TAC THENL
   [SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `~(nu:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(G0:real^3^3) ** nu = basis 3` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `g33 = basis 3 dot (nu:real^3)` THEN
  SUBGOAL_THEN `&0 < g33` ASSUME_TAC THENL
   [EXPAND_TAC "g33" THEN
    SUBGOAL_THEN `basis 3 dot (nu:real^3) = nu dot ((G0:real^3^3) ** nu)`
    SUBST1_TAC THENL
     [REWRITE_TAC[ASSUME `(G0:real^3^3) ** nu = basis 3`] THEN
      MATCH_ACCEPT_TAC DOT_SYM;
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(nu:real^3)$3 = g33` ASSUME_TAC THENL
   [EXPAND_TAC "g33" THEN SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  ABBREV_TAC `H = transp(matrix lvs_iota) ** (G0:real^3^3) ** matrix lvs_iota` THEN
  SUBGOAL_THEN `!a:real^2. a dot ((H:real^2^2) ** a) =
                          lvs_iota a dot ((G0:real^3^3) ** lvs_iota a)`
  ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN
    ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible(H:real^2^2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LVS_POSDEF_INVERTIBLE THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LVS_IOTA_EQ_0];
    ALL_TAC] THEN
  ABBREV_TAC `Z = matrix_inv(G0:real^3^3) ** Y` THEN
  SUBGOAL_THEN `Y = (G0:real^3^3) ** Z` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  ABBREV_TAC `t = (Z:real^3)$3 / g33` THEN
  SUBGOAL_THEN `(Z:real^3)$3 = t * g33` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  ABBREV_TAC `a = lvs_proj((Z:real^3) - t % nu)` THEN
  SUBGOAL_THEN `Z = lvs_iota a + t % (nu:real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    SUBGOAL_THEN `((Z:real^3) - t % nu)$3 = &0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[LVS_IOTA_PROJ] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp(matrix lvs_iota) ** Y = (H:real^2^2) ** a` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
    EXPAND_TAC "H" THEN
    ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; LVS_IOTA_TRANSP_E3;
                    VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix_inv(H:real^2^2) ** (H ** a) = a` SUBST1_TAC THENL
   [SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV;
             ASSUME `invertible(H:real^2^2)`; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL;
              ASSUME `!w:real^2. matrix lvs_iota ** w = lvs_iota w`] THEN
  SUBGOAL_THEN `(nu:real^3) dot Y = t * g33` SUBST1_TAC THENL
   [REWRITE_TAC[ASSUME `Y = (G0:real^3^3) ** Z`] THEN
    MP_TAC(ISPECL [`G0:real^3^3`; `nu:real^3`; `Z:real^3`] LVS_SYM_DOT) THEN
    REWRITE_TAC[ASSUME `transp(G0:real^3^3) = G0`;
                ASSUME `(G0:real^3^3) ** nu = basis 3`] THEN
    DISCH_THEN SUBST1_TAC THEN SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[ASSUME `(Z:real^3)$3 = t * g33`];
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `Z = lvs_iota a + t % (nu:real^3)`; DOT_RADD; DOT_RMUL;
              ISPECL [`nu:real^3`; `X:real^3`] DOT_SYM] THEN
  UNDISCH_TAC `&0 < g33` THEN CONV_TAC REAL_FIELD);;

let LVS_CHRISTOFFEL_SPLIT = prove
 (`!S (G:real^3->real^3^3) z a b.
     metric_field S G /\ lvs_iota z IN S
     ==> christoffel G (lvs_iota z) (lvs_iota a) (lvs_iota b) =
         lvs_iota(christoffel (lvs_hslice G) z a b) +
         ((christoffel G (lvs_iota z) (lvs_iota a) (lvs_iota b))$3 /
          (basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))) %
         (matrix_inv(G(lvs_iota z)) ** basis 3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `z:real^2`;
                 `a:real^2`; `b:real^2`] LVS_HSLICE_CHRISTOFFEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `transp((G:real^3->real^3^3)(lvs_iota z)) = G(lvs_iota z) /\
    (!v. ~(v = vec 0) ==> &0 < v dot (G(lvs_iota z) ** v))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ABBREV_TAC `G0 = (G:real^3->real^3^3)(lvs_iota z)` THEN
  SUBGOAL_THEN `invertible(G0:real^3^3)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LVS_POSDEF_INVERTIBLE]; ALL_TAC] THEN
  ABBREV_TAC
   `X = christoffel (G:real^3->real^3^3) (lvs_iota z) (lvs_iota a) (lvs_iota b)` THEN
  ABBREV_TAC `C = christoffel (lvs_hslice (G:real^3->real^3^3)) z a b` THEN
  ABBREV_TAC `nu = matrix_inv(G0:real^3^3) ** basis 3` THEN
  SUBGOAL_THEN `(G0:real^3^3) ** nu = basis 3` ASSUME_TAC THENL
   [EXPAND_TAC "nu" THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  ABBREV_TAC `g33 = basis 3 dot (nu:real^3)` THEN
  SUBGOAL_THEN `&0 < g33` ASSUME_TAC THENL
   [EXPAND_TAC "g33" THEN
    SUBGOAL_THEN `basis 3 dot (nu:real^3) = nu dot ((G0:real^3^3) ** nu)`
    SUBST1_TAC THENL
     [REWRITE_TAC[ASSUME `(G0:real^3^3) ** nu = basis 3`] THEN
      MATCH_ACCEPT_TAC DOT_SYM;
      ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `(G0:real^3^3) ** nu = basis 3` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN
    MESON_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH_RULE `1 <= 3 /\ 3 <= 3`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(nu:real^3)$3 = g33` ASSUME_TAC THENL
   [EXPAND_TAC "g33" THEN SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  ABBREV_TAC `Wv = X - lvs_iota C - ((X:real^3)$3 / g33) % (nu:real^3)` THEN
  SUBGOAL_THEN `(Wv:real^3)$3 = &0` ASSUME_TAC THENL
   [EXPAND_TAC "Wv" THEN
    ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
                    LVS_IOTA_COMPONENT] THEN
    UNDISCH_TAC `&0 < g33` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^2. lvs_iota w dot ((G0:real^3^3) ** Wv) = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^2` THEN EXPAND_TAC "Wv" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                DOT_RSUB; DOT_RMUL] THEN
    REWRITE_TAC[ASSUME `(G0:real^3^3) ** nu = basis 3`] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH; LVS_IOTA_COMPONENT] THEN
    MP_TAC(ISPECL [`G:real^3->real^3^3`; `z:real^2`; `w:real^2`; `C:real^2`]
                  LVS_HSLICE_DOT) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^2`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Wv:real^3 = vec 0` ASSUME_TAC THENL
   [SUBGOAL_THEN `Wv = lvs_iota(lvs_proj(Wv:real^3))` SUBST1_TAC THENL
     [ASM_SIMP_TAC[LVS_IOTA_PROJ]; ALL_TAC] THEN
    REWRITE_TAC[LVS_IOTA_EQ_0] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lvs_iota(lvs_proj(Wv:real^3))`) THEN
    ASM_REWRITE_TAC[LVS_IOTA_EQ_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lvs_proj(Wv:real^3)`) THEN
    ASM_SIMP_TAC[LVS_IOTA_PROJ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `Wv:real^3 = vec 0` THEN EXPAND_TAC "Wv" THEN
  VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The lowered Gauss equation in adapted coordinates: for                    *)
(* a, b, c, w in real^2, with gamma(p,q) = Gamma_G(Pp,Pq)$3 and              *)
(* g33 = e3.G^-1 e3,                                                         *)
(*   w.h R_h(a,b)c = (Pw).G R_G(Pa,Pb)(Pc)                                   *)
(*                   + (gamma(a,w) gamma(b,c) - gamma(b,w) gamma(a,c)) / g33. *)
(* ------------------------------------------------------------------------- *)

let LVS_DERIV_SLICE = prove
 (`!S (G:real^3->real^3^3) z p q r a.
     metric_field S G /\ lvs_iota z IN S
     ==> frechet_derivative
           (\x. lift(r dot (lvs_hslice G x ** christoffel (lvs_hslice G) x p q)))
           (at z) a =
         frechet_derivative
           (\z:real^3. lift(lvs_iota r dot
                     (G z ** christoffel G z (lvs_iota p) (lvs_iota q))))
           (at (lvs_iota z)) (lvs_iota a)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `Fn = \y. lift(lvs_iota r dot ((G:real^3->real^3^3) y **
                                  christoffel G y (lvs_iota p) (lvs_iota q)))` THEN
  SUBGOAL_THEN
   `frechet_derivative
      (\x. lift(r dot (lvs_hslice (G:real^3->real^3^3) x **
                       christoffel (lvs_hslice G) x p q))) (at z) =
    frechet_derivative ((Fn:real^3->real^1) o lvs_iota) (at z)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `{x:real^2 | lvs_iota x IN S}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LVS_OPEN_IOTA_PREIMAGE THEN ASM_MESON_TAC[metric_field];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EXPAND_TAC "Fn" THEN
    REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LVS_HSLICE_CHRISTOFFEL THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((Fn:real^3->real^1) o lvs_iota) has_derivative
     (frechet_derivative Fn (at (lvs_iota z)) o lvs_iota)) (at z)`
  MP_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN
    SIMP_TAC[HAS_DERIVATIVE_LINEAR; LVS_IOTA_LINEAR] THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN EXPAND_TAC "Fn" THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `lvs_iota z`;
                   `lvs_iota r`; `lvs_iota p`; `lvs_iota q`]
                  LVS_GDOT_CHRIST_DERIV) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[differentiable];
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[o_THM]]);;

let LVS_QUAD_SLICE = prove
 (`!S (G:real^3->real^3^3) z p q r s.
     metric_field S G /\ lvs_iota z IN S
     ==> (lvs_hslice G z ** christoffel (lvs_hslice G) z p q) dot
         christoffel (lvs_hslice G) z r s =
         (G(lvs_iota z) ** christoffel G (lvs_iota z) (lvs_iota p) (lvs_iota q)) dot
         christoffel G (lvs_iota z) (lvs_iota r) (lvs_iota s) -
         (christoffel G (lvs_iota z) (lvs_iota p) (lvs_iota q))$3 *
         (christoffel G (lvs_iota z) (lvs_iota r) (lvs_iota s))$3 /
         (basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field {x:real^2 | lvs_iota x IN S} (lvs_hslice G)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LVS_HSLICE_METRIC]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible(lvs_hslice (G:real^3->real^3^3) z)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{x:real^2 | lvs_iota x IN S}`;
                   `lvs_hslice (G:real^3->real^3^3)`; `z:real^2`]
                  LRG_METRIC_INVERTIBLE) THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `transp((G:real^3->real^3^3)(lvs_iota z)) = G(lvs_iota z) /\
    (!v. ~(v = vec 0) ==> &0 < v dot (G(lvs_iota z) ** v))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible((G:real^3->real^3^3)(lvs_iota z))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LVS_POSDEF_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `christoffel (lvs_hslice (G:real^3->real^3^3)) z r s =
    matrix_inv(lvs_hslice G z) **
    (transp(matrix lvs_iota) **
     (G(lvs_iota z) ** christoffel G (lvs_iota z) (lvs_iota r) (lvs_iota s)))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `z:real^2`;
                   `r:real^2`; `s:real^2`] LVS_HSLICE_GCHRIST_VEC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `z:real^2`;
                 `p:real^2`; `q:real^2`] LVS_HSLICE_GCHRIST_VEC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ISPECL [`G:real^3->real^3^3`; `z:real^2`] LVS_HSLICE_TRANSP] THEN
  SUBGOAL_THEN
   `!w:real^3. matrix_inv((G:real^3->real^3^3)(lvs_iota z)) ** (G(lvs_iota z) ** w) = w`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^3. (matrix_inv((G:real^3->real^3^3)(lvs_iota z)) ** basis 3) dot
               (G(lvs_iota z) ** w) = w$3`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`(G:real^3->real^3^3)(lvs_iota z)`;
                   `matrix_inv((G:real^3->real^3^3)(lvs_iota z)) ** basis 3`;
                   `w:real^3`] LVS_SYM_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(G:real^3->real^3^3)(lvs_iota z)`;
    `(G:real^3->real^3^3)(lvs_iota z) **
     christoffel G (lvs_iota z) (lvs_iota p) (lvs_iota q)`;
    `(G:real^3->real^3^3)(lvs_iota z) **
     christoffel G (lvs_iota z) (lvs_iota r) (lvs_iota s)`] LVS_BLOCK_INV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let LVS_HSLICE_RIEMANN = prove
 (`!S (G:real^3->real^3^3) z a b c w.
     metric_field S G /\ lvs_iota z IN S
     ==> w dot (lvs_hslice G z ** lriemann (lvs_hslice G) z a b c) =
         lvs_iota w dot (G(lvs_iota z) **
                         lriemann G (lvs_iota z) (lvs_iota a) (lvs_iota b)
                                  (lvs_iota c)) +
         ((christoffel G (lvs_iota z) (lvs_iota a) (lvs_iota w))$3 *
          (christoffel G (lvs_iota z) (lvs_iota b) (lvs_iota c))$3 -
          (christoffel G (lvs_iota z) (lvs_iota b) (lvs_iota w))$3 *
          (christoffel G (lvs_iota z) (lvs_iota a) (lvs_iota c))$3) /
         (basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field {x:real^2 | lvs_iota x IN S} (lvs_hslice G)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LVS_HSLICE_METRIC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^2 | lvs_iota x IN S}`; `lvs_hslice (G:real^3->real^3^3)`;
                 `z:real^2`; `a:real^2`; `b:real^2`; `c:real^2`; `w:real^2`]
                LVS_LRIEMANN_LOWER) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `lvs_iota z`;
                 `lvs_iota a`; `lvs_iota b`; `lvs_iota c`; `lvs_iota w`]
                LVS_LRIEMANN_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `z:real^2`]
                LVS_DERIV_SLICE) THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `z:real^2`]
                LVS_QUAD_SLICE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Scalar curvature in orthonormal frames (with pc_rfa_pevol): in            *)
(* dimension 2, R = 2 R(f1,f2,f1,f2); in dimension 3,                        *)
(* R = 2 R(F1,F2,F1,F2) + 2 Ric(F3,F3).  The adapted frame (P f1, P f2, n)   *)
(* of a slice is G-orthonormal.                                              *)
(* ------------------------------------------------------------------------- *)

let LVS_SCALAR_FRAME2 = prove
 (`!U (h:real^2->real^2^2) z (S2:real^2^2).
     metric_field U h /\ z IN U /\ matrix_inv(h z) = transp S2 ** S2
     ==> lscalar h z =
         &2 * lrm4 h z (\m. if m = 1 then transp S2 ** basis 1
                            else if m = 2 then transp S2 ** basis 2
                            else if m = 3 then transp S2 ** basis 1
                            else transp S2 ** basis 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `h:real^2->real^2^2`; `z:real^2`;
                 `S2:real^2^2`] RFA_SCAL_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `h:real^2->real^2^2`; `z:real^2`;
                 `S2:real^2^2`] RFA_RIC_FRAME_RM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `h:real^2->real^2^2`; `z:real^2`]
                RFA_LRM4_ZERO12) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `h:real^2->real^2^2`; `z:real^2`;
                 `transp(S2:real^2^2) ** basis 2`;
                 `transp(S2:real^2^2) ** basis 1`] RFA_LRM4_SWAP_PAIRS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let LVS_SCALAR_FRAME3 = prove
 (`!U (G:real^3->real^3^3) y (S3:real^3^3).
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S3 ** S3
     ==> lscalar G y =
         &2 * lrm4 G y (\m. if m = 1 then transp S3 ** basis 1
                            else if m = 2 then transp S3 ** basis 2
                            else if m = 3 then transp S3 ** basis 1
                            else transp S3 ** basis 2) +
         &2 * lricci G y (transp S3 ** basis 3) (transp S3 ** basis 3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                 `S3:real^3^3`] RFA_SCAL_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                 `S3:real^3^3`] RFA_RIC_FRAME_RM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
                RFA_LRM4_ZERO12) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                 `transp(S3:real^3^3) ** basis 2`;
                 `transp(S3:real^3^3) ** basis 1`] RFA_LRM4_SWAP_PAIRS) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                 `transp(S3:real^3^3) ** basis 3`;
                 `transp(S3:real^3^3) ** basis 1`] RFA_LRM4_SWAP_PAIRS) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                 `transp(S3:real^3^3) ** basis 3`;
                 `transp(S3:real^3^3) ** basis 2`] RFA_LRM4_SWAP_PAIRS) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let LVS_GAMMA3_BILINEAR = prove
 (`!S (G:real^3->real^3^3) z p q.
     metric_field S G /\ lvs_iota z IN S
     ==> (christoffel G (lvs_iota z) (lvs_iota p) (lvs_iota q))$3 =
         p dot ((lambda a b. (christoffel G (lvs_iota z) (lvs_iota(basis a))
                                           (lvs_iota(basis b)))$3):real^2^2 ** q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `lvs_iota z`]
                CHRISTOFFEL_BILINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!v:real^2. lvs_iota v = v$1 % lvs_iota(basis 1) + v$2 % lvs_iota(basis 2)`
  (fun th -> SUBST1_TAC(SPEC `p:real^2` th) THEN SUBST1_TAC(SPEC `q:real^2` th)) THENL
   [GEN_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; LVS_IOTA_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP BILINEAR_LADD th;
                                    MATCH_MP BILINEAR_RADD th;
                                    MATCH_MP BILINEAR_LMUL th;
                                    MATCH_MP BILINEAR_RMUL th]) THEN
  SIMP_TAC[dot; matrix_vector_mul; LAMBDA_BETA; DIMINDEX_2; SUM_2; ARITH;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let LVS_G33_FACTS = prove
 (`!S (G:real^3->real^3^3) y.
     metric_field S G /\ y IN S
     ==> G y ** (matrix_inv(G y) ** basis 3) = basis 3 /\
         &0 < basis 3 dot (matrix_inv(G y) ** basis 3) /\
         (matrix_inv(G y) ** basis 3)$3 = basis 3 dot (matrix_inv(G y) ** basis 3) /\
         (!w. (matrix_inv(G y) ** basis 3) dot (G y ** w) = w$3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `transp((G:real^3->real^3^3) y) = G y /\
    (!v. ~(v = vec 0) ==> &0 < v dot (G y ** v))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible((G:real^3->real^3^3) y)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LVS_POSDEF_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(G:real^3->real^3^3) y ** (matrix_inv(G y) ** basis 3) = basis 3`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `basis 3 dot (matrix_inv((G:real^3->real^3^3) y) ** basis 3) =
      (matrix_inv(G y) ** basis 3) dot (G y ** (matrix_inv(G y) ** basis 3))`
    SUBST1_TAC THENL
     [REWRITE_TAC[ASSUME `(G:real^3->real^3^3) y ** (matrix_inv(G y) ** basis 3) =
                          basis 3`] THEN MATCH_ACCEPT_TAC DOT_SYM;
      ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `(G:real^3->real^3^3) y ** (matrix_inv(G y) ** basis 3) = basis 3` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN
    MESON_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH_RULE `1 <= 3 /\ 3 <= 3`];
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH];
    GEN_TAC THEN
    MP_TAC(ISPECL [`(G:real^3->real^3^3) y`;
                   `matrix_inv((G:real^3->real^3^3) y) ** basis 3`;
                   `w:real^3`] LVS_SYM_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]]);;

let LVS_SLICE_FRAMES = prove
 (`!S (G:real^3->real^3^3) z.
     metric_field S G /\ lvs_iota z IN S
     ==> ?S2:real^2^2 S3:real^3^3.
           invertible S2 /\ matrix_inv(lvs_hslice G z) = transp S2 ** S2 /\
           invertible S3 /\ matrix_inv(G(lvs_iota z)) = transp S3 ** S3 /\
           transp S3 ** basis 1 = lvs_iota(transp S2 ** basis 1) /\
           transp S3 ** basis 2 = lvs_iota(transp S2 ** basis 2) /\
           transp S3 ** basis 3 =
             inv(sqrt(basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))) %
             (matrix_inv(G(lvs_iota z)) ** basis 3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field {x:real^2 | lvs_iota x IN S} (lvs_hslice G)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LVS_HSLICE_METRIC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^2 | lvs_iota x IN S}`; `lvs_hslice (G:real^3->real^3^3)`;
                 `z:real^2`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `S2:real^2^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `invertible(lvs_hslice (G:real^3->real^3^3) z)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{x:real^2 | lvs_iota x IN S}`;
                   `lvs_hslice (G:real^3->real^3^3)`; `z:real^2`]
                  LRG_METRIC_INVERTIBLE) THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `lvs_iota z`]
                LVS_G33_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `nu = matrix_inv((G:real^3->real^3^3)(lvs_iota z)) ** basis 3` THEN
  ABBREV_TAC `g33 = basis 3 dot (nu:real^3)` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
          ==> lvs_iota(transp (S2:real^2^2) ** basis i) dot
              ((G:real^3->real^3^3)(lvs_iota z) ** lvs_iota(transp S2 ** basis j)) =
              if i = j then &1 else &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LVS_HSLICE_DOT] THEN
    MATCH_MP_TAC RFA_GFRAME_ORTHO THEN ASM_REWRITE_TAC[DIMINDEX_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. lvs_iota(transp (S2:real^2^2) ** basis i) dot
        ((G:real^3->real^3^3)(lvs_iota z) ** (inv(sqrt g33) % nu)) = &0`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH; LVS_IOTA_COMPONENT; REAL_MUL_RZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3)(lvs_iota z)`;
                 `lvs_iota(transp (S2:real^2^2) ** basis 1)`;
                 `lvs_iota(transp (S2:real^2^2) ** basis 2)`;
                 `inv(sqrt g33) % (nu:real^3)`] RFA_ORTHO3_MATRIX) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ARITH] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[LRG_METRIC_SYM]; ALL_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `a * a * b = (a * a) * b`; GSYM REAL_INV_MUL] THEN
    ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_LT_IMP_LE; REAL_MUL_LINV;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S3:real^3^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`S2:real^2^2`; `S3:real^3^3`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The local scalar Gauss equation.  lvs_IIloc G z is the second             *)
(* fundamental form Hess(y3)(Pa,Pb) / |grad y3| = -gamma(a,b)/sqrt g33 on    *)
(* the slice basis; det(h^-1 II) is the determinant of the shape operator.   *)
(* ------------------------------------------------------------------------- *)

let lvs_IIloc = new_definition
 `lvs_IIloc (G:real^3->real^3^3) (z:real^2) =
    (lambda a b. --((christoffel G (lvs_iota z) (lvs_iota(basis a))
                                   (lvs_iota(basis b)))$3) /
                 sqrt(basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))):real^2^2`;;

let LVS_DET_SLICE = prove
 (`!S (G:real^3->real^3^3) z (S2:real^2^2).
     metric_field S G /\ lvs_iota z IN S /\
     matrix_inv(lvs_hslice G z) = transp S2 ** S2
     ==> ((christoffel G (lvs_iota z) (lvs_iota(transp S2 ** basis 1))
                          (lvs_iota(transp S2 ** basis 1)))$3 *
          (christoffel G (lvs_iota z) (lvs_iota(transp S2 ** basis 2))
                          (lvs_iota(transp S2 ** basis 2)))$3 -
          (christoffel G (lvs_iota z) (lvs_iota(transp S2 ** basis 2))
                          (lvs_iota(transp S2 ** basis 1)))$3 *
          (christoffel G (lvs_iota z) (lvs_iota(transp S2 ** basis 1))
                          (lvs_iota(transp S2 ** basis 2)))$3) /
         (basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3)) =
         det(matrix_inv(lvs_hslice G z) ** lvs_IIloc G z)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `Bm = (lambda a b. (christoffel (G:real^3->real^3^3) (lvs_iota z)
                         (lvs_iota(basis a)) (lvs_iota(basis b)))$3):real^2^2` THEN
  SUBGOAL_THEN
   `!s t. 1 <= s /\ s <= 2 /\ 1 <= t /\ t <= 2
          ==> (christoffel (G:real^3->real^3^3) (lvs_iota z)
                 (lvs_iota(transp S2 ** basis s)) (lvs_iota(transp S2 ** basis t)))$3 =
              (((S2:real^2^2) ** Bm) ** transp S2)$s$t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `z:real^2`;
                   `transp(S2:real^2^2) ** basis s`; `transp(S2:real^2^2) ** basis t`]
                  LVS_GAMMA3_BILINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_2; MATRIX_VECTOR_MUL_BASIS] THEN
    ASM_SIMP_TAC[column; LAMBDA_BETA; DIMINDEX_2];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH] THEN
  SUBGOAL_THEN
   `(((S2:real^2^2) ** Bm) ** transp S2)$1$1 * ((S2 ** Bm) ** transp S2)$2$2 -
    ((S2 ** Bm) ** transp S2)$2$1 * ((S2 ** Bm) ** transp S2)$1$2 =
    det(((S2:real^2^2) ** (Bm:real^2^2)) ** transp S2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[DET_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `lvs_IIloc (G:real^3->real^3^3) z =
    (--inv(sqrt(basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3)))) %% Bm`
  SUBST1_TAC THENL
   [REWRITE_TAC[lvs_IIloc] THEN EXPAND_TAC "Bm" THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_CMUL_COMPONENT; DIMINDEX_2] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DET_MUL; DET_CMUL; DET_TRANSP; DIMINDEX_2] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `lvs_iota z`]
                LVS_G33_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `g33 = basis 3 dot (matrix_inv((G:real^3->real^3^3)(lvs_iota z)) **
                                 basis 3)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `sqrt g33 pow 2 = g33` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt g33` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `sqrt g33 pow 2 = g33` THEN UNDISCH_TAC `&0 < sqrt g33` THEN
  CONV_TAC REAL_FIELD);;

let LVS_LOCAL_GAUSS = prove
 (`!S (G:real^3->real^3^3) z.
     metric_field S G /\ lvs_iota z IN S
     ==> lscalar (lvs_hslice G) z =
         lscalar G (lvs_iota z) -
         &2 * lricci G (lvs_iota z)
               (inv(sqrt(basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))) %
                (matrix_inv(G(lvs_iota z)) ** basis 3))
               (inv(sqrt(basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))) %
                (matrix_inv(G(lvs_iota z)) ** basis 3)) +
         &2 * det(matrix_inv(lvs_hslice G z) ** lvs_IIloc G z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `z:real^2`]
                LVS_SLICE_FRAMES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S2:real^2^2` (X_CHOOSE_THEN `S3:real^3^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `metric_field {x:real^2 | lvs_iota x IN S} (lvs_hslice G)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LVS_HSLICE_METRIC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{x:real^2 | lvs_iota x IN S}`; `lvs_hslice (G:real^3->real^3^3)`;
                 `z:real^2`; `S2:real^2^2`] LVS_SCALAR_FRAME2) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `lvs_iota z`;
                 `S3:real^3^3`] LVS_SCALAR_FRAME3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lrm4] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `z:real^2`;
                 `transp(S2:real^2^2) ** basis 1`; `transp(S2:real^2^2) ** basis 2`;
                 `transp(S2:real^2^2) ** basis 2`; `transp(S2:real^2^2) ** basis 1`]
                LVS_HSLICE_RIEMANN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `z:real^2`;
                 `S2:real^2^2`] LVS_DET_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hessians.  cmp_lhess in coordinates; the Hessian and the squared          *)
(* gradient of the coordinate function u + y3 (Hess = -Gamma^3,              *)
(* |grad|^2 = g33); the Hessian of a restriction f o lvs_iota for the slice  *)
(* metric is the tangential Hessian of f plus (gamma/g33) df(nu).            *)
(* ------------------------------------------------------------------------- *)

let LVS_LHESS_D = prove
 (`!(G:real^N->real^N^N) f y a b.
     cmp_lhess G f y a b =
     drop(frechet_derivative (\x. frechet_derivative (\w. lift(f w)) (at x) a)
                             (at y) b) -
     drop(frechet_derivative (\x. lift(f x)) (at y) (christoffel G y b a))`,
  REWRITE_TAC[cmp_lhess; LRG_LNABLA_EQ; SUM_SING_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LIFT_DROP; ETA_AX]);;

let LVS_AFFINE3_DERIV = prove
 (`!u (x:real^3). frechet_derivative (\w:real^3. lift(u + w$3)) (at x) =
                  (\h. lift(h$3))`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN REWRITE_TAC[LIFT_ADD] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ABS_CONV) [GSYM VECTOR_ADD_LID] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT]);;

let LVS_LHESS_Y3 = prove
 (`!U (G:real^3->real^3^3) y u a b.
     metric_field U G /\ y IN U
     ==> cmp_lhess G (\w. u + w$3) y a b = --((christoffel G y a b)$3)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LVS_LHESS_D; LVS_AFFINE3_DERIV] THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_CONST_AT; LIFT_DROP; DROP_VEC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                 `b:real^3`; `a:real^3`] CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let LVS_LGRAD2_Y3 = prove
 (`!(G:real^3->real^3^3) y u.
     lgrad2 G (\w. u + w$3) y = basis 3 dot (matrix_inv(G y) ** basis 3)`,
  REWRITE_TAC[lgrad2; LVS_AFFINE3_DERIV; LIFT_DROP] THEN
  SIMP_TAC[DIMINDEX_3; SUM_3; BASIS_COMPONENT; ARITH; DOT_BASIS;
           MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA] THEN
  REAL_ARITH_TAC);;

let LVS_LOCAL_HESS = prove
 (`!S (G:real^3->real^3^3) f z a b.
     metric_field S G /\ lvs_iota z IN S /\ smooth_map_on S (\y. lift(f y))
     ==> cmp_lhess (lvs_hslice G) (\x. f(lvs_iota x)) z a b =
         cmp_lhess G f (lvs_iota z) (lvs_iota a) (lvs_iota b) +
         ((christoffel G (lvs_iota z) (lvs_iota b) (lvs_iota a))$3 /
          (basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))) *
         drop(frechet_derivative (\x. lift(f x)) (at (lvs_iota z))
                                 (matrix_inv(G(lvs_iota z)) ** basis 3))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LVS_LHESS_D] THEN
  SUBGOAL_THEN `open (S:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ABBREV_TAC `S2 = {x:real^2 | lvs_iota x IN S}` THEN
  SUBGOAL_THEN `open (S2:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S2" THEN ASM_SIMP_TAC[LVS_OPEN_IOTA_PREIMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2) IN S2` ASSUME_TAC THENL
   [EXPAND_TAC "S2" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p v. p IN S2
          ==> frechet_derivative (\w. lift((f:real^3->real)(lvs_iota w))) (at p) v =
              frechet_derivative (\x. lift(f x)) (at (lvs_iota p)) (lvs_iota v)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `((\w. lift((f:real^3->real)(lvs_iota w))) has_derivative
       (frechet_derivative (\x. lift(f x)) (at (lvs_iota p)) o lvs_iota)) (at p)`
    MP_TAC THENL
     [SUBGOAL_THEN
       `(\w. lift((f:real^3->real)(lvs_iota w))) = (\x. lift(f x)) o lvs_iota`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN
      SIMP_TAC[HAS_DERIVATIVE_LINEAR; LVS_IOTA_LINEAR] THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(p:real^2) IN S2` THEN EXPAND_TAC "S2" THEN
      SIMP_TAC[IN_ELIM_THM];
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      REWRITE_TAC[o_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative
      (\x. frechet_derivative (\w. lift((f:real^3->real)(lvs_iota w))) (at x) a)
      (at z) b =
    frechet_derivative
      (\x. frechet_derivative (\w. lift(f w)) (at x) (lvs_iota a))
      (at (lvs_iota z)) (lvs_iota b)`
  SUBST1_TAC THENL
   [ABBREV_TAC
     `Dfa = \y:real^3. frechet_derivative (\w. lift((f:real^3->real) w)) (at y)
                                          (lvs_iota a)` THEN
    SUBGOAL_THEN
     `frechet_derivative
        (\x. frechet_derivative (\w. lift((f:real^3->real)(lvs_iota w))) (at x) a)
        (at z) =
      frechet_derivative ((Dfa:real^3->real^1) o lvs_iota) (at z)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `S2:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EXPAND_TAC "Dfa" THEN
      REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(((Dfa:real^3->real^1) o lvs_iota) has_derivative
       (frechet_derivative Dfa (at (lvs_iota z)) o lvs_iota)) (at z)`
    MP_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN
      SIMP_TAC[HAS_DERIVATIVE_LINEAR; LVS_IOTA_LINEAR] THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "Dfa" THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      REWRITE_TAC[o_THM] THEN EXPAND_TAC "Dfa" THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (\x. lift((f:real^3->real) x)) (at (lvs_iota z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(frechet_derivative (\x. lift((f:real^3->real) x)) (at (lvs_iota z))
          (christoffel G (lvs_iota z) (lvs_iota b) (lvs_iota a))) =
    drop(frechet_derivative (\x. lift(f x)) (at (lvs_iota z))
          (lvs_iota(christoffel (lvs_hslice G) z b a))) +
    ((christoffel G (lvs_iota z) (lvs_iota b) (lvs_iota a))$3 /
     (basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))) *
    drop(frechet_derivative (\x. lift(f x)) (at (lvs_iota z))
          (matrix_inv(G(lvs_iota z)) ** basis 3))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `z:real^2`;
                   `b:real^2`; `a:real^2`] LVS_CHRISTOFFEL_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th;
                                      MATCH_MP LINEAR_CMUL th]) THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;


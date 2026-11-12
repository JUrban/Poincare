(* ========================================================================= *)
(* Unit pc_rfa_p3alg: pointwise linear algebra of the 3D curvature tensor    *)
(* P = (R/2) g - Ric (lpcurv): the sectional curvatures at a point are       *)
(* exactly the values P(w,w) at G-unit w, and in an eigenframe of Ric        *)
(* ordered by the values of P, the first frame vector is a minimizing        *)
(* eigenvector: P(f1,f1) is the minimal sectional curvature.                 *)
(* ========================================================================= *)

needs "src/pc_rfa_raylap.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* Invariances of lsectional (swap, scaling, Gram-Schmidt).                  *)
(* ========================================================================= *)

(* Invariances of the sectional curvature of a plane under change of basis *)

let RFA_LSECTIONAL_SWAP = prove
 (`!U (G:real^N->real^N^N) y u v.
     metric_field U G /\ y IN U ==> lsectional G y u v = lsectional G y v u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lsectional] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `u:real^N`; `v:real^N`; `u:real^N`] LRIEMANN_ANTISYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `u:real^N`; `v:real^N`; `u:real^N`; `v:real^N`]
         LRIEMANN_METRIC_ANTISYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `u:real^N`; `v:real^N`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_RNEG; REAL_NEG_NEG] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

let RFA_LSECTIONAL_LSCALE = prove
 (`!U (G:real^N->real^N^N) y u v c.
     metric_field U G /\ y IN U /\ ~(c = &0)
     ==> lsectional G y (c % u) v = lsectional G y u v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lsectional] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `v:real^N`] o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o SPECL [`c:real`; `u:real^N`] o MATCH_MP LINEAR_CMUL) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  ABBREV_TAC `n = u dot ((G:real^N->real^N^N) y ** lriemann G y u v v)` THEN
  ABBREV_TAC `a = u dot ((G:real^N->real^N^N) y ** u)` THEN
  ABBREV_TAC `b = v dot ((G:real^N->real^N^N) y ** v)` THEN
  ABBREV_TAC `d = u dot ((G:real^N->real^N^N) y ** v)` THEN
  ASM_CASES_TAC `a * b - d pow 2 = &0` THENL
   [SUBGOAL_THEN `(c * c * a) * b - (c * d) pow 2 = &0` SUBST1_TAC THENL
     [UNDISCH_TAC `a * b - d pow 2 = &0` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO];
    UNDISCH_TAC `~(a * b - d pow 2 = &0)` THEN UNDISCH_TAC `~(c = &0)` THEN
    CONV_TAC REAL_FIELD]);;

let RFA_LSECTIONAL_RSCALE = prove
 (`!U (G:real^N->real^N^N) y u v c.
     metric_field U G /\ y IN U /\ ~(c = &0)
     ==> lsectional G y u (c % v) = lsectional G y u v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         RFA_LSECTIONAL_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_LSECTIONAL_LSCALE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* Gram-Schmidt for a plane: a G-orthonormal basis with the same sectional *)
(* curvature.                                                               *)

let RFA_GS_ORTHO = prove
 (`!U (G:real^N->real^N^N) y u v.
     metric_field U G /\ y IN U /\ ~collinear {vec 0,u,v}
     ==> ?u1 v1. u1 dot (G y ** u1) = &1 /\ v1 dot (G y ** v1) = &1 /\
                 u1 dot (G y ** v1) = &0 /\
                 lsectional G y u1 v1 = lsectional G y u v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  ABBREV_TAC `a = u dot ((G:real^N->real^N^N) y ** u)` THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w = v - ((u dot ((G:real^N->real^N^N) y ** v)) / a) % u` THEN
  SUBGOAL_THEN `u dot ((G:real^N->real^N^N) y ** w) = &0` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                DOT_RSUB; DOT_RMUL] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w:real^N = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `b = w dot ((G:real^N->real^N^N) y ** w)` THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `inv(sqrt a) % (u:real^N)` THEN
  EXISTS_TAC `inv(sqrt b) % (w:real^N)` THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  SUBGOAL_THEN `~(inv(sqrt a) = &0) /\ ~(inv(sqrt b) = &0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_EQ_0] THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
    ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_LT_IMP_LE; REAL_MUL_LINV;
                 REAL_LT_IMP_NZ];
    REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
    ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_LT_IMP_LE; REAL_MUL_LINV;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `u:real^N`; `inv(sqrt b) % (w:real^N)`; `inv(sqrt a)`]
         RFA_LSECTIONAL_LSCALE) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `u:real^N`; `w:real^N`; `inv(sqrt b)`] RFA_LSECTIONAL_RSCALE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "w" THEN MATCH_MP_TAC LSECTIONAL_SHEAR THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* In dimension 3 every G-orthonormal pair extends to a triple,              *)
(* and the sectional curvatures are exactly the values P(w,w), w G-unit.     *)
(* ========================================================================= *)

(* In dimension 3, a G-orthonormal pair extends to a G-orthonormal triple   *)
(* (the third vector is G^-1 of the Euclidean cross product, normalized).   *)

let RFA_CROSS3_ZERO = prove
 (`!u v:real^3.
     vector[u$2 * v$3 - u$3 * v$2; u$3 * v$1 - u$1 * v$3; u$1 * v$2 - u$2 * v$1]:real^3 =
     vec 0 /\ ~(u = vec 0)
     ==> ?c. v = c % u`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `(u:real^3)$1 = &0` THENL
   [ASM_CASES_TAC `(u:real^3)$2 = &0` THENL
     [EXISTS_TAC `(v:real^3)$3 / (u:real^3)$3` THEN
      SUBGOAL_THEN `~((u:real^3)$3 = &0)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
      EXISTS_TAC `(v:real^3)$2 / (u:real^3)$2` THEN
      REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD];
    EXISTS_TAC `(v:real^3)$1 / (u:real^3)$1` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD]);;

let RFA_NORMAL3 = prove
 (`!U (G:real^3->real^3^3) y u v.
     metric_field U G /\ y IN U /\
     u dot (G y ** u) = &1 /\ v dot (G y ** v) = &1 /\ u dot (G y ** v) = &0
     ==> ?w. w dot (G y ** w) = &1 /\ u dot (G y ** w) = &0 /\
             v dot (G y ** w) = &0`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `n = vector[(u:real^3)$2 * (v:real^3)$3 - u$3 * v$2;
                         u$3 * v$1 - u$1 * v$3; u$1 * v$2 - u$2 * v$1]:real^3` THEN
  SUBGOAL_THEN `(u:real^3) dot n = &0 /\ (v:real^3) dot n = &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[DOT_3; VECTOR_3] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`u:real^3`; `v:real^3`] RFA_CROSS3_ZERO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `(u:real^3) dot ((G:real^3->real^3^3) y ** u) = &1` THEN
      ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `(u:real^3) dot ((G:real^3->real^3^3) y ** c % u) = &0` THEN
    UNDISCH_TAC `(c % u:real^3) dot ((G:real^3->real^3^3) y ** c % u) = &1` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible((G:real^3->real^3^3) y)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
           LRG_METRIC_INVERTIBLE) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w' = matrix_inv((G:real^3->real^3^3) y) ** n` THEN
  SUBGOAL_THEN `(G:real^3->real^3^3) y ** w' = n` ASSUME_TAC THENL
   [EXPAND_TAC "w'" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w':real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(G:real^3->real^3^3) y ** w' = n` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  ABBREV_TAC `b = (w':real^3) dot n` THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th] THEN
                            ASSUME_TAC th) THEN
    MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `inv(sqrt b) % (w':real^3)` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL; REAL_MUL_RZERO] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_LT_IMP_LE; REAL_MUL_LINV;
               REAL_LT_IMP_NZ]);;

(* In dimension 3 the sectional curvatures are exactly the values P(w,w)    *)
(* of P = lpcurv G at G-unit vectors w (the unit normals of the planes).    *)

let RFA_ORTHO_NONCOLLINEAR = prove
 (`!(G0:real^N^N) u v.
     u dot (G0 ** u) = &1 /\ v dot (G0 ** v) = &1 /\ u dot (G0 ** v) = &0
     ==> ~collinear {vec 0,u,v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[COLLINEAR_LEMMA] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(u:real^N) dot ((G0:real^N^N) ** u) = &1` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN UNDISCH_TAC `(v:real^N) dot ((G0:real^N^N) ** v) = &1` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    X_GEN_TAC `c:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(u:real^N) dot ((G0:real^N^N) ** v) = &0` THEN
    UNDISCH_TAC `(v:real^N) dot ((G0:real^N^N) ** v) = &1` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
    CONV_TAC REAL_RING]);;

let RFA_SEC_AS_PCURV = prove
 (`!U (G:real^3->real^3^3) y u v.
     metric_field U G /\ y IN U /\ ~collinear {vec 0,u,v}
     ==> ?w. w dot (G y ** w) = &1 /\ lsectional G y u v = lpcurv G y (\m. w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                 `u:real^3`; `v:real^3`] RFA_GS_ORTHO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `v1:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                 `u1:real^3`; `v1:real^3`] RFA_NORMAL3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `lsectional (G:real^3->real^3^3) y u1 v1 = lsectional G y u v` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RFA_LSECTIONAL_PCURV_3D THEN EXISTS_TAC `U:real^3->bool` THEN
  ASM_REWRITE_TAC[]);;

let RFA_NONCOLLINEAR_BASIS3 = prove
 (`!w:real^3. ~(w = vec 0)
              ==> ~collinear {vec 0,w,basis 1} \/ ~collinear {vec 0,w,basis 2}`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[COLLINEAR_LEMMA] THEN
  ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[GSYM DE_MORGAN_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `c1:real`) (X_CHOOSE_TAC `c2:real`)) THEN
  SUBGOAL_THEN
   `(basis 1:real^3)$1 = c1 * (w:real^3)$1 /\ (basis 1:real^3)$2 = c1 * w$2 /\
    (basis 2:real^3)$1 = c2 * w$1 /\ (basis 2:real^3)$2 = c2 * w$2`
  MP_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT]; ALL_TAC] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN CONV_TAC REAL_RING);;

let RFA_PCURV_AS_SEC = prove
 (`!U (G:real^3->real^3^3) y w.
     metric_field U G /\ y IN U /\ w dot (G y ** w) = &1
     ==> ?u v. ~collinear {vec 0,u,v} /\ lsectional G y u v = lpcurv G y (\m. w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(w:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(w:real^3) dot ((G:real^3->real^3^3) y ** w) = &1` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^3. ~collinear {vec 0,w,z}` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP RFA_NONCOLLINEAR_BASIS3) THENL
     [EXISTS_TAC `basis 1:real^3`; EXISTS_TAC `basis 2:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `z' = z - (w dot ((G:real^3->real^3^3) y ** z)) % (w:real^3)` THEN
  SUBGOAL_THEN `(w:real^3) dot ((G:real^3->real^3^3) y ** z') = &0` ASSUME_TAC THENL
   [EXPAND_TAC "z'" THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                    DOT_RSUB; DOT_RMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z':real^3 = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "z'" THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN DISCH_TAC THEN
    UNDISCH_TAC `~collinear {vec 0:real^3,w,z}` THEN
    REWRITE_TAC[COLLINEAR_LEMMA] THEN DISJ2_TAC THEN DISJ2_TAC THEN
    EXISTS_TAC `(w:real^3) dot ((G:real^3->real^3^3) y ** z)` THEN
    FIRST_X_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `b = (z':real^3) dot ((G:real^3->real^3^3) y ** z')` THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `u = inv(sqrt b) % (z':real^3)` THEN
  SUBGOAL_THEN `(u:real^3) dot ((G:real^3->real^3^3) y ** u) = &1 /\
                (w:real^3) dot (G y ** u) = &0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL; REAL_MUL_RZERO] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
    ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_LT_IMP_LE; REAL_MUL_LINV;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                 `w:real^3`; `u:real^3`] RFA_NORMAL3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_ORTHO_NONCOLLINEAR THEN
    EXISTS_TAC `(G:real^3->real^3^3) y` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_LSECTIONAL_PCURV_3D THEN EXISTS_TAC `U:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
         LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;

let RFA_SECSET_3D = prove
 (`!U (G:real^3->real^3^3) y.
     metric_field U G /\ y IN U
     ==> {lsectional G y u v | u,v | ~collinear {vec 0,u,v}} =
         {lpcurv G y (\m. w) | w | w dot (G y ** w) = &1}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                   `u:real^3`; `v:real^3`] RFA_SEC_AS_PCURV) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                   `w:real^3`] RFA_PCURV_AS_SEC) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;


(* ========================================================================= *)
(* Frame expansions, the ordered eigenframe and the minimal                  *)
(* sectional curvature P(f1,f1).                                             *)
(* ========================================================================= *)

(* Expansions in a G-orthonormal frame f_a = transp S ** basis a (3D).     *)

let RFA_LPCURV_BIL = prove
 (`!(G:real^N->real^N^N) y v w.
     lpcurv G y (\m. if m = 1 then v else w) =
     lscalar G y / &2 * (v dot (G y ** w)) - lricci G y v w`,
  REWRITE_TAC[lpcurv; lmetric2; lric2; ARITH]);;

let RFA_LPCURV_DIAG = prove
 (`!(G:real^N->real^N^N) y w.
     lpcurv G y (\m. w) = lscalar G y / &2 * (w dot (G y ** w)) - lricci G y w w`,
  REWRITE_TAC[lpcurv; lmetric2; lric2]);;

let RFA_FRAME3_DOT = prove
 (`!(G0:real^3^3) (S:real^3^3) v w.
     invertible G0 /\ invertible S /\ matrix_inv G0 = transp S ** S
     ==> v dot (G0 ** w) =
         ((transp S ** basis 1) dot (G0 ** v)) * ((transp S ** basis 1) dot (G0 ** w)) +
         ((transp S ** basis 2) dot (G0 ** v)) * ((transp S ** basis 2) dot (G0 ** w)) +
         ((transp S ** basis 3) dot (G0 ** v)) * ((transp S ** basis 3) dot (G0 ** w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G0:real^3^3`; `S:real^3^3`; `\v w:real^3. v dot ((G0:real^3^3) ** w)`;
                 `v:real^3`; `w:real^3`] RFA_BILIN_FRAME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RFA_LIFT_DOT_GMUL_LINEAR] THEN GEN_TAC THEN
    ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3] THEN
  ASM_SIMP_TAC[RFA_GFRAME_ORTHO; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

let RFA_FRAME3_RIC = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) v w.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
            ==> lricci G y (transp S ** basis i) (transp S ** basis j) = &0)
     ==> lricci G y v w =
         ((transp S ** basis 1) dot (G y ** v)) * ((transp S ** basis 1) dot (G y ** w)) *
         lricci G y (transp S ** basis 1) (transp S ** basis 1) +
         ((transp S ** basis 2) dot (G y ** v)) * ((transp S ** basis 2) dot (G y ** w)) *
         lricci G y (transp S ** basis 2) (transp S ** basis 2) +
         ((transp S ** basis 3) dot (G y ** v)) * ((transp S ** basis 3) dot (G y ** w)) *
         lricci G y (transp S ** basis 3) (transp S ** basis 3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
         LRG_METRIC_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`;
                 `lricci (G:real^3->real^3^3) y`; `v:real^3`; `w:real^3`]
         RFA_BILIN_FRAME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
           LRG_LRICCI_LINEAR) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIMINDEX_3; SUM_3] THEN
  ASM_SIMP_TAC[ARITH] THEN REAL_ARITH_TAC);;

let RFA_FRAME3_P = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) v w.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
            ==> lricci G y (transp S ** basis i) (transp S ** basis j) = &0)
     ==> lpcurv G y (\m. if m = 1 then v else w) =
         ((transp S ** basis 1) dot (G y ** v)) * ((transp S ** basis 1) dot (G y ** w)) *
         lpcurv G y (\m. transp S ** basis 1) +
         ((transp S ** basis 2) dot (G y ** v)) * ((transp S ** basis 2) dot (G y ** w)) *
         lpcurv G y (\m. transp S ** basis 2) +
         ((transp S ** basis 3) dot (G y ** v)) * ((transp S ** basis 3) dot (G y ** w)) *
         lpcurv G y (\m. transp S ** basis 3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
         LRG_METRIC_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[RFA_LPCURV_BIL; RFA_LPCURV_DIAG] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                 `v:real^3`; `w:real^3`] RFA_FRAME3_RIC) THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `v:real^3`; `w:real^3`]
         RFA_FRAME3_DOT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ASM_SIMP_TAC[RFA_GFRAME_ORTHO; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

(* An eigenframe of Ric (hence of P) ordered so that P(f1,f1) is minimal.  *)

let RFA_PERM_FRAME3 = prove
 (`!U (G:real^3->real^3^3) y (S0:real^3^3) a b c.
     metric_field U G /\ y IN U /\ invertible S0 /\ matrix_inv(G y) = transp S0 ** S0 /\
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
            ==> lricci G y (transp S0 ** basis i) (transp S0 ** basis j) = &0) /\
     1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 /\
     ~(a = b) /\ ~(a = c) /\ ~(b = c)
     ==> ?S:real^3^3. invertible S /\ matrix_inv(G y) = transp S ** S /\
           (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
                  ==> lricci G y (transp S ** basis i) (transp S ** basis j) = &0) /\
           transp S ** basis 1 = transp S0 ** basis a /\
           transp S ** basis 2 = transp S0 ** basis b /\
           transp S ** basis 3 = transp S0 ** basis c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP LRG_METRIC_INVERTIBLE
    (CONJ (ASSUME `metric_field U (G:real^3->real^3^3)`) (ASSUME `(y:real^3) IN U`))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `transp(S0:real^3^3) ** basis a`;
                 `transp(S0:real^3^3) ** basis b`; `transp(S0:real^3^3) ** basis c`]
         RFA_ORTHO3_MATRIX) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RFA_GFRAME_ORTHO; DIMINDEX_3] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
           LRG_METRIC_SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `S:real^3^3` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(i = 1 \/ i = 2 \/ i = 3) /\ (j = 1 \/ j = 2 \/ j = 3)`
  MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let RFA_P3_EIGENFRAME = prove
 (`!U (G:real^3->real^3^3) y.
     metric_field U G /\ y IN U
     ==> ?S:real^3^3. invertible S /\ matrix_inv(G y) = transp S ** S /\
           (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
                  ==> lricci G y (transp S ** basis i) (transp S ** basis j) = &0) /\
           lpcurv G y (\m. transp S ** basis 1) <= lpcurv G y (\m. transp S ** basis 2) /\
           lpcurv G y (\m. transp S ** basis 1) <= lpcurv G y (\m. transp S ** basis 3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
         RFA_RIC_EIGENFRAME) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `S0:real^3^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `p1 = lpcurv (G:real^3->real^3^3) y (\m. transp(S0:real^3^3) ** basis 1)` THEN
  ABBREV_TAC `p2 = lpcurv (G:real^3->real^3^3) y (\m. transp(S0:real^3^3) ** basis 2)` THEN
  ABBREV_TAC `p3 = lpcurv (G:real^3->real^3^3) y (\m. transp(S0:real^3^3) ** basis 3)` THEN
  SUBGOAL_THEN
   `!a b c. 1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3 /\ 1 <= c /\ c <= 3 /\
            ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
            lpcurv (G:real^3->real^3^3) y (\m. transp(S0:real^3^3) ** basis a) <=
            lpcurv G y (\m. transp(S0:real^3^3) ** basis b) /\
            lpcurv G y (\m. transp(S0:real^3^3) ** basis a) <= lpcurv G y (\m. transp(S0:real^3^3) ** basis c)
            ==> ?S:real^3^3. invertible S /\ matrix_inv(G y) = transp S ** S /\
                  (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
                         ==> lricci G y (transp S ** basis i) (transp S ** basis j) = &0) /\
                  lpcurv G y (\m. transp S ** basis 1) <=
                  lpcurv G y (\m. transp S ** basis 2) /\
                  lpcurv G y (\m. transp S ** basis 1) <=
                  lpcurv G y (\m. transp S ** basis 3)`
  MATCH_MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S0:real^3^3`;
                   `a:num`; `b:num`; `c:num`] RFA_PERM_FRAME3) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `S:real^3^3` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `p1 <= p2 /\ p1 <= p3` THENL
   [MAP_EVERY EXISTS_TAC [`1`; `2`; `3`] THEN ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  ASM_CASES_TAC `p2 <= p1 /\ p2 <= p3` THENL
   [MAP_EVERY EXISTS_TAC [`2`; `1`; `3`] THEN ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`3`; `1`; `2`] THEN ASM_REWRITE_TAC[ARITH] THEN
  ASM_REAL_ARITH_TAC);;

(* The first frame vector of an ordered eigenframe is a minimizing unit   *)
(* eigenvector of P: P(f1,f1) <= P(w,w) for G-unit w, P(v,f1) =             *)
(* P(f1,f1) g(v,f1), and P(f1,f1) is the minimal sectional curvature.       *)

let RFA_P3_MIN_PROPS = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3).
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
            ==> lricci G y (transp S ** basis i) (transp S ** basis j) = &0) /\
     lpcurv G y (\m. transp S ** basis 1) <= lpcurv G y (\m. transp S ** basis 2) /\
     lpcurv G y (\m. transp S ** basis 1) <= lpcurv G y (\m. transp S ** basis 3)
     ==> (transp S ** basis 1) dot (G y ** (transp S ** basis 1)) = &1 /\
         (!w. w dot (G y ** w) = &1
              ==> lpcurv G y (\m. transp S ** basis 1) <= lpcurv G y (\m. w)) /\
         (!v. lpcurv G y (\m. if m = 1 then v else transp S ** basis 1) =
              lpcurv G y (\m. transp S ** basis 1) *
              (v dot (G y ** (transp S ** basis 1))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP LRG_METRIC_INVERTIBLE
    (CONJ (ASSUME `metric_field U (G:real^3->real^3^3)`) (ASSUME `(y:real^3) IN U`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> (transp(S:real^3^3) ** basis i) dot ((G:real^3->real^3^3) y ** (transp(S:real^3^3) ** basis j)) =
              if i = j then &1 else &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_GFRAME_ORTHO THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[ARITH];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `w:real^3`; `w:real^3`]
           RFA_FRAME3_DOT) THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `w:real^3`; `w:real^3`] RFA_FRAME3_P) THEN
    ASM_REWRITE_TAC[COND_ID] THEN DISCH_THEN SUBST1_TAC THEN
    ABBREV_TAC `c1 = (transp(S:real^3^3) ** basis 1) dot ((G:real^3->real^3^3) y ** w)` THEN
    ABBREV_TAC `c2 = (transp(S:real^3^3) ** basis 2) dot ((G:real^3->real^3^3) y ** w)` THEN
    ABBREV_TAC `c3 = (transp(S:real^3^3) ** basis 3) dot ((G:real^3->real^3^3) y ** w)` THEN
    ABBREV_TAC `p1 = lpcurv (G:real^3->real^3^3) y (\m. transp(S:real^3^3) ** basis 1)` THEN
    ABBREV_TAC `p2 = lpcurv (G:real^3->real^3^3) y (\m. transp(S:real^3^3) ** basis 2)` THEN
    ABBREV_TAC `p3 = lpcurv (G:real^3->real^3^3) y (\m. transp(S:real^3^3) ** basis 3)` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `c1 * c1 * p1 + c2 * c2 * p2 + c3 * c3 * p3 - p1 =
                  c2 pow 2 * (p2 - p1) + c3 pow 2 * (p3 - p1)` ASSUME_TAC THENL
     [UNDISCH_TAC `&1 = c1 * c1 + c2 * c2 + c3 * c3` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= c2 pow 2 * (p2 - p1) /\ &0 <= c3 pow 2 * (p3 - p1)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    X_GEN_TAC `v:real^3` THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `v:real^3`; `transp(S:real^3^3) ** basis 1:real^3`] RFA_FRAME3_P) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[ARITH] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                   `transp(S:real^3^3) ** basis 1:real^3`; `v:real^3`] LRG_METRIC_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

let RFA_SECMIN_FRAME_3D = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3).
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
            ==> lricci G y (transp S ** basis i) (transp S ** basis j) = &0) /\
     lpcurv G y (\m. transp S ** basis 1) <= lpcurv G y (\m. transp S ** basis 2) /\
     lpcurv G y (\m. transp S ** basis 1) <= lpcurv G y (\m. transp S ** basis 3)
     ==> (!u v. ~collinear {vec 0,u,v}
                ==> lpcurv G y (\m. transp S ** basis 1) <= lsectional G y u v) /\
         inf {lsectional G y u v | u,v | ~collinear {vec 0,u,v}} =
         lpcurv G y (\m. transp S ** basis 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
         RFA_P3_MIN_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u v. ~collinear {vec 0,u,v}
          ==> lpcurv (G:real^3->real^3^3) y (\m. transp(S:real^3^3) ** basis 1) <=
              lsectional G y u v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                   `u:real^3`; `v:real^3`] RFA_SEC_AS_PCURV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INF_UNIQUE THEN
  REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `b:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                 `transp(S:real^3^3) ** basis 1:real^3`] RFA_PCURV_AS_SEC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[]);;


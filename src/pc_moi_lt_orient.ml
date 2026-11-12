(* ========================================================================= *)
(* pc_moi_lt_orient: the orientation sign of an injective PL map of a        *)
(* connected open set of real^3 into the interior of a finite oriented       *)
(* combinatorial 3-manifold with boundary (the loop theorem, case 1 of       *)
(* Moise p.185).  Main theorem ORIENT_SIGN : |- MOI_LT_ORIENT_SIGN           *)
(* (pc_moi_loop_stmt3).                                                      *)
(* The value of a good ball is sg a b d e times the sign of det of the Gram *)
(* form; it is locally constant off the preimage of the 1-skeleton (an      *)
(* unfolding across a 2-face and LOCAL_SIGN of pc_moi_s35_deg), and that    *)
(* complement is connected (dimension <= 1).                                *)
(* ========================================================================= *)

needs "src/pc_moi_loop_stmt3.ml";;
needs "src/pc_moi_s35_deg.ml";;
needs "src/pc_moi_fnd_rn.ml";;
needs "src/pc_moi_fnd_m3a.ml";;
needs "src/pc_moi_real.ml";;
needs "src/pc_moi_plmap.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Algebra of good balls.  The Gram-form matrix and the value of a          *)
(* good ball; coordinate maps of a tetrahedron; the Gram matrix is positive *)
(* definite; the value does not depend on the order of the vertices.        *)
(* ========================================================================= *)

let moi_lor_mat = new_definition
 `moi_lor_mat (l:real^3->real^N) (a:real^N) b d e =
    (lambda i j. l(basis j) dot
                 (if i = 1 then b - a else if i = 2 then d - a else e - a)):real^3^3`;;

let moi_lor_val = new_definition
 `moi_lor_val (sg:real^N->real^N->real^N->real^N->real) (l:real^3->real^N) a b d e =
    sg a b d e * real_sgn(det(moi_lor_mat l a b d e))`;;

let moi_lor_good = new_definition
 `moi_lor_good (c:(real^N->bool)->bool) (g:real^3->real^N) w a b d e
               (l:real^3->real^N) y z r <=>
    convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
    linear l /\ &0 < r /\ ball(z,r) SUBSET w /\
    (!x. x IN ball(z,r) ==> g x = l x + y /\ g x IN convex hull {a,b,d,e})`;;

let MOI_LOR_TET = prove
 (`!a b d e:real^N.
     aff_dim(convex hull {a,b,d,e}) = &3
     ==> ~affine_dependent {a,b,d,e} /\
         ~(a = b) /\ ~(a = d) /\ ~(a = e) /\ ~(b = d) /\ ~(b = e) /\ ~(d = e)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_FMB_AFF3_INDEP) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `CARD:(real^N->bool)->num`)) (concl th))) THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT COND_CASES_TAC THEN ARITH_TAC);;

let MOI_LOR_INDEP = prove
 (`!a b d e:real^N.
     ~affine_dependent {a,b,d,e} /\
     ~(a = b) /\ ~(a = d) /\ ~(a = e) /\ ~(b = d) /\ ~(b = e) /\ ~(d = e)
     ==> independent {b - a, d - a, e - a} /\
         ~(b - a = d - a) /\ ~(b - a = e - a) /\ ~(d - a = e - a)`,
  REPEAT STRIP_TAC THEN
  TRY(UNDISCH_TAC `b - a:real^N = d - a` THEN ASM_REWRITE_TAC[VECTOR_ARITH
    `x - a:real^N = y - a <=> x = y`] THEN NO_TAC) THEN
  TRY(UNDISCH_TAC `b - a:real^N = e - a` THEN ASM_REWRITE_TAC[VECTOR_ARITH
    `x - a:real^N = y - a <=> x = y`] THEN NO_TAC) THEN
  TRY(UNDISCH_TAC `d - a:real^N = e - a` THEN ASM_REWRITE_TAC[VECTOR_ARITH
    `x - a:real^N = y - a <=> x = y`] THEN NO_TAC) THEN
  REWRITE_TAC[independent] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `{b:real^N,d,e}`] DEPENDENT_IMP_AFFINE_DEPENDENT) THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; SIMPLE_IMAGE; IMAGE_CLAUSES]);;

let MOI_LOR_COORDS = prove
 (`!a b d e:real^N.
     ~affine_dependent {a,b,d,e} /\
     ~(a = b) /\ ~(a = d) /\ ~(a = e) /\ ~(b = d) /\ ~(b = e) /\ ~(d = e)
     ==> ?L:real^N->real^3.
           linear L /\ L(b - a) = basis 1 /\ L(d - a) = basis 2 /\ L(e - a) = basis 3`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_LOR_INDEP) THEN
  MP_TAC(ISPECL
   [`\v:real^N. if v = b - a then basis 1
                else if v = d - a then basis 2 else basis 3:real^3`;
    `{b - a:real^N, d - a, e - a}`] LINEAR_INDEPENDENT_EXTEND) THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^N->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `L:real^N->real^3` THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[]);;

let MOI_LOR_SPAN_COORDS = prove
 (`!a b d e:real^N (L:real^N->real^3) v.
     linear L /\ L(b - a) = basis 1 /\ L(d - a) = basis 2 /\ L(e - a) = basis 3 /\
     v IN span {b - a, d - a, e - a}
     ==> v = (L v)$1 % (b - a) + (L v)$2 % (d - a) + (L v)$3 % (e - a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\v:real^N. v`;
    `\v:real^N. (L v:real^3)$1 % (b - a:real^N) + (L v)$2 % (d - a) + (L v)$3 % (e - a)`;
    `{b - a:real^N, d - a, e - a}`; `span {b - a:real^N, d - a, e - a}`]
   LINEAR_EQ) THEN
  REWRITE_TAC[SUBSET_REFL] THEN ANTS_TAC THENL
   [REWRITE_TAC[LINEAR_ID] THEN CONJ_TAC THENL
     [REWRITE_TAC[linear] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th;
                                        MATCH_MP LINEAR_CMUL th]) THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      VECTOR_ARITH_TAC;
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
      CONV_TAC NUM_REDUCE_CONV THEN VECTOR_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[]]);;
let MOI_LOR_MAT_COORDS = prove
 (`!a b d e:real^N (L:real^N->real^3) (l:real^3->real^N).
     linear L /\ L(b - a) = basis 1 /\ L(d - a) = basis 2 /\ L(e - a) = basis 3 /\
     (!x. l x IN span {b - a, d - a, e - a})
     ==> moi_lor_mat l a b d e =
         (lambda i j. (if j = 1 then b - a else if j = 2 then d - a else e - a) dot
                      (if i = 1 then b - a else if i = 2 then d - a else e - a)):real^3^3 **
         matrix(L o l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x w. (l:real^3->real^N) x dot w =
          (L(l x):real^3)$1 * ((b - a) dot w) + (L(l x))$2 * ((d - a) dot w) +
          (L(l x))$3 * ((e - a) dot w)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `L:real^N->real^3`;
                   `(l:real^3->real^N) x`] MOI_LOR_SPAN_COORDS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THEN
    REWRITE_TAC[DOT_LADD; DOT_LMUL];
    ALL_TAC] THEN
  REWRITE_TAC[moi_lor_mat] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_3; FORALL_3; ARITH; matrix_mul; SUM_3;
           matrix; o_THM] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_LOR_GRAM_POS = prove
 (`!a b d e:real^N (L:real^N->real^3).
     linear L /\ L(b - a) = basis 1 /\ L(d - a) = basis 2 /\ L(e - a) = basis 3
     ==> &0 < det((lambda i j. (if j = 1 then b - a else if j = 2 then d - a else e - a) dot
                              (if i = 1 then b - a else if i = 2 then d - a else e - a))
                  :real^3^3)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN
  REWRITE_TAC[positive_definite; symmetric_matrix] THEN CONJ_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA; TRANSP_COMPONENT; DIMINDEX_3; FORALL_3; ARITH] THEN
    REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  ABBREV_TAC `v:real^N = (x:real^3)$1 % (b - a) + x$2 % (d - a) + x$3 % (e - a)` THEN
  SUBGOAL_THEN `(L:real^N->real^3) v = x` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v:real^N = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(x:real^3 = vec 0)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `(L:real^N->real^3) v = x` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LINEAR_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(x:real^3) dot
    ((lambda i j. (if j = 1 then b - a:real^N else if j = 2 then d - a else e - a) dot
                  (if i = 1 then b - a else if i = 2 then d - a else e - a))
     :real^3^3) ** x = (v:real^N) dot v`
  SUBST1_TAC THENL
   [EXPAND_TAC "v" THEN
    SIMP_TAC[DOT_3; MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH; LAMBDA_BETA] THEN
    REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[DOT_POS_LT]]);;

let MOI_LOR_SGN_COORDS = prove
 (`!a b d e:real^N (L:real^N->real^3) (l:real^3->real^N).
     linear L /\ L(b - a) = basis 1 /\ L(d - a) = basis 2 /\ L(e - a) = basis 3 /\
     (!x. l x IN span {b - a, d - a, e - a})
     ==> real_sgn(det(moi_lor_mat l a b d e)) = real_sgn(det(matrix(L o l)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `L:real^N->real^3`;
                 `l:real^3->real^N`] MOI_LOR_MAT_COORDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DET_MUL; REAL_SGN_MUL] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `L:real^N->real^3`]
    MOI_LOR_GRAM_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [real_sgn] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID]);;

let MOI_LOR_DET_NZ = prove
 (`!a b d e:real^N (L:real^N->real^3) (l:real^3->real^N).
     linear L /\ L(b - a) = basis 1 /\ L(d - a) = basis 2 /\ L(e - a) = basis 3 /\
     linear l /\ (!x. l x IN span {b - a, d - a, e - a}) /\
     (!x y. l x = l y ==> x = y)
     ==> ~(det(matrix(L o l)) = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear((L:real^N->real^3) o (l:real^3->real^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[LINEAR_COMPOSE]; ALL_TAC] THEN
  MP_TAC(ISPEC `matrix((L:real^N->real^3) o (l:real^3->real^N))`
    HOMOGENEOUS_LINEAR_EQUATIONS_DET) THEN
  ASM_SIMP_TAC[MATRIX_WORKS; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `L:real^N->real^3`;
                 `(l:real^3->real^N) x`] MOI_LOR_SPAN_COORDS) THEN
  ASM_REWRITE_TAC[VEC_COMPONENT; VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
  DISCH_TAC THEN UNDISCH_TAC `~(x:real^3 = vec 0)` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[LINEAR_0]);;

let MOI_LOR_DET_SWAPS = prove
 (`!(l:real^3->real^N) a b d e.
     det(moi_lor_mat l b a d e) = --det(moi_lor_mat l a b d e) /\
     det(moi_lor_mat l a d b e) = --det(moi_lor_mat l a b d e) /\
     det(moi_lor_mat l a b e d) = --det(moi_lor_mat l a b d e)`,
  REWRITE_TAC[moi_lor_mat; DET_3] THEN SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[DOT_RSUB] THEN CONV_TAC REAL_RING);;
let MOI_LOR_PERM4 = prove
 (`!P:A->A->A->A->bool.
     (!a b d e. P a b d e ==> P b a d e /\ P a d b e /\ P a b e d)
     ==> !a b d e a' b' d' e'.
           P a b d e /\
           ~(a = b) /\ ~(a = d) /\ ~(a = e) /\ ~(b = d) /\ ~(b = e) /\ ~(d = e) /\
           {a',b',d',e'} = {a,b,d,e}
           ==> P a' b' d' e'`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(b:A = a) /\ ~(d = a) /\ ~(e = a) /\ ~(d = b) /\ ~(e = b) /\ ~(e = d)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:A`) THEN FIRST_ASSUM(MP_TAC o SPEC `b:A`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `d:A`) THEN FIRST_ASSUM(MP_TAC o SPEC `e:A`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `a':A`) THEN FIRST_ASSUM(MP_TAC o SPEC `b':A`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `d':A`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `e':A`) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_LOR_VAL_SWAPS = prove
 (`!(sg:real^N->real^N->real^N->real^N->real) (c:(real^N->bool)->bool) l a b d e.
     (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
                ==> (sg a b d e = &1 \/ sg a b d e = -- &1) /\
                    sg b a d e = --(sg a b d e) /\ sg a d b e = --(sg a b d e) /\
                    sg a b e d = --(sg a b d e)) /\
     convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
     ==> moi_lor_val sg l b a d e = moi_lor_val sg l a b d e /\
         moi_lor_val sg l a d b e = moi_lor_val sg l a b d e /\
         moi_lor_val sg l a b e d = moi_lor_val sg l a b d e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l:real^3->real^N`; `a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`]
    MOI_LOR_DET_SWAPS) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[moi_lor_val; REAL_SGN_NEG] THEN REAL_ARITH_TAC);;

let MOI_LOR_VAL_PERM = prove
 (`!(sg:real^N->real^N->real^N->real^N->real) (c:(real^N->bool)->bool) l a b d e
    a' b' d' e'.
     (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
                ==> (sg a b d e = &1 \/ sg a b d e = -- &1) /\
                    sg b a d e = --(sg a b d e) /\ sg a d b e = --(sg a b d e) /\
                    sg a b e d = --(sg a b d e)) /\
     convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
     {a',b',d',e'} = {a,b,d,e}
     ==> moi_lor_val sg l a' b' d' e' = moi_lor_val sg l a b d e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] MOI_LOR_TET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC
   `\x y z t:real^N. {x,y,z,t} = {a,b,d,e} /\
                     moi_lor_val sg (l:real^3->real^N) x y z t = moi_lor_val sg l a b d e`
   MOI_LOR_PERM4) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `z:real^N`; `t:real^N`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`sg:real^N->real^N->real^N->real^N->real`;
                   `c:(real^N->bool)->bool`; `l:real^3->real^N`;
                   `x:real^N`; `y:real^N`; `z:real^N`; `t:real^N`] MOI_LOR_VAL_SWAPS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{x:real^N,y,z,t} = {a,b,d,e}` THEN SET_TAC[];
    DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`;
                               `a':real^N`; `b':real^N`; `d':real^N`; `e':real^N`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* Facts about one good ball: the linear part is injective with             *)
(* range in the direction space of the tetrahedron, the centre maps to the  *)
(* relative interior, the value is +/-1, good balls shrink.                 *)
(* ========================================================================= *)

let MOI_LOR_LINEAR_INJ = prove
 (`!(l:real^3->real^N) y z r.
     linear l /\ &0 < r /\
     (!x1 x2. x1 IN ball(z,r) /\ x2 IN ball(z,r) /\ l x1 + y = l x2 + y ==> x1 = x2)
     ==> !u v. l u = l v ==> u = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  ABBREV_TAC `w:real^3 = u - v` THEN
  SUBGOAL_THEN `(l:real^3->real^N) w = vec 0` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_SUB th]) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `w:real^3 = vec 0` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`z + (r / (&2 * norm(w:real^3))) % w`; `z:real^3`]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID; CENTRE_IN_BALL;
                  VECTOR_ARITH `z + x:real^3 = z <=> x = vec 0`; VECTOR_MUL_EQ_0] THEN
  SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[IN_BALL; NORM_ARITH `dist(z:real^3,z + x) = norm x`; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_NORM;
               REAL_ARITH `&0 < r ==> abs r = r`] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH;
               REAL_FIELD `&0 < n ==> r / (&2 * n) * n = r / &2`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_ARITH `&0 < r ==> r / &2 < r`] THEN
  REWRITE_TAC[real_div; REAL_ENTIRE; REAL_INV_EQ_0; REAL_OF_NUM_EQ; ARITH] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ]);;

let MOI_LOR_GOOD_SHRINK = prove
 (`!(c:(real^N->bool)->bool) g w a b d e l y z r z1 r1.
     moi_lor_good c g w a b d e l y z r /\ &0 < r1 /\ ball(z1,r1) SUBSET ball(z,r)
     ==> moi_lor_good c g w a b d e l y z1 r1`,
  REWRITE_TAC[moi_lor_good] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[SUBSET]]);;

let MOI_LOR_GOOD_HULL = prove
 (`!(c:(real^N->bool)->bool) g w a b d e a' b' d' e' l y z r.
     moi_lor_good c g w a b d e l y z r /\
     convex hull {a',b',d',e'} = convex hull {a,b,d,e}
     ==> moi_lor_good c g w a' b' d' e' l y z r`,
  REWRITE_TAC[moi_lor_good] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let MOI_LOR_GOOD_INJ = prove
 (`!(c:(real^N->bool)->bool) (g:real^3->real^N) w a b d e l y z r.
     moi_lor_good c g w a b d e l y z r /\
     (!x y. x IN w /\ y IN w /\ g x = g y ==> x = y)
     ==> !u v. l u = l v ==> u = v`,
  REWRITE_TAC[moi_lor_good] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_LOR_LINEAR_INJ THEN
  MAP_EVERY EXISTS_TAC [`y:real^N`; `z:real^3`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term ((=) `w:real^3->bool`)) (concl th) &&
    can (find_term ((=) `g:real^3->real^N`)) (concl th) && is_forall (concl th) &&
    not (can (find_term ((=) `ball:real^3#real->real^3->bool`)) (concl th)))) THEN
  ASM_MESON_TAC[SUBSET]);;

let MOI_LOR_GOOD_SPAN = prove
 (`!(c:(real^N->bool)->bool) (g:real^3->real^N) w a b d e l y z r.
     moi_lor_good c g w a b d e l y z r
     ==> !x. l x IN span {b - a, d - a, e - a}`,
  REWRITE_TAC[moi_lor_good] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `x:real^3` THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] MOI_LOR_TET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!p:real^N. p IN convex hull {a,b,d,e} ==> p - a IN span {b - a, d - a, e - a}`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `{b:real^N,d,e}`] AFFINE_HULL_INSERT_SPAN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]; ALL_TAC] THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^N) IN affine hull {a,b,d,e}` MP_TAC THENL
     [ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(a + q) - a:real^N = q`];
    ALL_TAC] THEN
  ABBREV_TAC `t = (r / &2) / (norm(x:real^3) + &1)` THEN
  SUBGOAL_THEN `&0 < norm(x:real^3) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `x:real^3` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t /\ t * (norm(x:real^3) + &1) = r / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_RMUL; REAL_LT_IMP_NZ;
                 REAL_ARITH `&0 < r ==> &0 < r / &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN `z + t % x IN ball(z:real^3,r)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL; NORM_ARITH `dist(z:real^3,z + x) = norm x`; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
    UNDISCH_TAC `t * (norm(x:real^3) + &1) = r / &2` THEN
    UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^3->real^N) (t % x) IN span {b - a, d - a, e - a}` MP_TAC THENL
   [SUBGOAL_THEN `(l:real^3->real^N) (t % x) =
                  ((g:real^3->real^N) (z + t % x) - a) - (g z - a)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[CENTRE_IN_BALL] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th]) THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC SPAN_SUB THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[CENTRE_IN_BALL]];
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
    DISCH_THEN(MP_TAC o SPEC `inv t:real` o MATCH_MP SPAN_MUL) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]]);;

let MOI_LOR_GOOD_PM1 = prove
 (`!(c:(real^N->bool)->bool) sg (g:real^3->real^N) w a b d e l y z r.
     (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
                ==> (sg a b d e = &1 \/ sg a b d e = -- &1) /\
                    sg b a d e = --(sg a b d e) /\ sg a d b e = --(sg a b d e) /\
                    sg a b e d = --(sg a b d e)) /\
     (!x y. x IN w /\ y IN w /\ g x = g y ==> x = y) /\
     moi_lor_good c g w a b d e l y z r
     ==> moi_lor_val sg l a b d e = &1 \/ moi_lor_val sg l a b d e = -- &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_LOR_GOOD_SPAN) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^3->real^N`; `w:real^3->bool`;
                 `a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `l:real^3->real^N`;
                 `y:real^N`; `z:real^3`; `r:real`] MOI_LOR_GOOD_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lor_good]) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] MOI_LOR_TET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] MOI_LOR_COORDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `L:real^N->real^3`;
                 `l:real^3->real^N`] MOI_LOR_SGN_COORDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `L:real^N->real^3`;
                 `l:real^3->real^N`] MOI_LOR_DET_NZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `real_sgn(det(matrix((L:real^N->real^3) o (l:real^3->real^N)))) = &1 \/
    real_sgn(det(matrix((L:real^N->real^3) o (l:real^3->real^N)))) = -- &1`
  MP_TAC THENL
   [REWRITE_TAC[REAL_SGN_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ASM_REWRITE_TAC[moi_lor_val] THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_LOR_GOOD_RELINT = prove
 (`!(c:(real^N->bool)->bool) (g:real^3->real^N) w a b d e l y z r.
     moi_lor_good c g w a b d e l y z r /\
     (!x y. x IN w /\ y IN w /\ g x = g y ==> x = y)
     ==> g z IN relative_interior(convex hull {a,b,d,e})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^3->real^N`; `w:real^3->bool`;
                 `a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `l:real^3->real^N`;
                 `y:real^N`; `z:real^3`; `r:real`] MOI_LOR_GOOD_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lor_good]) THEN
  ABBREV_TAC `q = IMAGE (\x. y + x) (IMAGE (l:real^3->real^N) (ball(z,r)))` THEN
  SUBGOAL_THEN `!x. x IN ball(z:real^3,r) ==> (g:real^3->real^N) x IN q` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXPAND_TAC "q" THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(l:real^3->real^N) x` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `q SUBSET convex hull {a:real^N,b,d,e}` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `y + (l:real^3->real^N) x = g x` SUBST1_TAC THENL
     [ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(q:real^N->bool) = &3` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[AFF_DIM_TRANSLATION_EQ] THEN
    MP_TAC(ISPECL [`l:real^3->real^N`; `ball(z:real^3,r)`]
      AFF_DIM_INJECTIVE_LINEAR_IMAGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[AFF_DIM_BALL; DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior q:real^N->bool = q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[RELATIVE_INTERIOR_TRANSLATION] THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_LINEAR_IMAGE_CONVEX; CONVEX_BALL;
                 RELATIVE_INTERIOR_OPEN; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_interior q SUBSET relative_interior(convex hull {a:real^N,b,d,e})`
  MP_TAC THENL
   [MATCH_MP_TAC SUBSET_RELATIVE_INTERIOR THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN ASM_REWRITE_TAC[INT_LE_REFL];
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]]);;

let MOI_LOR_GOOD_OFF_SKEL = prove
 (`!(c:(real^N->bool)->bool) (g:real^3->real^N) w a b d e l y z r.
     lf_simplicial_complex c /\ moi_lor_good c g w a b d e l y z r /\
     (!x y. x IN w /\ y IN w /\ g x = g y ==> x = y)
     ==> ~(g z IN UNIONS {t | t IN c /\ aff_dim t <= &1})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^3->real^N`; `w:real^3->bool`;
                 `a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `l:real^3->real^N`;
                 `y:real^N`; `z:real^3`; `r:real`] MOI_LOR_GOOD_RELINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `convex hull {a:real^N,b,d,e}`;
                 `t:real^N->bool`; `(g:real^3->real^N) z`] MOI_FM3_LF_RELINT_SUBSET) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lor_good]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN
  ASM_INT_ARITH_TAC);;

(* ========================================================================= *)
(* The complex near a point off the 1-skeleton and off the                  *)
(* boundary: one 3-simplex, or two 3-simplices meeting in a 2-face; the     *)
(* unfolding of two adjacent 3-simplices into real^3.                       *)
(* ========================================================================= *)

let MOI_LOR_SIMPLICIAL = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c ==> simplicial_complex c`,
  GEN_TAC THEN REWRITE_TAC[simplicial_complex; lf_simplicial_complex] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let MOI_LOR_VERTS_EQ = prove
 (`!s t:real^N->bool.
     ~affine_dependent s /\ ~affine_dependent t /\ convex hull s = convex hull t
     ==> s = t`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`]
    EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `x:real^N`]
    EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_LOR_CELL_EQ = prove
 (`!c s t:real^N->bool.
     lf_simplicial_complex c /\ s IN c /\ t IN c /\ s SUBSET t /\
     aff_dim t <= aff_dim s
     ==> s = t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) INTER t face_of t` MP_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER t = (s:real^N->bool)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex(t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  ASM_CASES_TAC `s:real^N->bool = t` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

let MOI_LOR_SIMPLEX_VERTS = prove
 (`!c t:real^N->bool.
     lf_simplicial_complex c /\ t IN c
     ==> ?C. ~affine_dependent C /\ aff_dim t = &(CARD C) - &1 /\ t = convex hull C`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_TAC THEN EXISTS_TAC `C:real^N->bool` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]);;

let MOI_LOR_SIMPLEX_2 = prove
 (`!c t:real^N->bool.
     lf_simplicial_complex c /\ t IN c /\ aff_dim t = &2
     ==> ?v0 v1 v2. t = convex hull {v0,v1,v2} /\ ~affine_dependent {v0,v1,v2} /\
                    ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v1 = v2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_LOR_SIMPLEX_VERTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(C:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real^N` (X_CHOOSE_THEN `v1:real^N`
    (X_CHOOSE_THEN `v2:real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`v0:real^N`; `v1:real^N`; `v2:real^N`] THEN
  ASM_MESON_TAC[]);;

let MOI_LOR_SIMPLEX_3 = prove
 (`!c t:real^N->bool.
     lf_simplicial_complex c /\ t IN c /\ aff_dim t = &3
     ==> ?a b d e. t = convex hull {a,b,d,e}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_LOR_SIMPLEX_VERTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(C:real^N->bool) HAS_SIZE 4` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `d:real^N` (X_CHOOSE_THEN `e:real^N` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] THEN
  ASM_MESON_TAC[]);;

let MOI_LOR_STAR_NBHD = prove
 (`!c t (p:real^N).
     FINITE c /\ lf_simplicial_complex c /\ t IN c /\ p IN relative_interior t
     ==> ?u. open u /\ p IN u /\
             !x. x IN u /\ x IN UNIONS c ==> ?r. r IN c /\ t SUBSET r /\ x IN r`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(:real^N) DIFF UNIONS {r | r IN c /\ ~((p:real^N) IN r)}` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
    X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC POLYTOPE_IMP_CLOSED THEN
    ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_POLYTOPE];
    REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(p:real^N) IN r` ASSUME_TAC THENL
     [UNDISCH_TAC `~((x:real^N) IN UNIONS {r | r IN c /\ ~((p:real^N) IN r)})` THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[MOI_FM3_LF_RELINT_SUBSET]]]);;

let MOI_LOR_AFF_DIM_4 = prove
 (`!a b d e:real^N.
     ~affine_dependent {a,b,d,e} /\
     ~(a = b) /\ ~(a = d) /\ ~(a = e) /\ ~(b = d) /\ ~(b = e) /\ ~(d = e)
     ==> aff_dim(convex hull {a,b,d,e}) = &3`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
  ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV);;

let MOI_LOR_AFF_DIM_3 = prove
 (`!a b d:real^N.
     ~affine_dependent {a,b,d} /\ ~(a = b) /\ ~(a = d) /\ ~(b = d)
     ==> aff_dim(convex hull {a,b,d}) = &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
  ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV);;

let MOI_LOR_TWO_COFACES = prove
 (`!c (a:real^N) b d p.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     convex hull {a,b,d} IN c /\ ~affine_dependent {a,b,d} /\
     ~(a = b) /\ ~(a = d) /\ ~(b = d) /\
     p IN convex hull {a,b,d} /\ ~(p IN complex_boundary c)
     ==> ?e e'. ~(e = e') /\
                convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
                convex hull {a,b,d,e'} IN c /\ aff_dim(convex hull {a,b,d,e'}) = &3 /\
                (!r. r IN c /\ aff_dim r = &3 /\ convex hull {a,b,d} SUBSET r
                     ==> r = convex hull {a,b,d,e} \/ r = convex hull {a,b,d,e'}) /\
                convex hull {a,b,d,e} INTER convex hull {a,b,d,e'} =
                convex hull {a,b,d}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `d:real^N`]
    MOI_FRN_TRIANGLE_COFACES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `aff_dim(convex hull {a,b,d,u1:real^N}) = &3 /\
                aff_dim(convex hull {a,b,d,u2:real^N}) = &3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LOR_AFF_DIM_4 THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(convex hull {a,b,d:real^N}) = &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LOR_AFF_DIM_3 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(u1:real^N = u2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((p:real^N) IN complex_boundary c)` THEN
    REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `convex hull {a:real^N,b,d}` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{r | r IN c /\ aff_dim r = &3 /\ convex hull {a,b,d} SUBSET r} =
      {convex hull {a:real^N,b,d,u2}}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `r:real^N->bool` THEN EQ_TAC THENL
       [ASM_MESON_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
      REWRITE_TAC[CARD_SING]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u1:real^N`; `u2:real^N`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{a:real^N,b,d,u1}`; `{a:real^N,b,d,u2}`]
    MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LOR_SIMPLICIAL THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]]);;

let MOI_LOR_LOCAL_STRUCT = prove
 (`!c (p:real^N).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     p IN UNIONS c /\ ~(p IN complex_boundary c) /\
     ~(p IN UNIONS {t | t IN c /\ aff_dim t <= &1})
     ==> ?u. open u /\ p IN u /\
             ((?a b d e. convex hull {a,b,d,e} IN c /\
                         aff_dim(convex hull {a,b,d,e}) = &3 /\
                         !x. x IN u /\ x IN UNIONS c ==> x IN convex hull {a,b,d,e}) \/
              (?a b d e e'. ~(e = e') /\
                 convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
                 convex hull {a,b,d,e'} IN c /\ aff_dim(convex hull {a,b,d,e'}) = &3 /\
                 convex hull {a,b,d,e} INTER convex hull {a,b,d,e'} =
                 convex hull {a,b,d} /\
                 !x. x IN u /\ x IN UNIONS c
                     ==> x IN convex hull {a,b,d,e} UNION convex hull {a,b,d,e'}))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `p:real^N`] MOI_FM3_CARRIER_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `p:real^N`]
    MOI_LOR_STAR_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(p:real^N) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN c ==> aff_dim r <= &3` ASSUME_TAC THENL
   [MATCH_MP_TAC CM_WB_DIM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(t:real^N->bool) = &2 \/ aff_dim t = &3` MP_TAC THENL
   [SUBGOAL_THEN `~(aff_dim(t:real^N->bool) <= &1)` MP_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~((p:real^N) IN UNIONS {t | t IN c /\ aff_dim t <= &1})` THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ2_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_LOR_SIMPLEX_2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      (X_CHOOSE_THEN `d:real^N` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `d:real^N`;
                   `p:real^N`] MOI_LOR_TWO_COFACES) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N` (X_CHOOSE_THEN `e':real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `e':real^N`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      can (find_term ((=) `u:real^N->bool`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `aff_dim(r:real^N->bool) = &2 \/ aff_dim r = &3` MP_TAC THENL
     [MP_TAC(ISPECL [`t:real^N->bool`; `r:real^N->bool`] AFF_DIM_SUBSET) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool` o check (fun th ->
        can (find_term ((=) `&3:int`)) (concl th) && is_forall (concl th) &&
        not (can (find_term ((=) `convex hull {a:real^N,b,d}`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `t:real^N->bool = r` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC MOI_LOR_CELL_EQ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[INT_LE_REFL];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
      SUBGOAL_THEN `convex hull {a,b,d} SUBSET convex hull {a:real^N,b,d,e}` MP_TAC THENL
       [MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ASM SET_TAC[]];
      SUBGOAL_THEN `r = convex hull {a:real^N,b,d,e} \/ r = convex hull {a,b,d,e'}`
      MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM SET_TAC[]];
    DISJ1_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_LOR_SIMPLEX_3) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      (X_CHOOSE_THEN `d:real^N` (X_CHOOSE_THEN `e:real^N` ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] THEN
    UNDISCH_TAC `t = convex hull {a:real^N,b,d,e}` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      can (find_term ((=) `u:real^N->bool`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `t:real^N->bool = r` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MOI_LOR_CELL_EQ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[]]);;

let moi_lor_flip = new_definition
 `moi_lor_flip (x:real^3) = vector[x$1; x$2; --(x$3)]:real^3`;;

let moi_lor_unf = new_definition
 `moi_lor_unf (s:real^N->bool) (a:real^N) (L1:real^N->real^3) (L2:real^N->real^3) x =
    if x IN s then L1(x - a) else moi_lor_flip(L2(x - a))`;;

let MOI_LOR_FLIP = prove
 (`linear moi_lor_flip /\
   moi_lor_flip(basis 1) = basis 1 /\ moi_lor_flip(basis 2) = basis 2 /\
   (!x. (moi_lor_flip x)$3 = --(x$3)) /\
   (!x y. moi_lor_flip x = moi_lor_flip y ==> x = y) /\
   det(matrix moi_lor_flip) = -- &1`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[linear; moi_lor_flip] THEN
    SIMP_TAC[CART_EQ; VECTOR_3; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    SIMP_TAC[moi_lor_flip; CART_EQ; VECTOR_3; DIMINDEX_3; FORALL_3; BASIS_COMPONENT;
             ARITH] THEN REAL_ARITH_TAC;
    SIMP_TAC[moi_lor_flip; CART_EQ; VECTOR_3; DIMINDEX_3; FORALL_3; BASIS_COMPONENT;
             ARITH] THEN REAL_ARITH_TAC;
    REWRITE_TAC[moi_lor_flip; VECTOR_3];
    REWRITE_TAC[moi_lor_flip] THEN
    SIMP_TAC[CART_EQ; VECTOR_3; DIMINDEX_3; FORALL_3] THEN REAL_ARITH_TAC;
    SIMP_TAC[matrix; DET_3; LAMBDA_BETA; DIMINDEX_3; ARITH; moi_lor_flip; VECTOR_3;
             BASIS_COMPONENT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let MOI_LOR_HULL_SPAN = prove
 (`!(a:real^N) s p. p IN convex hull (a INSERT s) ==> p - a IN span {x - a | x IN s}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `s:real^N->bool`] AFFINE_HULL_INSERT_SUBSET_SPAN) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `(a + v) - a:real^N = v`]);;

let MOI_LOR_HULL_SPAN_4 = prove
 (`!a b d e p:real^N.
     p IN convex hull {a,b,d,e} ==> p - a IN span {b - a, d - a, e - a}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_LOR_HULL_SPAN) THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES]);;

let MOI_LOR_HULL_SPAN_3 = prove
 (`!a b d p:real^N.
     p IN convex hull {a,b,d} ==> p - a IN span {b - a, d - a}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_LOR_HULL_SPAN) THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES]);;

let MOI_LOR_HULL_COORDS = prove
 (`!a b d e:real^N (L:real^N->real^3) x.
     linear L /\ L(b - a) = basis 1 /\ L(d - a) = basis 2 /\ L(e - a) = basis 3 /\
     x IN convex hull {a,b,d,e}
     ==> &0 <= (L(x - a))$1 /\ &0 <= (L(x - a))$2 /\ &0 <= (L(x - a))$3 /\
         (L(x - a))$1 + (L(x - a))$2 + (L(x - a))$3 <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `convex hull {a,b,d,e} SUBSET
    {x:real^N | &0 <= (L(x - a):real^3)$1 /\ &0 <= (L(x - a))$2 /\
                &0 <= (L(x - a))$3 /\ (L(x - a))$1 + (L(x - a))$2 + (L(x - a))$3 <= &1}`
  MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[VECTOR_SUB_REFL] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN
      SIMP_TAC[VEC_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      REWRITE_TAC[convex; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`x1:real^N`; `x2:real^N`; `u:real`; `v:real`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(u % x1 + v % x2) - a:real^N = u % (x1 - a) + v % (x2 - a)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `u + v = &1` THEN
        REWRITE_TAC[REAL_ARITH `u + v = &1 <=> v = &1 - u`] THEN
        DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th;
                                        MATCH_MP LINEAR_CMUL th]) THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN
         `u * (((L:real^N->real^3)(x1 - a))$1 + (L(x1 - a))$2 + (L(x1 - a))$3)
          <= u * &1 /\
          v * (((L:real^N->real^3)(x2 - a))$1 + (L(x2 - a))$2 + (L(x2 - a))$3)
          <= v * &1`
        MP_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `u + v = &1` THEN REAL_ARITH_TAC]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LOR_FACE_COORD = prove
 (`!a b d e:real^N (L:real^N->real^3) x.
     linear L /\ L(b - a) = basis 1 /\ L(d - a) = basis 2 /\ L(e - a) = basis 3 /\
     x IN convex hull {a,b,d,e} /\ (L(x - a))$3 = &0
     ==> x IN convex hull {a,b,d}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `L:real^N->real^3`;
                 `x:real^N`] MOI_LOR_HULL_COORDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `L:real^N->real^3`;
                 `x - a:real^N`] MOI_LOR_SPAN_COORDS) THEN
  ASM_SIMP_TAC[MOI_LOR_HULL_SPAN_4; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  DISCH_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC
   [`&1 - ((L:real^N->real^3)(x - a))$1 - (L(x - a))$2`;
    `((L:real^N->real^3)(x - a))$1`; `((L:real^N->real^3)(x - a))$2`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC
   `x - a:real^N = (L(x - a):real^3)$1 % (b - a) + (L(x - a))$2 % (d - a)` THEN
  VECTOR_ARITH_TAC);;

let MOI_LOR_FLAT = prove
 (`!a b d e:real^N (L:real^N->real^3).
     linear L /\ L(b - a) = basis 1 /\ L(d - a) = basis 2 /\ L(e - a) = basis 3
     ==> (\x. L(x - a)) continuous_on (convex hull {a,b,d,e}) /\
         (!x x'. x IN convex hull {a,b,d,e} /\ x' IN convex hull {a,b,d,e} /\
                 L(x - a) = L(x' - a) ==> x = x')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:real^N. (L:real^N->real^3)(x - a)) = (\x. L x - L a)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[LINEAR_SUB]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX] THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `L:real^N->real^3`;
                   `x - a:real^N`] MOI_LOR_SPAN_COORDS) THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `L:real^N->real^3`;
                   `x' - a:real^N`] MOI_LOR_SPAN_COORDS) THEN
    ASM_SIMP_TAC[MOI_LOR_HULL_SPAN_4] THEN
    DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
      MATCH_MP_TAC(VECTOR_ARITH `x - a:real^N = x' - a ==> x = x'`) THEN
      ONCE_REWRITE_TAC[th1; th2])) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LOR_AFFINE_CONT = prove
 (`!(L:real^N->real^M) a s. linear L ==> (\x. L(x - a)) continuous_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. (L:real^N->real^M)(x - a)) = (\x. L x - L a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[LINEAR_SUB]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX] THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON]);;

let MOI_LOR_UNFOLD = prove
 (`!a b d e e':real^N (L1:real^N->real^3) L2.
     convex hull {a,b,d,e} INTER convex hull {a,b,d,e'} = convex hull {a,b,d} /\
     linear L1 /\ L1(b - a) = basis 1 /\ L1(d - a) = basis 2 /\ L1(e - a) = basis 3 /\
     linear L2 /\ L2(b - a) = basis 1 /\ L2(d - a) = basis 2 /\ L2(e' - a) = basis 3
     ==> (!x. x IN convex hull {a,b,d,e}
              ==> moi_lor_unf (convex hull {a,b,d,e}) a L1 L2 x = L1(x - a)) /\
         (!x. x IN convex hull {a,b,d,e'}
              ==> moi_lor_unf (convex hull {a,b,d,e}) a L1 L2 x =
                  moi_lor_flip(L2(x - a))) /\
         moi_lor_unf (convex hull {a,b,d,e}) a L1 L2 continuous_on
           (convex hull {a,b,d,e} UNION convex hull {a,b,d,e'}) /\
         (!x x'. x IN convex hull {a,b,d,e} UNION convex hull {a,b,d,e'} /\
                 x' IN convex hull {a,b,d,e} UNION convex hull {a,b,d,e'} /\
                 moi_lor_unf (convex hull {a,b,d,e}) a L1 L2 x =
                 moi_lor_unf (convex hull {a,b,d,e}) a L1 L2 x'
                 ==> x = x')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v:real^N. v IN span {b - a, d - a} ==> L1 v = moi_lor_flip(L2 v)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L1:real^N->real^3`; `moi_lor_flip o (L2:real^N->real^3)`;
                   `{b - a:real^N, d - a}`; `span {b - a:real^N, d - a}`] LINEAR_EQ) THEN
    REWRITE_TAC[SUBSET_REFL; o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[LINEAR_COMPOSE; MOI_LOR_FLIP] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[MOI_LOR_FLIP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN convex hull {a,b,d} ==> L1(x - a) = moi_lor_flip(L2(x - a))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MOI_LOR_HULL_SPAN_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN convex hull {a,b,d,e}
               ==> moi_lor_unf (convex hull {a,b,d,e}) a L1 L2 x = L1(x - a)`
  ASSUME_TAC THENL [SIMP_TAC[moi_lor_unf]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN convex hull {a,b,d,e'}
               ==> moi_lor_unf (convex hull {a,b,d,e}) a L1 L2 x =
                   moi_lor_flip(L2(x - a))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[moi_lor_unf] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x x':real^N. x IN convex hull {a,b,d,e} /\ x' IN convex hull {a,b,d,e'} /\
                  L1(x - a) = moi_lor_flip(L2(x' - a))
                  ==> x' IN convex hull {a,b,d,e}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `((L2:real^N->real^3)(x' - a))$3 = &0` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`;
                     `L1:real^N->real^3`; `x:real^N`] MOI_LOR_HULL_COORDS) THEN
      MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e':real^N`;
                     `L2:real^N->real^3`; `x':real^N`] MOI_LOR_HULL_COORDS) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. v$3` o check (fun th ->
        is_eq(concl th) &&
        can (find_term ((=) `moi_lor_flip`)) (concl th) &&
        not (is_forall(concl th)))) THEN
      REWRITE_TAC[MOI_LOR_FLIP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(x':real^N) IN convex hull {a,b,d}` MP_TAC THENL
     [MATCH_MP_TAC MOI_LOR_FACE_COORD THEN
      MAP_EVERY EXISTS_TAC [`e':real^N`; `L2:real^N->real^3`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> (x:real^N) IN t`) THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN
     `moi_lor_unf (convex hull {a,b,d,e}) a (L1:real^N->real^3) L2 =
      (\x. if x IN convex hull {a,b,d,e} then L1(x - a)
           else moi_lor_flip(L2(x - a)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_lor_unf]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT;
             FINITE_INSERT; FINITE_EMPTY] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LOR_AFFINE_CONT THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `(\x:real^N. moi_lor_flip((L2:real^N->real^3)(x - a))) =
        (\x. (moi_lor_flip o L2)(x - a))`
      SUBST1_TAC THENL [REWRITE_TAC[o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_LOR_AFFINE_CONT THEN ASM_SIMP_TAC[LINEAR_COMPOSE; MOI_LOR_FLIP];
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `x':real^N`] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`;
                   `L1:real^N->real^3`] MOI_LOR_FLAT) THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e':real^N`;
                   `L2:real^N->real^3`] MOI_LOR_FLAT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    ASM_CASES_TAC `(x:real^N) IN convex hull {a,b,d,e}` THEN
    ASM_CASES_TAC `(x':real^N) IN convex hull {a,b,d,e}` THEN
    ASM_MESON_TAC[MOI_LOR_FLIP]]);;

(* ========================================================================= *)
(* Local constancy of the value near a point whose image is off             *)
(* the 1-skeleton, via LOCAL_SIGN (pc_moi_s35_deg) for phi o g, phi the     *)
(* chart of one 3-simplex or the unfolding of two adjacent ones.            *)
(* ========================================================================= *)

let MOI_LOR_SGN_EQ = prove
 (`!x y. &0 < x * y ==> real_sgn x = real_sgn y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `real_sgn x * real_sgn y = &1` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_SGN_MUL; REAL_SGN_EQ] THEN ASM_REWRITE_TAC[real_gt];
    ALL_TAC] THEN
  MP_TAC(SPEC `x:real` REAL_SGN_CASES) THEN MP_TAC(SPEC `y:real` REAL_SGN_CASES) THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_LOR_BALL_SHRINK = prove
 (`!(z:real^3) rho z1 r1.
     z1 IN ball(z,rho) /\ &0 < r1
     ==> ?r. &0 < r /\ ball(z1,r) SUBSET ball(z1,r1) /\ ball(z1,r) SUBSET ball(z,rho)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `min r1 (rho - dist(z:real^3,z1))` THEN
  UNDISCH_TAC `z1 IN ball(z:real^3,rho)` THEN
  REWRITE_TAC[IN_BALL; SUBSET] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`z:real^3`; `z1:real^3`; `x:real^3`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_LOR_LIN_AT = prove
 (`!(M:real^N->real^3) (g:real^3->real^N) (phi:real^N->real^3) l y z r a.
     linear M /\ linear l /\ &0 < r /\
     (!x. x IN ball(z,r) ==> phi(g x) = M(l x + y - a))
     ==> moi_s35_lin_at (phi o g) z (M o l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s35_lin_at] THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE] THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[o_THM] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[CENTRE_IN_BALL] THEN
  SUBGOAL_THEN `(l:real^3->real^N) x + y - a = (l z + y - a) + l(x - z)` SUBST1_TAC THENL
   [REWRITE_TAC[MATCH_MP LINEAR_SUB (ASSUME `linear (l:real^3->real^N)`)] THEN
    VECTOR_ARITH_TAC;
    REWRITE_TAC[MATCH_MP LINEAR_ADD (ASSUME `linear (M:real^N->real^3)`)]]);;

let MOI_LOR_LOCAL_GENERIC = prove
 (`!(c:(real^N->bool)->bool) sg (g:real^3->real^N) w (phi:real^N->real^3) z rho s0.
     &0 < rho /\ ball(z,rho) SUBSET w /\
     (phi o g) continuous_on ball(z,rho) /\
     (!x y. x IN ball(z,rho) /\ y IN ball(z,rho) /\ phi(g x) = phi(g y) ==> x = y) /\
     (!a b d e l y z1 r1.
          moi_lor_good c g w a b d e l y z1 r1 /\ ball(z1,r1) SUBSET ball(z,rho)
          ==> ?m. moi_s35_lin_at (phi o g) z1 m /\
                  moi_lor_val sg l a b d e = s0 * real_sgn(det(matrix m)))
     ==> !a b d e l y z1 r1 a' b' d' e' l' y' z2 r2.
            moi_lor_good c g w a b d e l y z1 r1 /\ z1 IN ball(z,rho) /\
            moi_lor_good c g w a' b' d' e' l' y' z2 r2 /\ z2 IN ball(z,rho)
            ==> moi_lor_val sg l a b d e = moi_lor_val sg l' a' b' d' e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`z:real^3`; `rho:real`; `z1:real^3`; `r1:real`] MOI_LOR_BALL_SHRINK) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_lor_good]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`z:real^3`; `rho:real`; `z2:real^3`; `r2:real`] MOI_LOR_BALL_SHRINK) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_lor_good]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPECL [`a':real^N`; `b':real^N`; `d':real^N`; `e':real^N`; `l':real^3->real^N`;
                  `y':real^N`; `z2:real^3`; `s2:real`] th) THEN
    MP_TAC(SPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `l:real^3->real^N`;
                  `y:real^N`; `z1:real^3`; `s1:real`] th)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LOR_GOOD_SHRINK THEN
    MAP_EVERY EXISTS_TAC [`z1:real^3`; `r1:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:real^3->real^3` STRIP_ASSUME_TAC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LOR_GOOD_SHRINK THEN
    MAP_EVERY EXISTS_TAC [`z2:real^3`; `r2:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m2:real^3->real^3` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC MOI_LOR_SGN_EQ THEN
  MATCH_MP_TAC LOCAL_SIGN THEN
  MAP_EVERY EXISTS_TAC [`(phi:real^N->real^3) o (g:real^3->real^N)`; `ball(z:real^3,rho)`;
                        `z1:real^3`; `z2:real^3`] THEN
  ASM_REWRITE_TAC[OPEN_BALL; CONNECTED_BALL; o_THM]);;

let MOI_LOR_DATUM_CELL = prove
 (`!(c:(real^N->bool)->bool) (g:real^3->real^N) w a b d e l y z r a' b' d' e'.
     combinatorial_manifold_with_boundary 3 c /\
     (!x y. x IN w /\ y IN w /\ g x = g y ==> x = y) /\
     moi_lor_good c g w a b d e l y z r /\
     convex hull {a',b',d',e'} IN c /\ aff_dim(convex hull {a',b',d',e'}) = &3 /\
     g z IN convex hull {a',b',d',e'}
     ==> {a,b,d,e} = {a',b',d',e'}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^3->real^N`; `w:real^3->bool`;
                 `a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `l:real^3->real^N`;
                 `y:real^N`; `z:real^3`; `r:real`] MOI_LOR_GOOD_RELINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lor_good]) THEN
  SUBGOAL_THEN `convex hull {a,b,d,e} = convex hull {a':real^N,b',d',e'}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LOR_CELL_EQ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[INT_LE_REFL] THEN MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `(g:real^3->real^N) z`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LOR_VERTS_EQ THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MOI_LOR_TET]);;

let MOI_LOR_LOCAL_A = prove
 (`!(c:(real^N->bool)->bool) sg (g:real^3->real^N) w z a b d e u.
     combinatorial_manifold_with_boundary 3 c /\
     (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
                ==> (sg a b d e = &1 \/ sg a b d e = -- &1) /\
                    sg b a d e = --(sg a b d e) /\ sg a d b e = --(sg a b d e) /\
                    sg a b e d = --(sg a b d e)) /\
     open w /\ g continuous_on w /\ (!x y. x IN w /\ y IN w /\ g x = g y ==> x = y) /\
     IMAGE g w SUBSET UNIONS c /\ z IN w /\
     convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
     open u /\ g z IN u /\
     (!x. x IN u /\ x IN UNIONS c ==> x IN convex hull {a,b,d,e})
     ==> ?rho. &0 < rho /\
               !a1 b1 d1 e1 l1 y1 z1 r1 a2 b2 d2 e2 l2 y2 z2 r2.
                  moi_lor_good c g w a1 b1 d1 e1 l1 y1 z1 r1 /\ z1 IN ball(z,rho) /\
                  moi_lor_good c g w a2 b2 d2 e2 l2 y2 z2 r2 /\ z2 IN ball(z,rho)
                  ==> moi_lor_val sg l1 a1 b1 d1 e1 = moi_lor_val sg l2 a2 b2 d2 e2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] MOI_LOR_TET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] MOI_LOR_COORDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `L:real^N->real^3`]
    MOI_LOR_FLAT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^N`; `w:real^3->bool`; `u:real^N->bool`]
    CONTINUOUS_OPEN_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ball(z:real^3,rho) SUBSET w /\
                (!x. x IN ball(z,rho) ==> (g:real^3->real^N) x IN u)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ball(z:real^3,rho) SUBSET {x | x IN w /\ (g:real^3->real^N) x IN u}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ball(z:real^3,rho) ==> (g:real^3->real^N) x IN convex hull {a,b,d,e}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `u:real^N->bool`)) (concl th) && is_forall(concl th) &&
      can (find_term ((=) `UNIONS:((real^N->bool)->bool)->real^N->bool`)) (concl th))) THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^N) w SUBSET UNIONS c` THEN
    UNDISCH_TAC `ball(z:real^3,rho) SUBSET w` THEN UNDISCH_TAC `x IN ball(z:real^3,rho)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LOR_LOCAL_GENERIC THEN
  MAP_EVERY EXISTS_TAC [`\x:real^N. (L:real^N->real^3)(x - a)`;
                        `(sg:real^N->real^N->real^N->real^N->real) a b d e`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_LOR_AFFINE_CONT THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`x1:real^3`; `x2:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `w:real^3->bool`)) (concl th) && is_forall(concl th) &&
      not (can (find_term ((=) `u:real^N->bool`)) (concl th)))) THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ball(z:real^3,rho) SUBSET w` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `ball(z:real^3,rho) SUBSET w` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `L:real^N->real^3`)) (concl th) && is_forall(concl th))) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`a1:real^N`; `b1:real^N`; `d1:real^N`; `e1:real^N`;
                         `l:real^3->real^N`; `y1:real^N`; `z1:real^3`; `r1:real`] THEN
    STRIP_TAC THEN EXISTS_TAC `(L:real^N->real^3) o (l:real^3->real^N)` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lor_good]) THEN
    SUBGOAL_THEN `{a1,b1,d1,e1} = {a:real^N,b,d,e}` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_LOR_DATUM_CELL THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `g:real^3->real^N`;
                            `w:real^3->bool`; `l:real^3->real^N`; `y1:real^N`;
                            `z1:real^3`; `r1:real`] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `ball(z1:real^3,r1) SUBSET ball(z,rho)` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_lor_good c g w a b d e (l:real^3->real^N) y1 z1 r1` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_LOR_GOOD_HULL THEN
      MAP_EVERY EXISTS_TAC [`a1:real^N`; `b1:real^N`; `d1:real^N`; `e1:real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LOR_LIN_AT THEN
      MAP_EVERY EXISTS_TAC [`y1:real^N`; `r1:real`; `a:real^N`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[VECTOR_ARITH `(x + y) - a:real^N = x + y - a`];
      MP_TAC(ISPECL [`sg:real^N->real^N->real^N->real^N->real`;
                     `c:(real^N->bool)->bool`; `l:real^3->real^N`;
                     `a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`;
                     `a1:real^N`; `b1:real^N`; `d1:real^N`; `e1:real^N`]
        MOI_LOR_VAL_PERM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[moi_lor_val] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC MOI_LOR_SGN_COORDS THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_LOR_GOOD_SPAN THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `g:real^3->real^N`;
                            `w:real^3->bool`; `y1:real^N`; `z1:real^3`; `r1:real`] THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_LOR_FLIP_DET = prove
 (`!(L:real^N->real^3) (l:real^3->real^N).
     linear L /\ linear l
     ==> real_sgn(det(matrix((moi_lor_flip o L) o l))) =
         --real_sgn(det(matrix(L o l)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM o_ASSOC] THEN
  SUBGOAL_THEN `linear((L:real^N->real^3) o (l:real^3->real^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[LINEAR_COMPOSE]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; MOI_LOR_FLIP; DET_MUL] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID; REAL_SGN_NEG]);;

let MOI_LOR_LOCAL_B = prove
 (`!(c:(real^N->bool)->bool) sg (g:real^3->real^N) w z a b d e e' u.
     combinatorial_manifold_with_boundary 3 c /\
     (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
                ==> (sg a b d e = &1 \/ sg a b d e = -- &1) /\
                    sg b a d e = --(sg a b d e) /\ sg a d b e = --(sg a b d e) /\
                    sg a b e d = --(sg a b d e)) /\
     (!a b d e e'. ~(e = e') /\
                   convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
                   convex hull {a,b,d,e'} IN c /\ aff_dim(convex hull {a,b,d,e'}) = &3
                   ==> sg a b d e' = --(sg a b d e)) /\
     open w /\ g continuous_on w /\ (!x y. x IN w /\ y IN w /\ g x = g y ==> x = y) /\
     IMAGE g w SUBSET UNIONS c /\ z IN w /\ ~(e = e') /\
     convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
     convex hull {a,b,d,e'} IN c /\ aff_dim(convex hull {a,b,d,e'}) = &3 /\
     convex hull {a,b,d,e} INTER convex hull {a,b,d,e'} = convex hull {a,b,d} /\
     open u /\ g z IN u /\
     (!x. x IN u /\ x IN UNIONS c
          ==> x IN convex hull {a,b,d,e} UNION convex hull {a,b,d,e'})
     ==> ?rho. &0 < rho /\
               !a1 b1 d1 e1 l1 y1 z1 r1 a2 b2 d2 e2 l2 y2 z2 r2.
                  moi_lor_good c g w a1 b1 d1 e1 l1 y1 z1 r1 /\ z1 IN ball(z,rho) /\
                  moi_lor_good c g w a2 b2 d2 e2 l2 y2 z2 r2 /\ z2 IN ball(z,rho)
                  ==> moi_lor_val sg l1 a1 b1 d1 e1 = moi_lor_val sg l2 a2 b2 d2 e2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] MOI_LOR_TET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e':real^N`] MOI_LOR_TET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`] MOI_LOR_COORDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L1:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e':real^N`] MOI_LOR_COORDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L2:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `e':real^N`;
                 `L1:real^N->real^3`; `L2:real^N->real^3`] MOI_LOR_UNFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^N`; `w:real^3->bool`; `u:real^N->bool`]
    CONTINUOUS_OPEN_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ball(z:real^3,rho) SUBSET w /\
                (!x. x IN ball(z,rho) ==> (g:real^3->real^N) x IN u)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ball(z:real^3,rho) SUBSET {x | x IN w /\ (g:real^3->real^N) x IN u}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ball(z:real^3,rho)
        ==> (g:real^3->real^N) x IN convex hull {a,b,d,e} UNION convex hull {a,b,d,e'}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `u:real^N->bool`)) (concl th) && is_forall(concl th) &&
      can (find_term ((=) `UNIONS:((real^N->bool)->bool)->real^N->bool`)) (concl th))) THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^N) w SUBSET UNIONS c` THEN
    UNDISCH_TAC `ball(z:real^3,rho) SUBSET w` THEN UNDISCH_TAC `x IN ball(z:real^3,rho)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LOR_LOCAL_GENERIC THEN
  MAP_EVERY EXISTS_TAC
   [`moi_lor_unf (convex hull {a,b,d,e}) (a:real^N) (L1:real^N->real^3) L2`;
    `(sg:real^N->real^N->real^N->real^N->real) a b d e`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `convex hull {a,b,d,e} UNION convex hull {a:real^N,b,d,e'}` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`x1:real^3`; `x2:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `w:real^3->bool`)) (concl th) && is_forall(concl th) &&
      not (can (find_term ((=) `u:real^N->bool`)) (concl th)))) THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ball(z:real^3,rho) SUBSET w` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `ball(z:real^3,rho) SUBSET w` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `moi_lor_unf:(real^N->bool)->real^N->(real^N->real^3)->
                              (real^N->real^3)->real^N->real^3`)) (concl th) &&
      is_forall(concl th) && is_imp(snd(strip_forall(concl th))) &&
      is_eq(snd(dest_imp(snd(strip_forall(concl th))))) &&
      not (is_comb(rhs(snd(dest_imp(snd(strip_forall(concl th))))))))) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`a1:real^N`; `b1:real^N`; `d1:real^N`; `e1:real^N`;
                         `l:real^3->real^N`; `y1:real^N`; `z1:real^3`; `r1:real`] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lor_good]) THEN
    SUBGOAL_THEN `(g:real^3->real^N) z1 IN convex hull {a,b,d,e} UNION
                  convex hull {a,b,d,e'}` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `ball(z1:real^3,r1) SUBSET ball(z,rho)` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [EXISTS_TAC `(L1:real^N->real^3) o (l:real^3->real^N)` THEN
      SUBGOAL_THEN `{a1,b1,d1,e1} = {a:real^N,b,d,e}` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_LOR_DATUM_CELL THEN
        MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `g:real^3->real^N`;
                              `w:real^3->bool`; `l:real^3->real^N`; `y1:real^N`;
                              `z1:real^3`; `r1:real`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `moi_lor_good c g w a b d e (l:real^3->real^N) y1 z1 r1`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_LOR_GOOD_HULL THEN
        MAP_EVERY EXISTS_TAC [`a1:real^N`; `b1:real^N`; `d1:real^N`; `e1:real^N`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_LOR_LIN_AT THEN
        MAP_EVERY EXISTS_TAC [`y1:real^N`; `r1:real`; `a:real^N`] THEN
        ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(g:real^3->real^N) x IN convex hull {a,b,d,e}` ASSUME_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN
         `moi_lor_unf (convex hull {a,b,d,e}) a (L1:real^N->real^3) L2
            ((g:real^3->real^N) x) = L1(g x - a)`
        SUBST1_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            is_forall(concl th) &&
            can (find_term ((=) `L1:real^N->real^3`)) (concl th) &&
            not (can (find_term ((=) `moi_lor_flip`)) (concl th)) &&
            not (can (find_term ((=) `(UNION):(real^N->bool)->(real^N->bool)->real^N->bool`))
                   (concl th)))) THEN
          FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[VECTOR_ARITH `(x + y) - a:real^N = x + y - a`];
        MP_TAC(ISPECL [`sg:real^N->real^N->real^N->real^N->real`;
                       `c:(real^N->bool)->bool`; `l:real^3->real^N`;
                       `a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`;
                       `a1:real^N`; `b1:real^N`; `d1:real^N`; `e1:real^N`]
          MOI_LOR_VAL_PERM) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[moi_lor_val] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC MOI_LOR_SGN_COORDS THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MOI_LOR_GOOD_SPAN THEN
        MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `g:real^3->real^N`;
                              `w:real^3->bool`; `y1:real^N`; `z1:real^3`; `r1:real`] THEN
        ASM_REWRITE_TAC[]];
      EXISTS_TAC `(moi_lor_flip o (L2:real^N->real^3)) o (l:real^3->real^N)` THEN
      SUBGOAL_THEN `{a1,b1,d1,e1} = {a:real^N,b,d,e'}` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_LOR_DATUM_CELL THEN
        MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `g:real^3->real^N`;
                              `w:real^3->bool`; `l:real^3->real^N`; `y1:real^N`;
                              `z1:real^3`; `r1:real`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `moi_lor_good c g w a b d e' (l:real^3->real^N) y1 z1 r1`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_LOR_GOOD_HULL THEN
        MAP_EVERY EXISTS_TAC [`a1:real^N`; `b1:real^N`; `d1:real^N`; `e1:real^N`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_LOR_LIN_AT THEN
        MAP_EVERY EXISTS_TAC [`y1:real^N`; `r1:real`; `a:real^N`] THEN
        CONJ_TAC THENL [ASM_SIMP_TAC[LINEAR_COMPOSE; MOI_LOR_FLIP]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(g:real^3->real^N) x IN convex hull {a,b,d,e'}` ASSUME_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN
         `moi_lor_unf (convex hull {a,b,d,e}) a (L1:real^N->real^3) L2
            ((g:real^3->real^N) x) = moi_lor_flip(L2(g x - a))`
        SUBST1_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            is_forall(concl th) &&
            can (find_term ((=) `moi_lor_flip`)) (concl th) &&
            not (can (find_term ((=) `(UNION):(real^N->bool)->(real^N->bool)->real^N->bool`))
                   (concl th)))) THEN
          FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[o_THM; VECTOR_ARITH `(x + y) - a:real^N = x + y - a`];
        MP_TAC(ISPECL [`sg:real^N->real^N->real^N->real^N->real`;
                       `c:(real^N->bool)->bool`; `l:real^3->real^N`;
                       `a:real^N`; `b:real^N`; `d:real^N`; `e':real^N`;
                       `a1:real^N`; `b1:real^N`; `d1:real^N`; `e1:real^N`]
          MOI_LOR_VAL_PERM) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[moi_lor_val] THEN
        MP_TAC(ISPECL [`L2:real^N->real^3`; `l:real^3->real^N`] MOI_LOR_FLIP_DET) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e':real^N`;
                       `L2:real^N->real^3`; `l:real^3->real^N`] MOI_LOR_SGN_COORDS) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LOR_GOOD_SPAN THEN
          MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `g:real^3->real^N`;
                                `w:real^3->bool`; `y1:real^N`; `z1:real^3`; `r1:real`] THEN
          ASM_REWRITE_TAC[];
          DISCH_THEN SUBST1_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`;
                                      `e':real^N`] o check (fun th ->
          is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 5)) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]]]);;

let MOI_LOR_LOCAL = prove
 (`!(c:(real^N->bool)->bool) sg (g:real^3->real^N) w z.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
                ==> (sg a b d e = &1 \/ sg a b d e = -- &1) /\
                    sg b a d e = --(sg a b d e) /\ sg a d b e = --(sg a b d e) /\
                    sg a b e d = --(sg a b d e)) /\
     (!a b d e e'. ~(e = e') /\
                   convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
                   convex hull {a,b,d,e'} IN c /\ aff_dim(convex hull {a,b,d,e'}) = &3
                   ==> sg a b d e' = --(sg a b d e)) /\
     open w /\ g continuous_on w /\ (!x y. x IN w /\ y IN w /\ g x = g y ==> x = y) /\
     IMAGE g w SUBSET UNIONS c DIFF complex_boundary c /\
     z IN w /\ ~(g z IN UNIONS {t | t IN c /\ aff_dim t <= &1})
     ==> ?rho. &0 < rho /\
               !a1 b1 d1 e1 l1 y1 z1 r1 a2 b2 d2 e2 l2 y2 z2 r2.
                  moi_lor_good c g w a1 b1 d1 e1 l1 y1 z1 r1 /\ z1 IN ball(z,rho) /\
                  moi_lor_good c g w a2 b2 d2 e2 l2 y2 z2 r2 /\ z2 IN ball(z,rho)
                  ==> moi_lor_val sg l1 a1 b1 d1 e1 = moi_lor_val sg l2 a2 b2 d2 e2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^N) w SUBSET UNIONS c /\
                (g:real^3->real^N) z IN UNIONS c /\ ~(g z IN complex_boundary c)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^3->real^N) w SUBSET UNIONS c DIFF complex_boundary c` THEN
    UNDISCH_TAC `(z:real^3) IN w` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(g:real^3->real^N) z`]
    MOI_LOR_LOCAL_STRUCT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC MOI_LOR_LOCAL_A THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`;
                          `u:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_LOR_LOCAL_B THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`; `e':real^N`;
                          `u:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Good balls are dense in w (points off finitely many negligible           *)
(* convex frontiers, twice: first for the polytopes of the PL structure,    *)
(* then for the preimages of the simplices of c).                           *)
(* ========================================================================= *)

let MOI_LOR_AVOID_FRONTIERS = prove
 (`!(f:(real^3->bool)->bool) s.
     FINITE f /\ (!k. k IN f ==> convex k) /\ open s /\ ~(s = {})
     ==> ?x. x IN s /\ !k. k IN f ==> ~(x IN frontier k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `negligible(UNIONS (IMAGE frontier (f:(real^3->bool)->bool)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; NEGLIGIBLE_CONVEX_FRONTIER];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((s:real^3->bool) SUBSET UNIONS (IMAGE frontier f))` MP_TAC THENL
   [DISCH_TAC THEN MP_TAC(ISPEC `s:real^3->bool` OPEN_NOT_NEGLIGIBLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NEGLIGIBLE_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM; NOT_FORALL_THM; NOT_IMP] THEN
  MESON_TAC[]);;

let MOI_LOR_IN_INTERIOR = prove
 (`!k (x:real^3). x IN k /\ ~(x IN frontier k) ==> x IN interior k`,
  REWRITE_TAC[frontier; IN_DIFF] THEN MESON_TAC[CLOSURE_SUBSET; SUBSET]);;

let MOI_LOR_PREIMAGE_CONVEX = prove
 (`!(l:real^3->real^N) y t.
     linear l /\ convex t ==> convex {x | l x + y IN t}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[convex; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x1:real^3`; `x2:real^3`; `u:real`; `v:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(l:real^3->real^N)(u % x1 + v % x2) + y = u % (l x1 + y) + v % (l x2 + y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATCH_MP LINEAR_ADD (ASSUME `linear (l:real^3->real^N)`);
                MATCH_MP LINEAR_CMUL (ASSUME `linear (l:real^3->real^N)`)] THEN
    UNDISCH_TAC `u + v = &1` THEN REWRITE_TAC[REAL_ARITH `u + v = &1 <=> u = &1 - v`] THEN
    DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[convex]) THEN ASM_REWRITE_TAC[]]);;

let MOI_LOR_DENSE = prove
 (`!(c:(real^N->bool)->bool) (g:real^3->real^N) w z rho.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     open w /\ pl_map_on w g /\ (!x y. x IN w /\ y IN w /\ g x = g y ==> x = y) /\
     IMAGE g w SUBSET UNIONS c /\ z IN w /\ &0 < rho
     ==> ?a b d e l y z1 r1. moi_lor_good c g w a b d e l y z1 r1 /\ z1 IN ball(z,rho)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:real^3` o GEN_REWRITE_RULE I [pl_map_on]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:(real^3->bool)->bool` (X_CHOOSE_THEN `u:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`cc:(real^3->bool)->bool`; `ball(z:real^3,rho) INTER u INTER w`]
    MOI_LOR_AVOID_FRONTIERS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; OPEN_INTER; OPEN_BALL] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z:real^3` THEN
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z2:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?k:real^3->bool. k IN cc /\ z2 IN k` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `w INTER u SUBSET UNIONS (cc:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `(z2:real^3) IN ball(z,rho) INTER u INTER w` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope (k:real^3->bool) /\ k SUBSET w /\
                ?l:real^3->real^N y. linear l /\ !x. x IN k ==> g x = l x + y`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l:real^3->real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(z2:real^3) IN interior k` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LOR_IN_INTERIOR THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `interior k INTER ball(z:real^3,rho) INTER u INTER w` OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR; OPEN_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z2:real^3`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN ball(z2:real^3,r2) ==> x IN k /\ x IN w /\ x IN ball(z,rho)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `k:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `ball(z2:real^3,r2) SUBSET interior k INTER ball(z,rho) INTER u INTER w` THEN
    UNDISCH_TAC `(x:real^3) IN ball(z2,r2)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u' v'. (l:real^3->real^N) u' = l v' ==> u' = v'` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LOR_LINEAR_INJ THEN
    MAP_EVERY EXISTS_TAC [`y:real^N`; `z2:real^3`; `r2:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `w:real^3->bool`)) (concl th) && is_forall(concl th) &&
      can (find_term ((=) `g:real^3->real^N`)) (concl th) &&
      not (can (find_term ((=) `ball:real^3#real->real^3->bool`)) (concl th)))) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\t. {x:real^3 | (l:real^3->real^N) x + y IN t}) c`;
                 `ball(z2:real^3,r2)`] MOI_LOR_AVOID_FRONTIERS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; OPEN_BALL; BALL_EQ_EMPTY;
                 REAL_NOT_LE] THEN
    X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_LOR_PREIMAGE_CONVEX THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z3:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?t:real^N->bool. t IN c /\ (l:real^3->real^N) z3 + y IN t`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(g:real^3->real^N) z3 IN UNIONS c` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^3->real^N) w SUBSET UNIONS c` THEN
      MATCH_MP_TAC(SET_RULE `x IN w ==> IMAGE (g:real^3->real^N) w SUBSET s ==> g x IN s`) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^3->real^N) z3 = l z3 + y` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z3:real^3) IN interior {x | (l:real^3->real^N) x + y IN t}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LOR_IN_INTERIOR THEN ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPEC `interior {x | (l:real^3->real^N) x + y IN t} INTER ball(z2:real^3,r2)`
    OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR; OPEN_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z3:real^3`) THEN ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN ball(z3:real^3,r3)
                    ==> (l:real^3->real^N) x + y IN t /\ x IN ball(z2,r2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `{x | (l:real^3->real^N) x + y IN t}` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `ball(z3:real^3,r3) SUBSET
                 interior {x | (l:real^3->real^N) x + y IN t} INTER ball(z2,r2)` THEN
    UNDISCH_TAC `(x:real^3) IN ball(z3,r3)` THEN REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(t:real^N->bool) = &3` ASSUME_TAC THENL
   [MATCH_MP_TAC(INT_ARITH `a <= &3 /\ &3 <= a ==> a:int = &3`) THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `c:(real^N->bool)->bool` CM_WB_DIM) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (\x. y + x) (IMAGE (l:real^3->real^N) (ball(z3,r3)))`;
                   `t:real^N->bool`] AFF_DIM_SUBSET) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[AFF_DIM_TRANSLATION_EQ] THEN
    MP_TAC(ISPECL [`l:real^3->real^N`; `ball(z3:real^3,r3)`]
      AFF_DIM_INJECTIVE_LINEAR_IMAGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[AFF_DIM_BALL; DIMINDEX_3];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_LOR_SIMPLEX_3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `d:real^N` (X_CHOOSE_THEN `e:real^N` SUBST_ALL_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`;
                        `l:real^3->real^N`; `y:real^N`; `z3:real^3`; `r3:real`] THEN
  ASM_REWRITE_TAC[moi_lor_good] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^3->real^N) x = l x + y` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* The points of w over the complement of the 1-skeleton form a             *)
(* connected set: the preimage of the 1-skeleton has dimension <= 1         *)
(* (compact pieces homeomorphic via g to subsets of the 1-skeleton).        *)
(* ========================================================================= *)

let MOI_LOR_SKEL_DIM = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c
     ==> closed(UNIONS {t | t IN c /\ aff_dim t <= &1}) /\
         dimension(UNIONS {t | t IN c /\ aff_dim t <= &1}) <= &1`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN c ==> closed t /\ convex t` ASSUME_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_CLOSED];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
    MATCH_MP_TAC DIMENSION_LE_UNIONS THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_IMP_COUNTABLE; IN_ELIM_THM] THEN
    CONV_TAC INT_REDUCE_CONV THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CLOSED_IMP_FSIGMA; DIMENSION_EQ_AFF_DIM]]);;

let MOI_LOR_PRE_DIM = prove
 (`!(g:real^3->real^N) w k.
     open w /\ g continuous_on w /\ (!x y. x IN w /\ y IN w /\ g x = g y ==> x = y) /\
     closed k /\ dimension k <= &1
     ==> dimension {x | x IN w /\ g x IN k} <= &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_COUNTABLE_UNION_CLOSED_INTERVALS) THEN
  DISCH_THEN(X_CHOOSE_THEN `D:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `{x | x IN w /\ (g:real^3->real^N) x IN k} =
    UNIONS (IMAGE (\i. {x | x IN i /\ g x IN k}) D)`
  SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; EXTENSION] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      UNDISCH_TAC `UNIONS D = (w:real^3->bool)` THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `i:real^3->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC DIMENSION_LE_UNIONS THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
  CONV_TAC INT_REDUCE_CONV THEN X_GEN_TAC `i:real^3->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(i:real^3->bool) SUBSET w /\ closed i /\ bounded i` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:real^3->bool` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `D:(real^3->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[CLOSED_INTERVAL; BOUNDED_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^N) continuous_on i` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `closed {x | x IN i /\ (g:real^3->real^N) x IN k}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CLOSED_IMP_FSIGMA] THEN
  SUBGOAL_THEN
   `{x | x IN i /\ (g:real^3->real^N) x IN k} homeomorphic
    IMAGE g {x | x IN i /\ g x IN k}`
  ASSUME_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN EXISTS_TAC `g:real^3->real^N` THEN
    MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `i:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `i:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP HOMEOMORPHIC_DIMENSION) THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `dimension(k:real^N->bool)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIMENSION_SUBSET THEN SET_TAC[]);;

let MOI_LOR_V_CONNECTED = prove
 (`!(c:(real^N->bool)->bool) (g:real^3->real^N) w.
     FINITE c /\ lf_simplicial_complex c /\
     open w /\ connected w /\ g continuous_on w /\
     (!x y. x IN w /\ y IN w /\ g x = g y ==> x = y)
     ==> connected {x | x IN w /\ ~(g x IN UNIONS {t | t IN c /\ aff_dim t <= &1})}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LOR_SKEL_DIM) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN w /\ ~((g:real^3->real^N) x IN UNIONS {t | t IN c /\ aff_dim t <= &1})} =
    w DIFF {x | x IN w /\ g x IN UNIONS {t | t IN c /\ aff_dim t <= &1}}`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_OPEN_DIFF_LOWDIM THEN ASM_REWRITE_TAC[DIMINDEX_3] THEN
  CONV_TAC INT_REDUCE_CONV THEN MATCH_MP_TAC MOI_LOR_PRE_DIM THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Assembly.  The value is locally constant on the connected set            *)
(* of points of w over the complement of the 1-skeleton, good balls are     *)
(* dense and centred there, so all good balls have one value.               *)
(* ========================================================================= *)

let MOI_LOR_OPEN_LOCAL = prove
 (`!P:real^3->bool. open {z | ?rho. &0 < rho /\ !z1. z1 IN ball(z,rho) ==> P z1}`,
  GEN_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `z':real^3` THEN DISCH_TAC THEN EXISTS_TAC `rho - dist(z:real^3,z')` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `z' IN ball(z:real^3,rho)` THEN REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z1:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `z1 IN ball(z':real^3,rho - dist(z,z'))` THEN REWRITE_TAC[IN_BALL] THEN
  NORM_ARITH_TAC);;

let MOI_LOR_MAIN = prove
 (`!(c:(real^N->bool)->bool) sg (g:real^3->real^N) w.
    FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
    (!a b d e. convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
               ==> (sg a b d e = &1 \/ sg a b d e = -- &1) /\
                   sg b a d e = --(sg a b d e) /\ sg a d b e = --(sg a b d e) /\
                   sg a b e d = --(sg a b d e)) /\
    (!a b d e e'. ~(e = e') /\
                  convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
                  convex hull {a,b,d,e'} IN c /\ aff_dim(convex hull {a,b,d,e'}) = &3
                  ==> sg a b d e' = --(sg a b d e)) /\
    open w /\ connected w /\ pl_map_on w g /\
    (!x y. x IN w /\ y IN w /\ g x = g y ==> x = y) /\
    IMAGE g w SUBSET UNIONS c DIFF complex_boundary c
    ==> ?s. (s = &1 \/ s = -- &1) /\
            !a b d e (l:real^3->real^N) y z r.
               moi_lor_good c g w a b d e l y z r ==> moi_lor_val sg l a b d e = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^N) continuous_on w` ASSUME_TAC THENL
   [ASM_MESON_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^N) w SUBSET UNIONS c` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^3->real^N) w SUBSET UNIONS c DIFF complex_boundary c` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?a b d e (l:real^3->real^N) y z r. moi_lor_good c g w a b d e l y z r`
  THENL [ALL_TAC; EXISTS_TAC `&1` THEN ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a0:real^N` (X_CHOOSE_THEN `b0:real^N`
    (X_CHOOSE_THEN `d0:real^N` (X_CHOOSE_THEN `e0:real^N`
    (X_CHOOSE_THEN `l0:real^3->real^N` (X_CHOOSE_THEN `y0:real^N`
    (X_CHOOSE_THEN `z0:real^3` (X_CHOOSE_TAC `r0:real`)))))))) THEN
  ABBREV_TAC
   `s0 = moi_lor_val (sg:real^N->real^N->real^N->real^N->real) l0 a0 b0 d0 e0` THEN
  EXISTS_TAC `s0:real` THEN CONJ_TAC THENL
   [EXPAND_TAC "s0" THEN MATCH_MP_TAC MOI_LOR_GOOD_PM1 THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `g:real^3->real^N`;
                          `w:real^3->bool`; `y0:real^N`; `z0:real^3`; `r0:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `V = {x | x IN w /\
             ~((g:real^3->real^N) x IN UNIONS {t | t IN c /\ aff_dim t <= &1})}` THEN
  SUBGOAL_THEN
   `!a b d e (l:real^3->real^N) y z r.
       moi_lor_good c g w a b d e l y z r ==> (z:real^3) IN V`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lor_good]) THEN
      UNDISCH_TAC `ball(z:real^3,r) SUBSET w` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      MATCH_MP_TAC MOI_LOR_GOOD_OFF_SKEL THEN
      MAP_EVERY EXISTS_TAC [`w:real^3->bool`; `a:real^N`; `b:real^N`; `d:real^N`;
                            `e:real^N`; `l:real^3->real^N`; `y:real^N`; `r:real`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `A = {z:real^3 | ?rho. &0 < rho /\
           !z1. z1 IN ball(z,rho)
                ==> !a b d e (l:real^3->real^N) y r.
                      moi_lor_good c g w a b d e l y z1 r
                      ==> moi_lor_val sg l a b d e = s0}` THEN
  ABBREV_TAC
   `B = {z:real^3 | ?rho. &0 < rho /\
           !z1. z1 IN ball(z,rho)
                ==> !a b d e (l:real^3->real^N) y r.
                      moi_lor_good c g w a b d e l y z1 r
                      ==> ~(moi_lor_val sg l a b d e = s0)}` THEN
  SUBGOAL_THEN `open(A:real^3->bool) /\ open(B:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC
       `\z1:real^3. !a b d e (l:real^3->real^N) y r.
          moi_lor_good c g w a b d e l y z1 r ==> moi_lor_val sg l a b d e = s0`
       MOI_LOR_OPEN_LOCAL) THEN REWRITE_TAC[];
      MP_TAC(ISPEC
       `\z1:real^3. !a b d e (l:real^3->real^N) y r.
          moi_lor_good c g w a b d e l y z1 r ==> ~(moi_lor_val sg l a b d e = s0)`
       MOI_LOR_OPEN_LOCAL) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(V:real^3->bool) SUBSET A UNION B` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real^N->real`;
                   `g:real^3->real^N`; `w:real^3->bool`; `z:real^3`] MOI_LOR_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:real^3) IN V` THEN EXPAND_TAC "V" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_CASES_TAC
     `?a b d e (l:real^3->real^N) y z1 r.
        moi_lor_good c g w a b d e l y z1 r /\ z1 IN ball(z,rho) /\
        moi_lor_val sg l a b d e = s0`
    THENL
     [DISJ1_TAC THEN EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `a1:real^N` (X_CHOOSE_THEN `b1:real^N`
        (X_CHOOSE_THEN `d1:real^N` (X_CHOOSE_THEN `e1:real^N`
        (X_CHOOSE_THEN `l1:real^3->real^N` (X_CHOOSE_THEN `y1:real^N`
        (X_CHOOSE_THEN `z1:real^3` (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)))))))) THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^3->bool) INTER B INTER V = {}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `z:real^3` THEN
    MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `rho1:real` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `rho2:real` STRIP_ASSUME_TAC) MP_TAC)) THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^3->real^N`; `w:real^3->bool`;
                   `z:real^3`; `min rho1 rho2`] MOI_LOR_DENSE) THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    DISCH_THEN(X_CHOOSE_THEN `a1:real^N` (X_CHOOSE_THEN `b1:real^N`
      (X_CHOOSE_THEN `d1:real^N` (X_CHOOSE_THEN `e1:real^N`
      (X_CHOOSE_THEN `l1:real^3->real^N` (X_CHOOSE_THEN `y1:real^N`
      (X_CHOOSE_THEN `z1:real^3` (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)))))))) THEN
    SUBGOAL_THEN `(z1:real^3) IN ball(z,rho1) /\ z1 IN ball(z,rho2)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z1:real^3) IN ball(z,min rho1 rho2)` THEN
      REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z0:real^3) IN A` ASSUME_TAC THENL
   [SUBGOAL_THEN `(z0:real^3) IN V` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((z0:real^3) IN B)` MP_TAC THENL
     [EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z0:real^3`) THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
      DISCH_THEN(MP_TAC o SPECL [`a0:real^N`; `b0:real^N`; `d0:real^N`; `e0:real^N`;
                                 `l0:real^3->real^N`; `y0:real^N`; `r0:real`]) THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((A:real^3->bool) INTER V = {})` ASSUME_TAC THENL
   [SUBGOAL_THEN `(z0:real^3) IN V` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(z0:real^3) IN A` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(B:real^3->bool) INTER V = {}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^3->real^N`; `w:real^3->bool`]
      MOI_LOR_V_CONNECTED) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[connected] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`A:real^3->bool`; `B:real^3->bool`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`;
                       `l:real^3->real^N`; `y:real^N`; `z:real^3`; `r:real`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN A` MP_TAC THENL
   [SUBGOAL_THEN `(z:real^3) IN V` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `d:real^N`; `e:real^N`;
                             `l:real^3->real^N`; `y:real^N`; `r:real`]) THEN
  ASM_REWRITE_TAC[]);;

let ORIENT_SIGN = prove
 (MOI_LT_ORIENT_SIGN,
  MP_TAC MOI_LOR_MAIN THEN REWRITE_TAC[moi_lor_good; moi_lor_val; moi_lor_mat]);;


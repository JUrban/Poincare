(* ========================================================================= *)
(* pc_moi_s34_torus: circles on a torus surface and H_1, for the H_1 clause *)
(* of the Sec 34 face-ball invariant after Operation 1 (Moise Sec 34, Lemma *)
(* 6, which does not check it) and for op1b.  Route: the universal cover of *)
(* S1 x S1; a periodic simple curve separates the plane (Jordan curve       *)
(* theorem in the punctured plane, MOI_S4U_LINE_SEP); hence loops missing   *)
(* an essential circle are parallel to it, simple closed curves have        *)
(* primitive displacements, and such loops are homotopic to loops in the    *)
(* circle (MOI_S4U_TT_CURVE_LOOPS, MOI_S4U_CURVE_LOOPS).  Main results, for *)
(* any torus_surface th: MOI_S4U_T1 (a carrying union of circles has a      *)
(* carrying component) and MOI_S4U_SEP (Mayer-Vietoris on an open cover of  *)
(* th).  The PL bridges at the end use PL_SOLID_TORUS_BASIC                 *)
(* (pc_moi_fnd_plst).                                                       *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_h1.ml";;
needs "src/pc_moi_s34_h1.ml";;
needs "src/pc_moi_fnd_plst.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Separation by a periodic curve.  For d <> 0 the map moi_s4u_cyl d        *)
(* identifies real^2 / (Z d) with the punctured plane (the d-coordinate     *)
(* becomes the angle, the transverse coordinate det(d,x) the log of the    *)
(* modulus).  A d-periodic simple curve maps onto a Jordan curve with      *)
(* winding number 1 around 0, so it separates the far half planes of the   *)
(* transverse coordinate (MOI_S4U_LINE_SEP).                               *)
(* ------------------------------------------------------------------------- *)

let moi_s4u_nu = new_definition
 `moi_s4u_nu (d:real^2) (x:real^2) = d$1 * x$2 - d$2 * x$1`;;

let moi_s4u_cyl = new_definition
 `moi_s4u_cyl (d:real^2) (x:real^2) =
    cexp(Cx(moi_s4u_nu d x) + ii * Cx(&2 * pi * (d dot x) / (d dot d)))`;;

let MOI_S4U_NU_LINEAR = prove
 (`!d x y:real^2 a.
     moi_s4u_nu d (x + y) = moi_s4u_nu d x + moi_s4u_nu d y /\
     moi_s4u_nu d (a % x) = a * moi_s4u_nu d x /\
     moi_s4u_nu d (x - y) = moi_s4u_nu d x - moi_s4u_nu d y /\
     moi_s4u_nu d d = &0`,
  REWRITE_TAC[moi_s4u_nu; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VECTOR_SUB_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S4U_CYL_EQ = prove
 (`!d x y:real^2.
     ~(d = vec 0)
     ==> (moi_s4u_cyl d x = moi_s4u_cyl d y <=> ?n. integer n /\ x = y + n % d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s4u_cyl; CEXP_EQ] THEN
  SUBGOAL_THEN `&0 < (d:real^2) dot d` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `integer (n:real)` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [COMPLEX_EQ] THEN
  REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_II; IM_MUL_II;
              REAL_NEG_0; REAL_ADD_RID; REAL_ADD_LID] THEN
  REWRITE_TAC[moi_s4u_nu; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; DOT_2] THEN
  UNDISCH_TAC `&0 < (d:real^2) dot d` THEN REWRITE_TAC[DOT_2] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!a b. &2 * pi * a / ((d:real^2)$1 * d$1 + d$2 * d$2) =
                      &2 * pi * b / (d$1 * d$1 + d$2 * d$2) + &2 * n * pi <=>
                      a = b + n * (d$1 * d$1 + d$2 * d$2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MP_TAC PI_POS THEN
    UNDISCH_TAC `&0 < (d:real^2)$1 * d$1 + d$2 * d$2` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(x - y - n % d:real^2)$1 = &0 /\ (x - y - n % d:real^2)$2 = &0`
    MP_TAC THENL
     [REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      ABBREV_TAC `w1 = (x:real^2)$1 - (y:real^2)$1 - n * (d:real^2)$1` THEN
      ABBREV_TAC `w2 = (x:real^2)$2 - (y:real^2)$2 - n * (d:real^2)$2` THEN
      SUBGOAL_THEN `(d:real^2)$1 * w2 = d$2 * w1 /\ d$1 * w1 + d$2 * w2 = &0`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["w1"; "w2"] THEN
        MAP_EVERY UNDISCH_TAC
         [`(d:real^2)$1 * (x:real^2)$2 - d$2 * x$1 = d$1 * (y:real^2)$2 - d$2 * y$1`;
          `(d:real^2)$1 * (x:real^2)$1 + d$2 * x$2 =
           (d$1 * (y:real^2)$1 + d$2 * y$2) + n * (d$1 * d$1 + d$2 * d$2)`] THEN
        CONV_TAC REAL_RING;
        ALL_TAC] THEN
      SUBGOAL_THEN `((d:real^2)$1 * d$1 + d$2 * d$2) * w1 = &0 /\
                    ((d:real^2)$1 * d$1 + d$2 * d$2) * w2 = &0` MP_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(d:real^2)$1 * w2 = d$2 * w1`;
                               `(d:real^2)$1 * w1 + d$2 * w2 = &0`] THEN
        CONV_TAC REAL_RING;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ENTIRE] THEN
      UNDISCH_TAC `&0 < (d:real^2)$1 * d$1 + d$2 * d$2` THEN REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC];
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING]);;

let MOI_S4U_CYL_NORM = prove
 (`!d x:real^2. norm(moi_s4u_cyl d x) = exp(moi_s4u_nu d x)`,
  REWRITE_TAC[moi_s4u_cyl; NORM_CEXP; RE_ADD; RE_CX; RE_MUL_II; IM_CX;
              REAL_NEG_0; REAL_ADD_RID]);;

let MOI_S4U_CYL_ALT = prove
 (`!d x:real^2.
     moi_s4u_cyl d x =
     cexp(Cx(vector[--(d$2); d$1] dot x) + ii * Cx(((&2 * pi) / (d dot d)) % d dot x))`,
  REWRITE_TAC[moi_s4u_cyl; moi_s4u_nu; DOT_LMUL] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[DOT_2; VECTOR_2] THEN AP_TERM_TAC THEN BINOP_TAC THEN AP_TERM_TAC THENL
   [REAL_ARITH_TAC; AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

let MOI_S4U_CYL_LOG_CONTINUOUS = prove
 (`!d (s:real^2->bool).
     (\x. Cx(vector[--(d$2); d$1] dot x) + ii * Cx(((&2 * pi) / (d dot d)) % d dot x))
     continuous_on s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  REWRITE_TAC[CONTINUOUS_ON_CX_DOT] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN REWRITE_TAC[CONTINUOUS_ON_CX_DOT]);;

let MOI_S4U_CYL_CONTINUOUS = prove
 (`!d s. moi_s4u_cyl d continuous_on s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `moi_s4u_cyl d = cexp o
     (\x:real^2. Cx(vector[--(d$2); d$1] dot x) + ii * Cx(((&2 * pi) / (d dot d)) % d dot x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MOI_S4U_CYL_ALT]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  REWRITE_TAC[CONTINUOUS_ON_CEXP; MOI_S4U_CYL_LOG_CONTINUOUS]);;

(* The image in the punctured plane of a d-periodic simple curve is a      *)
(* Jordan curve with winding number 1 around 0, so 0 is inside it.         *)

let MOI_S4U_CYL_JORDAN = prove
 (`!(g:real^1->real^2) d.
     path g /\ ~(d = vec 0) /\ pathfinish g = pathstart g + d /\
     (!s t n. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
              integer n /\ g s = g t + n % d
              ==> s = t \/ (s = vec 0 /\ t = vec 1) \/ (s = vec 1 /\ t = vec 0))
     ==> path (moi_s4u_cyl d o g) /\
         pathfinish (moi_s4u_cyl d o g) = pathstart (moi_s4u_cyl d o g) /\
         simple_path (moi_s4u_cyl d o g) /\
         winding_number(moi_s4u_cyl d o g,Cx(&0)) = Cx(&1) /\
         Cx(&0) IN inside(path_image (moi_s4u_cyl d o g))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `p = moi_s4u_cyl d o (g:real^1->real^2)` THEN
  SUBGOAL_THEN `path (p:real^1->complex)` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[MOI_S4U_CYL_CONTINUOUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathfinish (p:real^1->complex) = pathstart p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
    ASM_SIMP_TAC[MOI_S4U_CYL_EQ] THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[INTEGER_CLOSED; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `simple_path (p:real^1->complex)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[simple_path] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `t:real^1`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(p:real^1->complex) s = p t` THEN EXPAND_TAC "p" THEN
    REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[MOI_S4U_CYL_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `integer:real->bool`)) (concl th))) THEN
    EXISTS_TAC `n:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the winding number of p around 0 is 1 *)
  SUBGOAL_THEN `winding_number(p,Cx(&0)) = Cx(&1)` ASSUME_TAC THENL
   [ABBREV_TAC `f = (\x:real^2. Cx(vector[--(d$2); d$1] dot x) +
                                ii * Cx(((&2 * pi) / (d dot d)) % d dot x))` THEN
    SUBGOAL_THEN `p = cexp o ((f:real^2->complex) o (g:real^1->real^2))` SUBST1_TAC THENL
     [EXPAND_TAC "p" THEN EXPAND_TAC "f" THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM; MOI_S4U_CYL_ALT];
      ALL_TAC] THEN
    SUBGOAL_THEN `path ((f:real^2->complex) o (g:real^1->real^2))` ASSUME_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "f" THEN REWRITE_TAC[MOI_S4U_CYL_LOG_CONTINUOUS];
      ALL_TAC] THEN
    ASM_SIMP_TAC[WINDING_NUMBER_COMPOSE_CEXP] THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f:real^2->complex) (pathstart g + d) - f (pathstart g) =
                  ii * Cx(&2 * pi)` SUBST1_TAC THENL
     [EXPAND_TAC "f" THEN
      REWRITE_TAC[DOT_RADD; DOT_LMUL; REAL_ADD_LDISTRIB; CX_ADD] THEN
      SUBGOAL_THEN `vector[--((d:real^2)$2); d$1] dot d = &0` SUBST1_TAC THENL
       [REWRITE_TAC[DOT_2; VECTOR_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(&2 * pi) / ((d:real^2) dot d) * (d dot d) = &2 * pi` SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MP_TAC PI_NZ THEN REWRITE_TAC[GSYM CX_INJ] THEN
    REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPEC `p:real^1->complex` JORDAN_INSIDE_OUTSIDE) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  (* 0 is inside *)
  SUBGOAL_THEN `~(Cx(&0) IN path_image (p:real^1->complex))` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[PATH_IMAGE_COMPOSE; IN_IMAGE] THEN
    REWRITE_TAC[moi_s4u_cyl; CEXP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx(&0) IN outside(path_image (p:real^1->complex)))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`p:real^1->complex`; `Cx(&0)`] WINDING_NUMBER_ZERO_IN_OUTSIDE) THEN
    ASM_REWRITE_TAC[CX_INJ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MAP_EVERY UNDISCH_TAC
   [`inside(path_image (p:real^1->complex)) UNION outside(path_image p) =
     (:complex) DIFF path_image p`;
    `~(Cx(&0) IN path_image (p:real^1->complex))`;
    `~(Cx(&0) IN outside(path_image (p:real^1->complex)))`] THEN
  SET_TAC[]);;

(* The separation lemma.  g is a path in real^2 with pathfinish = pathstart *)
(* + d, injective on [0,1) modulo Z d; its periodic extension is the set    *)
(* of the g t + n % d.                                                      *)

let MOI_S4U_LINE_SEP = prove
 (`!(g:real^1->real^2) d.
     path g /\ ~(d = vec 0) /\ pathfinish g = pathstart g + d /\
     (!s t n. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
              integer n /\ g s = g t + n % d
              ==> s = t \/ (s = vec 0 /\ t = vec 1) \/ (s = vec 1 /\ t = vec 0))
     ==> ?K. !S. connected S /\
                 (!x t n. x IN S /\ t IN interval[vec 0,vec 1] /\ integer n
                          ==> ~(x = g t + n % d))
                 ==> ~((?x. x IN S /\ K < moi_s4u_nu d x) /\
                       (?x. x IN S /\ moi_s4u_nu d x < --K))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g:real^1->real^2`; `d:real^2`] MOI_S4U_CYL_JORDAN) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `p = moi_s4u_cyl d o (g:real^1->real^2)` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `p:real^1->complex` JORDAN_INSIDE_OUTSIDE) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(Cx(&0),r) SUBSET inside(path_image (p:real^1->complex))`
  (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `?R. &0 < R /\ path_image (p:real^1->complex) SUBSET cball(Cx(&0),R)`
  (X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THENL
   [MATCH_MP_TAC BOUNDED_SUBSET_CBALL THEN MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_PATH_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(:complex) DIFF cball(Cx(&0),R) SUBSET outside(path_image (p:real^1->complex))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OUTSIDE_SUBSET_CONVEX THEN ASM_REWRITE_TAC[CONVEX_CBALL]; ALL_TAC] THEN
  EXISTS_TAC `abs(log R) + abs(log r)` THEN
  X_GEN_TAC `S:real^2->bool` THEN STRIP_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:real^2` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `x2:real^2` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `moi_s4u_cyl d x1 IN outside(path_image (p:real^1->complex)) /\
                moi_s4u_cyl d x2 IN inside(path_image (p:real^1->complex))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `R:real`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "outside")) (concl th))) THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV; IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG;
                  REAL_NOT_LE; MOI_S4U_CYL_NORM] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `exp(abs(log R) + abs(log r))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log R)` THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[EXP_LOG; REAL_LE_REFL];
          REWRITE_TAC[REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC];
        REWRITE_TAC[REAL_EXP_MONO_LT] THEN FIRST_ASSUM ACCEPT_TAC];
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `r:real`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "inside")) (concl th))) THEN
      REWRITE_TAC[IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG; MOI_S4U_CYL_NORM] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(log r)` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_EXP_MONO_LT] THEN
        UNDISCH_TAC `moi_s4u_nu d x2 < --(abs(log R) + abs(log r))` THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[EXP_LOG; REAL_LE_REFL]]];
    ALL_TAC] THEN
  (* the image of S is connected and misses the Jordan curve *)
  SUBGOAL_THEN `connected (IMAGE (moi_s4u_cyl d) (S:real^2->bool)) /\
                IMAGE (moi_s4u_cyl d) S INTER path_image (p:real^1->complex) = {}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[MOI_S4U_CYL_CONTINUOUS];
      EXPAND_TAC "p" THEN
      REWRITE_TAC[PATH_IMAGE_COMPOSE; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY;
                  path_image] THEN
      X_GEN_TAC `z:complex` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `y:real^2` (CONJUNCTS_THEN2 MP_TAC
          (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC)))) THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_S4U_CYL_EQ] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `t:real^1`; `n:real`] o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `S:real^2->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `connected (IMAGE (moi_s4u_cyl d) (S:real^2->bool))` THEN
  REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`inside(path_image (p:real^1->complex))`;
                             `outside(path_image (p:real^1->complex))`]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`IMAGE (moi_s4u_cyl d) S INTER path_image (p:real^1->complex) = {}`;
    `inside(path_image (p:real^1->complex)) UNION outside(path_image p) =
     (:complex) DIFF path_image p`;
    `inside(path_image (p:real^1->complex)) INTER outside(path_image p) = {}`;
    `moi_s4u_cyl d x1 IN outside(path_image (p:real^1->complex))`;
    `moi_s4u_cyl d x2 IN inside(path_image (p:real^1->complex))`;
    `(x1:real^2) IN S`; `(x2:real^2) IN S`] THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A Jordan curve around 0 meets each of its rotations (the maximum of      *)
(* the norm is attained on both), hence a translate of a d-periodic simple *)
(* curve by a vector parallel to d meets the curve (MOI_S4U_PARALLEL_MEETS).*)
(* ------------------------------------------------------------------------- *)

let MOI_S4U_CYL_SHIFT = prove
 (`!d x u:real^2.
     moi_s4u_cyl d (x + u) =
     cexp(Cx(moi_s4u_nu d u) + ii * Cx(&2 * pi * (d dot u) / (d dot d))) *
     moi_s4u_cyl d x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4u_cyl; GSYM CEXP_ADD; MOI_S4U_NU_LINEAR] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[DOT_RADD; real_div; REAL_ADD_RDISTRIB; REAL_ADD_LDISTRIB; CX_ADD; CX_MUL] THEN
  CONV_TAC COMPLEX_RING);;

let MOI_S4U_INSIDE_BALL = prove
 (`!s:real^N->bool r. closed s /\ s SUBSET cball(vec 0,r) ==> inside s SUBSET ball(vec 0,r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERIOR_CBALL] THEN
  MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_SIMP_TAC[OPEN_INSIDE] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `cball(vec 0:real^N,r)`] OUTSIDE_SUBSET_CONVEX) THEN
  ASM_REWRITE_TAC[CONVEX_CBALL] THEN
  MP_TAC(ISPEC `s:real^N->bool` INSIDE_INTER_OUTSIDE) THEN SET_TAC[]);;

let MOI_S4U_CONNECTED_SIDE = prove
 (`!s a b:real^N->bool.
     connected s /\ open a /\ open b /\ a INTER b = {} /\ s SUBSET a UNION b /\
     ~(s INTER b = {})
     ==> s SUBSET b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N->bool`; `b:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`a INTER b:real^N->bool = {}`; `s SUBSET a UNION b:real^N->bool`;
                         `~(s INTER b:real^N->bool = {})`] THEN
  SET_TAC[]);;

let MOI_S4U_ROT_JORDAN = prove
 (`!(p:real^1->complex) rho.
     simple_path p /\ pathfinish p = pathstart p /\
     Cx(&0) IN inside(path_image p) /\ norm rho = &1
     ==> ~(DISJOINT (path_image p) (IMAGE (\z. rho * z) (path_image p)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(rho = Cx(&0))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `norm(rho:complex) = &1` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `simple_path ((\z. rho * z) o (p:real^1->complex)) /\
                pathfinish ((\z. rho * z) o p) = pathstart ((\z. rho * z) o p) /\
                path_image ((\z. rho * z) o p) = IMAGE (\z. rho * z) (path_image p)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `simple_path ((\z. rho * z) o (p:real^1->complex)) <=> simple_path p`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SIMPLE_PATH_LINEAR_IMAGE_EQ THEN REWRITE_TAC[LINEAR_COMPLEX_MUL] THEN
      ASM_SIMP_TAC[COMPLEX_EQ_MUL_LCANCEL];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside(IMAGE (\z. rho * z) (path_image (p:real^1->complex))) =
                IMAGE (\z. rho * z) (inside(path_image p))` ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_LINEAR_IMAGE THEN REWRITE_TAC[LINEAR_COMPLEX_MUL] THEN
    ASM_SIMP_TAC[COMPLEX_EQ_MUL_LCANCEL] THEN X_GEN_TAC `y:complex` THEN
    EXISTS_TAC `inv rho * y:complex` THEN
    UNDISCH_TAC `~(rho = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `J = path_image (p:real^1->complex)` THEN
  ABBREV_TAC `J1 = IMAGE (\z. rho * z) (J:complex->bool)` THEN
  MP_TAC(ISPEC `p:real^1->complex` JORDAN_INSIDE_OUTSIDE) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `path_image (p:real^1->complex) = J`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(\z. rho * z) o (p:real^1->complex)` JORDAN_INSIDE_OUTSIDE) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `path_image ((\z. rho * z) o (p:real^1->complex)) = J1`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `compact (J:complex->bool) /\ ~(J = {})` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `path_image (p:real^1->complex) = J`); PATH_IMAGE_NONEMPTY] THEN
    MATCH_MP_TAC COMPACT_PATH_IMAGE THEN MATCH_MP_TAC SIMPLE_PATH_IMP_PATH THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?z0:complex. z0 IN J /\ !z. z IN J ==> norm z <= norm z0`
  (X_CHOOSE_THEN `z0:complex` STRIP_ASSUME_TAC) THENL
   [MP_TAC(ISPECL [`J:complex->bool`; `vec 0:complex`] DISTANCE_ATTAINS_SUP) THEN
    ASM_REWRITE_TAC[DIST_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN J1 ==> norm(z:complex) <= norm(z0:complex)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `IMAGE (\z. rho * z) (J:complex->bool) = J1`)] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_MUL; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (J1:complex->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `IMAGE (\z. rho * z) (J:complex->bool) = J1`)] THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    REWRITE_TAC[LINEAR_COMPLEX_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (J:complex->bool) /\ connected (J1:complex->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `path_image (p:real^1->complex) = J`);
                GSYM(ASSUME `path_image ((\z. rho * z) o (p:real^1->complex)) = J1`)] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONNECTED_PATH_IMAGE THEN
    MATCH_MP_TAC SIMPLE_PATH_IMP_PATH THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inside J SUBSET ball(vec 0:complex,norm(z0:complex)) /\
                inside J1 SUBSET ball(vec 0:complex,norm(z0:complex))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S4U_INSIDE_BALL THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; SUBSET; IN_CBALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(rho * z0:complex) IN J1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `IMAGE (\z. rho * z) (J:complex->bool) = J1`)] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z0:complex` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Cx(&0) IN inside J1` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `inside J1 = IMAGE (\z. rho * z) (inside J)`; IN_IMAGE] THEN
    EXISTS_TAC `Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_MUL_RZERO];
    ALL_TAC] THEN
  (* J1 lies outside J and J lies outside J1 *)
  SUBGOAL_THEN `J1 SUBSET outside(J:complex->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4U_CONNECTED_SIDE THEN EXISTS_TAC `inside(J:complex->bool)` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[ASSUME `inside J UNION outside J = (:complex) DIFF J`] THEN
      UNDISCH_TAC `DISJOINT (J:complex->bool) J1` THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `rho * z0:complex` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((rho * z0:complex) IN J) /\ ~((rho * z0:complex) IN inside J)`
      MP_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `DISJOINT (J:complex->bool) J1` THEN
          UNDISCH_TAC `(rho * z0:complex) IN J1` THEN SET_TAC[];
          DISCH_TAC THEN
          SUBGOAL_THEN `(rho * z0:complex) IN ball(vec 0,norm(z0:complex))` MP_TAC THENL
           [UNDISCH_TAC `inside J SUBSET ball(vec 0:complex,norm(z0:complex))` THEN
            UNDISCH_TAC `(rho * z0:complex) IN inside J` THEN SET_TAC[];
            ASM_REWRITE_TAC[IN_BALL_0; COMPLEX_NORM_MUL; REAL_MUL_LID; REAL_LT_REFL]]];
        MP_TAC(ISPEC `J:complex->bool` INSIDE_NO_OVERLAP) THEN
        MP_TAC(ISPEC `J:complex->bool` OUTSIDE_NO_OVERLAP) THEN
        UNDISCH_TAC `inside J UNION outside J = (:complex) DIFF J` THEN SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `J SUBSET outside(J1:complex->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4U_CONNECTED_SIDE THEN EXISTS_TAC `inside(J1:complex->bool)` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[ASSUME `inside J1 UNION outside J1 = (:complex) DIFF J1`] THEN
      UNDISCH_TAC `DISJOINT (J:complex->bool) J1` THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `z0:complex` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((z0:complex) IN J1) /\ ~((z0:complex) IN inside J1)` MP_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `DISJOINT (J:complex->bool) J1` THEN
          UNDISCH_TAC `(z0:complex) IN J` THEN SET_TAC[];
          DISCH_TAC THEN
          SUBGOAL_THEN `(z0:complex) IN ball(vec 0,norm(z0:complex))` MP_TAC THENL
           [UNDISCH_TAC `inside J1 SUBSET ball(vec 0:complex,norm(z0:complex))` THEN
            UNDISCH_TAC `(z0:complex) IN inside J1` THEN SET_TAC[];
            REWRITE_TAC[IN_BALL_0; REAL_LT_REFL]]];
        MP_TAC(ISPEC `J1:complex->bool` INSIDE_NO_OVERLAP) THEN
        MP_TAC(ISPEC `J1:complex->bool` OUTSIDE_NO_OVERLAP) THEN
        UNDISCH_TAC `inside J1 UNION outside J1 = (:complex) DIFF J1` THEN SET_TAC[]]];
    ALL_TAC] THEN
  (* inside J1 lies inside J, so J1 does too *)
  SUBGOAL_THEN `inside J1 SUBSET inside(J:complex->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4U_CONNECTED_SIDE THEN EXISTS_TAC `outside(J:complex->bool)` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ONCE_REWRITE_TAC[INTER_COMM] THEN FIRST_ASSUM ACCEPT_TAC;
      ONCE_REWRITE_TAC[UNION_COMM] THEN
      REWRITE_TAC[ASSUME `inside J UNION outside J = (:complex) DIFF J`] THEN
      MP_TAC(ISPEC `J1:complex->bool` INSIDE_INTER_OUTSIDE) THEN
      UNDISCH_TAC `J SUBSET outside(J1:complex->bool)` THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `Cx(&0)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `J1 SUBSET inside(J:complex->bool) UNION J` ASSUME_TAC THENL
   [SUBGOAL_THEN `closure(inside J1) SUBSET closure(inside(J:complex->bool))` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_CLOSURE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(J1:complex->bool = {})` MP_TAC THENL
   [UNDISCH_TAC `(rho * z0:complex) IN J1` THEN SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`J1 SUBSET inside(J:complex->bool) UNION J`; `DISJOINT (J:complex->bool) J1`;
    `J1 SUBSET outside(J:complex->bool)`;
    `inside J INTER outside J:complex->bool = {}`] THEN
  SET_TAC[]);;

(* A translate of a d-periodic simple curve by a vector parallel to d     *)
(* meets the curve.                                                       *)

let MOI_S4U_PARALLEL_MEETS = prove
 (`!(g:real^1->real^2) d u.
     path g /\ ~(d = vec 0) /\ pathfinish g = pathstart g + d /\
     (!s t n. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
              integer n /\ g s = g t + n % d
              ==> s = t \/ (s = vec 0 /\ t = vec 1) \/ (s = vec 1 /\ t = vec 0)) /\
     moi_s4u_nu d u = &0
     ==> ?s t n. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
                 integer n /\ g s = g t + u + n % d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g:real^1->real^2`; `d:real^2`] MOI_S4U_CYL_JORDAN) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`moi_s4u_cyl d o (g:real^1->real^2)`;
                 `cexp(ii * Cx(&2 * pi * ((d:real^2) dot (u:real^2)) / (d dot d)))`]
    MOI_S4U_ROT_JORDAN) THEN
  ASM_REWRITE_TAC[NORM_CEXP_II] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
  REWRITE_TAC[PATH_IMAGE_COMPOSE; IN_IMAGE; path_image; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:complex` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `y1:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC)))
    (X_CHOOSE_THEN `z1:complex` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `y2:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `moi_s4u_cyl d ((g:real^1->real^2) s) = moi_s4u_cyl d (g t + u)`
  MP_TAC THENL
   [REWRITE_TAC[MOI_S4U_CYL_SHIFT; ASSUME `moi_s4u_nu d u = &0`; COMPLEX_ADD_LID] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S4U_CYL_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`s:real^1`; `t:real^1`; `n:real`] THEN
  ASM_REWRITE_TAC[VECTOR_ADD_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The universal cover of the round torus S1 x S1 (moi_s4u_tor), the        *)
(* displacement of a loop (the winding numbers of its two coordinates),    *)
(* lifts of loops, loops in the torus are homotopic iff their displacements *)
(* agree, and powers of a loop (moi_s4u_ppow).                               *)
(* ------------------------------------------------------------------------- *)

let moi_s4u_ex = new_definition
 `moi_s4u_ex (a:real) = cexp(ii * Cx(&2 * pi * a))`;;

let moi_s4u_tor = new_definition
 `moi_s4u_tor (x:real^2) =
    pastecart (moi_s4u_ex (x$1)) (moi_s4u_ex (x$2)):real^(2,2)finite_sum`;;

let moi_s4u_disp = new_definition
 `moi_s4u_disp (g:real^1->real^(2,2)finite_sum) =
    vector[Re(winding_number(fstcart o g,vec 0));
           Re(winding_number(sndcart o g,vec 0))]:real^2`;;

let MOI_S4U_EX_EQ = prove
 (`!a b. moi_s4u_ex a = moi_s4u_ex b <=> integer(a - b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4u_ex; CEXP_EQ] THEN
  SUBGOAL_THEN `!n. ii * Cx(&2 * pi * a) = ii * Cx(&2 * pi * b) + Cx(&2 * n * pi) * ii <=>
                    a - b = n` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `Cx(&2 * pi * a) = Cx(&2 * pi * b + &2 * n * pi)` THEN CONJ_TAC THENL
     [REWRITE_TAC[CX_ADD] THEN MP_TAC II_NZ THEN CONV_TAC COMPLEX_FIELD;
      REWRITE_TAC[CX_INJ] THEN MP_TAC PI_POS THEN CONV_TAC REAL_FIELD];
    MESON_TAC[]]);;

let MOI_S4U_TOR_EQ = prove
 (`!x y:real^2.
     moi_s4u_tor x = moi_s4u_tor y <=> integer(x$1 - y$1) /\ integer(x$2 - y$2)`,
  REWRITE_TAC[moi_s4u_tor; PASTECART_INJ; MOI_S4U_EX_EQ]);;

let MOI_S4U_EX_SPHERE = prove
 (`!a. moi_s4u_ex a IN sphere(vec 0:real^2,&1)`,
  REWRITE_TAC[moi_s4u_ex; IN_SPHERE_0; NORM_CEXP_II]);;

let MOI_S4U_TOR_IN = prove
 (`!x. moi_s4u_tor x IN sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`,
  REWRITE_TAC[moi_s4u_tor; PASTECART_IN_PCROSS; MOI_S4U_EX_SPHERE]);;

let MOI_S4U_TOR_CONTINUOUS = prove
 (`!s. moi_s4u_tor continuous_on s`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `moi_s4u_tor =
    (\x. pastecart ((cexp o (\x:real^2. ii * Cx(((&2 * pi) % basis 1) dot x))) x)
                   ((cexp o (\x:real^2. ii * Cx(((&2 * pi) % basis 2) dot x))) x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_s4u_tor; moi_s4u_ex; o_THM; DOT_LMUL] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_2; ARITH; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN REWRITE_TAC[CONTINUOUS_ON_CX_DOT]);;

let MOI_S4U_TOR_INTEGER_SHIFT = prove
 (`!x u:real^2. integer(u$1) /\ integer(u$2) ==> moi_s4u_tor (x + u) = moi_s4u_tor x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_S4U_TOR_EQ; VECTOR_ADD_COMPONENT] THEN
  ASM_REWRITE_TAC[REAL_ARITH `(a + b) - a = b:real`]);;

(* Lifts of loops in the torus; the displacement has integer coordinates.  *)

let MOI_S4U_RE_ZERO = prove
 (`!z. Re z = &0 ==> z = ii * Cx(Im z)`,
  GEN_TAC THEN DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [COMPLEX_EXPAND] THEN
  ASM_REWRITE_TAC[COMPLEX_ADD_LID]);;

let MOI_S4U_LOOP_LIFT = prove
 (`!g:real^1->real^(2,2)finite_sum.
     path g /\ pathfinish g = pathstart g /\
     path_image g SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
     ==> integer((moi_s4u_disp g)$1) /\ integer((moi_s4u_disp g)$2) /\
         ?h. path h /\ pathfinish h = pathstart h + moi_s4u_disp g /\
             !t. t IN interval[vec 0,vec 1] ==> moi_s4u_tor (h t) = g t`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FH1_LOOP_COMPONENTS) THEN
  SUBGOAL_THEN `~(vec 0 IN path_image (fstcart o (g:real^1->real^(2,2)finite_sum))) /\
                ~(vec 0 IN path_image (sndcart o g))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `path_image (fstcart o (g:real^1->real^(2,2)finite_sum)) SUBSET
                   sphere(vec 0,&1)`;
      UNDISCH_TAC `path_image (sndcart o (g:real^1->real^(2,2)finite_sum)) SUBSET
                   sphere(vec 0,&1)`] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN
    ASM_REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `complex_integer(winding_number(fstcart o (g:real^1->real^(2,2)finite_sum),vec 0)) /\
    complex_integer(winding_number(sndcart o g,vec 0))` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGER_WINDING_NUMBER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[complex_integer] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s4u_disp; VECTOR_2] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`fstcart o (g:real^1->real^(2,2)finite_sum)`; `vec 0:complex`]
    WINDING_NUMBER_AS_CONTINUOUS_LOGARITHM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:real^1->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`sndcart o (g:real^1->real^(2,2)finite_sum)`; `vec 0:complex`]
    WINDING_NUMBER_AS_CONTINUOUS_LOGARITHM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^1->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t:real^1. t IN interval[vec 0,vec 1]
                    ==> (q1:real^1->complex) t = ii * Cx(Im(q1 t)) /\
                        (q2:real^1->complex) t = ii * Cx(Im(q2 t))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `fstcart((g:real^1->real^(2,2)finite_sum) t) IN sphere(vec 0,&1) /\
                  sndcart(g t) IN sphere(vec 0,&1)` MP_TAC THENL
     [REWRITE_TAC[GSYM MOI_FH1_IN_PCROSS] THEN
      UNDISCH_TAC `path g /\ pathfinish g = pathstart g /\
                   path_image g SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
      REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `fstcart((g:real^1->real^(2,2)finite_sum) t) = cexp(q1(t:real^1)) /\
                  sndcart(g t) = cexp(q2 t)` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th ->
          can (find_term ((=) `q1:real^1->complex`)) (concl th) && is_forall (concl th)));
        FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th ->
          can (find_term ((=) `q2:real^1->complex`)) (concl th) && is_forall (concl th)))] THEN
      ASM_REWRITE_TAC[o_THM; VECTOR_ADD_LID];
      ALL_TAC] THEN
    REWRITE_TAC[IN_SPHERE_0] THEN
    DISCH_THEN(CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP NORM_CEXP_IMAGINARY)) THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_S4U_RE_ZERO THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\t:real^1. inv(&2 * pi) % vector[Im(q1 t); Im(q2 t)]:real^2` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
    REWRITE_TAC[DIMINDEX_2; ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`] THEN
    GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[VECTOR_2; IM_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    UNDISCH_TAC `path (q1:real^1->complex)` THEN UNDISCH_TAC `path (q2:real^1->complex)` THEN
    REWRITE_TAC[path] THEN SIMP_TAC[];
    REWRITE_TAC[pathstart; pathfinish] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    MP_TAC(AP_TERM `Im` (ASSUME `pathfinish q1 - pathstart q1 =
                 Cx(&2) * Cx pi * ii *
                 winding_number(fstcart o (g:real^1->real^(2,2)finite_sum),vec 0)`)) THEN
    MP_TAC(AP_TERM `Im` (ASSUME `pathfinish q2 - pathstart q2 =
                 Cx(&2) * Cx pi * ii *
                 winding_number(sndcart o (g:real^1->real^(2,2)finite_sum),vec 0)`)) THEN
    REWRITE_TAC[pathstart; pathfinish; IM_SUB; IM_MUL_CX; IM_MUL_II] THEN
    MP_TAC PI_POS THEN
    CONV_TAC REAL_FIELD;
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th ->
      can (find_term ((=) `ii * Cx(Im((q1:real^1->complex) t))`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[moi_s4u_tor; moi_s4u_ex; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    SUBGOAL_THEN `!y. &2 * pi * inv(&2 * pi) * y = y` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[GSYM(ASSUME `q1(t:real^1) = ii * Cx(Im(q1 t))`);
                GSYM(ASSUME `q2(t:real^1) = ii * Cx(Im(q2 t))`)] THEN
    SUBGOAL_THEN `cexp(q1(t:real^1)) = fstcart((g:real^1->real^(2,2)finite_sum) t) /\
                  cexp(q2 t) = sndcart(g t)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th ->
          can (find_term ((=) `q1:real^1->complex`)) (concl th) && is_forall (concl th) &&
          can (find_term ((=) `fstcart:real^(2,2)finite_sum->real^2`)) (concl th)));
        FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th ->
          can (find_term ((=) `q2:real^1->complex`)) (concl th) && is_forall (concl th) &&
          can (find_term ((=) `sndcart:real^(2,2)finite_sum->real^2`)) (concl th)))] THEN
      ASM_REWRITE_TAC[o_THM; VECTOR_ADD_LID] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND]]);;
(* Loops in the round torus are homotopic iff their displacements agree.   *)

let MOI_S4U_DISP_HOMOTOPIC = prove
 (`!g h:real^1->real^(2,2)finite_sum.
     path g /\ pathfinish g = pathstart g /\
     path_image g SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
     path h /\ pathfinish h = pathstart h /\
     path_image h SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
     ==> (homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) g h <=>
          moi_s4u_disp g = moi_s4u_disp h)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FH1_LOOP_COMPONENTS th)) MP_TAC o
    REWRITE_RULE[TAUT `a /\ b /\ c /\ d /\ e /\ f <=> (a /\ b /\ c) /\ (d /\ e /\ f)`]) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FH1_LOOP_COMPONENTS th)) THEN
  SUBGOAL_THEN
   `(winding_number(fstcart o (g:real^1->real^(2,2)finite_sum),vec 0) =
     winding_number(fstcart o (h:real^1->real^(2,2)finite_sum),vec 0) <=>
     homotopic_loops (sphere(vec 0,&1)) (fstcart o g) (fstcart o h)) /\
    (winding_number(sndcart o g,vec 0) = winding_number(sndcart o h,vec 0) <=>
     homotopic_loops (sphere(vec 0,&1)) (sndcart o g) (sndcart o h))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FH1_CIRCLE_HOMOTOPIC_LOOPS_EQ THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k:real^1->real^(2,2)finite_sum.
      path k /\ pathfinish k = pathstart k /\
      path_image k SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
      ==> complex_integer(winding_number(fstcart o k,vec 0)) /\
          complex_integer(winding_number(sndcart o k,vec 0))`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_FH1_LOOP_COMPONENTS) THEN
    CONJ_TAC THEN MATCH_MP_TAC INTEGER_WINDING_NUMBER THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THENL
     [UNDISCH_TAC `path_image (fstcart o (k:real^1->real^(2,2)finite_sum)) SUBSET
                   sphere(vec 0,&1)`;
      UNDISCH_TAC `path_image (sndcart o (k:real^1->real^(2,2)finite_sum)) SUBSET
                   sphere(vec 0,&1)`] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN
    ASM_REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `g:real^1->real^(2,2)finite_sum`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real^1->real^(2,2)finite_sum`) THEN
  ASM_REWRITE_TAC[complex_integer] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_s4u_disp; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP MOI_FH1_HOMOTOPIC_LOOPS_PROJ) THEN
    REWRITE_TAC[GSYM(ASSUME
     `winding_number(fstcart o (g:real^1->real^(2,2)finite_sum),vec 0) =
      winding_number(fstcart o (h:real^1->real^(2,2)finite_sum),vec 0) <=>
      homotopic_loops (sphere(vec 0,&1)) (fstcart o g) (fstcart o h)`);
                GSYM(ASSUME
     `winding_number(sndcart o (g:real^1->real^(2,2)finite_sum),vec 0) =
      winding_number(sndcart o (h:real^1->real^(2,2)finite_sum),vec 0) <=>
      homotopic_loops (sphere(vec 0,&1)) (sndcart o g) (sndcart o h)`)] THEN
    SIMP_TAC[];
    STRIP_TAC THEN
    SUBGOAL_THEN
     `winding_number(fstcart o (g:real^1->real^(2,2)finite_sum),vec 0) =
      winding_number(fstcart o (h:real^1->real^(2,2)finite_sum),vec 0) /\
      winding_number(sndcart o g,vec 0) = winding_number(sndcart o h,vec 0)`
    MP_TAC THENL [REWRITE_TAC[COMPLEX_EQ] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_FH1_HOMOTOPIC_LOOPS_PASTECART) THEN
    REWRITE_TAC[o_THM; PASTECART_FST_SND; ETA_AX]]);;

(* Powers of a loop. *)

let moi_s4u_ppow = define
 `moi_s4u_ppow (g:real^1->real^N) 0 = linepath(pathstart g,pathstart g) /\
  moi_s4u_ppow g (SUC n) = g ++ moi_s4u_ppow g n`;;

let MOI_S4U_PPOW_LOOP = prove
 (`!(g:real^1->real^N) n.
     path g /\ pathfinish g = pathstart g
     ==> path (moi_s4u_ppow g n) /\ pathstart (moi_s4u_ppow g n) = pathstart g /\
         pathfinish (moi_s4u_ppow g n) = pathstart g /\
         path_image (moi_s4u_ppow g n) SUBSET path_image g`,
  GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_s4u_ppow] THENL
   [REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET; PATHSTART_IN_PATH_IMAGE];
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `pathfinish (g:real^1->real^N) = pathstart (moi_s4u_ppow g n)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[PATH_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN] THEN
    ASM_REWRITE_TAC[UNION_SUBSET; SUBSET_REFL]]);;

let MOI_S4U_PPOW_COMPOSE = prove
 (`!(f:real^M->real^N) (g:real^1->real^M) n.
     f o moi_s4u_ppow g n = moi_s4u_ppow (f o g) n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[moi_s4u_ppow] THENL
   [REWRITE_TAC[LINEPATH_REFL; PATHSTART_COMPOSE; FUN_EQ_THM; o_THM];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; joinpaths] THEN GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[o_THM]]);;

let MOI_S4U_PPOW_WINDING = prove
 (`!(g:real^1->complex) z n.
     path g /\ pathfinish g = pathstart g /\ ~(z IN path_image g)
     ==> winding_number(moi_s4u_ppow g n,z) = Cx(&n) * winding_number(g,z)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s4u_ppow] THENL
   [REWRITE_TAC[COMPLEX_MUL_LZERO] THEN MATCH_MP_TAC WINDING_NUMBER_TRIVIAL THEN
    DISCH_TAC THEN UNDISCH_TAC `~((z:complex) IN path_image g)` THEN
    ASM_REWRITE_TAC[PATHSTART_IN_PATH_IMAGE];
    MP_TAC(ISPECL [`g:real^1->complex`; `n:num`] MOI_S4U_PPOW_LOOP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) WINDING_NUMBER_JOIN o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `path_image (moi_s4u_ppow (g:real^1->complex) n) SUBSET path_image g` THEN
      UNDISCH_TAC `~((z:complex) IN path_image g)` THEN SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; CX_ADD] THEN CONV_TAC COMPLEX_RING]);;

let MOI_S4U_TT_LOOP_COMPOSE = prove
 (`!(f:real^(2,2)finite_sum->real^2) (g:real^1->real^(2,2)finite_sum).
     path g /\ pathfinish g = pathstart g /\
     path_image g SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
     (f = fstcart \/ f = sndcart)
     ==> path (f o g) /\ pathfinish (f o g) = pathstart (f o g) /\
         ~(vec 0 IN path_image (f o g))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o
    REWRITE_RULE[TAUT `a /\ b /\ c /\ d <=> (a /\ b /\ c) /\ d`]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FH1_LOOP_COMPONENTS) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [UNDISCH_TAC `path_image (fstcart o (g:real^1->real^(2,2)finite_sum)) SUBSET
                 sphere(vec 0,&1)`;
    UNDISCH_TAC `path_image (sndcart o (g:real^1->real^(2,2)finite_sum)) SUBSET
                 sphere(vec 0,&1)`] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN
  ASM_REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC);;

let MOI_S4U_DISP_PPOW = prove
 (`!(g:real^1->real^(2,2)finite_sum) n.
     path g /\ pathfinish g = pathstart g /\
     path_image g SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
     ==> moi_s4u_disp (moi_s4u_ppow g n) = &n % moi_s4u_disp g`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_s4u_disp; MOI_S4U_PPOW_COMPOSE] THEN
  MP_TAC(ISPECL [`fstcart:real^(2,2)finite_sum->real^2`; `g:real^1->real^(2,2)finite_sum`]
    MOI_S4U_TT_LOOP_COMPOSE) THEN
  MP_TAC(ISPECL [`sndcart:real^(2,2)finite_sum->real^2`; `g:real^1->real^(2,2)finite_sum`]
    MOI_S4U_TT_LOOP_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_S4U_PPOW_WINDING; GSYM COMPLEX_VEC_0] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_MUL_COMPONENT; RE_MUL_CX]);;

let MOI_S4U_DISP_REVERSEPATH = prove
 (`!g:real^1->real^(2,2)finite_sum.
     path g /\ pathfinish g = pathstart g /\
     path_image g SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
     ==> moi_s4u_disp (reversepath g) = --(moi_s4u_disp g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!f:real^(2,2)finite_sum->real^2.
                  f o reversepath (g:real^1->real^(2,2)finite_sum) = reversepath (f o g)`
  (fun th -> REWRITE_TAC[moi_s4u_disp; th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; reversepath]; ALL_TAC] THEN
  MP_TAC(ISPECL [`fstcart:real^(2,2)finite_sum->real^2`; `g:real^1->real^(2,2)finite_sum`]
    MOI_S4U_TT_LOOP_COMPOSE) THEN
  MP_TAC(ISPECL [`sndcart:real^(2,2)finite_sum->real^2`; `g:real^1->real^(2,2)finite_sum`]
    MOI_S4U_TT_LOOP_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WINDING_NUMBER_REVERSEPATH] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT; RE_NEG]);;

(* For an integer m there is a loop in the image of g with displacement   *)
(* m times that of g.                                                      *)

let MOI_S4U_DISP_MULTIPLE = prove
 (`!(g:real^1->real^(2,2)finite_sum) m.
     path g /\ pathfinish g = pathstart g /\
     path_image g SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
     integer m
     ==> ?h. path h /\ pathfinish h = pathstart h /\ path_image h SUBSET path_image g /\
             moi_s4u_disp h = m % moi_s4u_disp g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n. path (moi_s4u_ppow (g:real^1->real^(2,2)finite_sum) n) /\
                    pathfinish (moi_s4u_ppow g n) = pathstart (moi_s4u_ppow g n) /\
                    path_image (moi_s4u_ppow g n) SUBSET path_image g /\
                    path_image (moi_s4u_ppow g n) SUBSET
                    sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
                    moi_s4u_disp (moi_s4u_ppow g n) = &n % moi_s4u_disp g`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`g:real^1->real^(2,2)finite_sum`; `n:num`] MOI_S4U_PPOW_LOOP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[MOI_S4U_DISP_PPOW] THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `&0 <= m \/ &0 <= --m`) THENL
   [MP_TAC(SPEC `m:real` INTEGER_POS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    EXISTS_TAC `moi_s4u_ppow (g:real^1->real^(2,2)finite_sum) n` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPEC `--m:real` INTEGER_POS) THEN ASM_REWRITE_TAC[INTEGER_NEG] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    EXISTS_TAC `reversepath(moi_s4u_ppow (g:real^1->real^(2,2)finite_sum) n)` THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                    PATH_IMAGE_REVERSEPATH] THEN
    ASM_SIMP_TAC[MOI_S4U_DISP_REVERSEPATH] THEN
    UNDISCH_TAC `--m = &n` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_NEG_NEG]]);;

(* ------------------------------------------------------------------------- *)
(* Simple closed curves in the round torus.  A circle C has a simple        *)
(* closed parametrisation g whose displacement generates the displacements *)
(* of all loops in C (MOI_S4U_TT_CURVE_PARAM); if C is essential, loops     *)
(* missing C have displacements parallel to that of g (separation by the   *)
(* periodic lift), hence integer multiples of it (primitivity), hence they *)
(* are homotopic to loops in C (MOI_S4U_TT_CURVE_LOOPS).                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S4U_DISP_CONST = prove
 (`!a:real^(2,2)finite_sum.
     a IN sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
     ==> moi_s4u_disp (linepath(a,a)) = vec 0`,
  GEN_TAC THEN REWRITE_TAC[MOI_FH1_IN_PCROSS; IN_SPHERE_0] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s4u_disp] THEN
  SUBGOAL_THEN `!f:real^(2,2)finite_sum->real^2.
                  f o linepath(a,a) = linepath(f a,f a)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[LINEPATH_REFL; FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `winding_number(linepath(fstcart(a:real^(2,2)finite_sum),fstcart a),vec 0) = Cx(&0) /\
    winding_number(linepath(sndcart a,sndcart a),vec 0) = Cx(&0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC WINDING_NUMBER_TRIVIAL THEN DISCH_TAC THENL
     [UNDISCH_TAC `norm(fstcart(a:real^(2,2)finite_sum)) = &1`;
      UNDISCH_TAC `norm(sndcart(a:real^(2,2)finite_sum)) = &1`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    REWRITE_TAC[RE_CX; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT]]);;

(* Loops on the unit circle are homotopic to powers of the circle path or  *)
(* their reverses.                                                         *)

let MOI_S4U_S1_LOOP_POWER = prove
 (`!p:real^1->real^2.
     path p /\ pathfinish p = pathstart p /\ path_image p SUBSET sphere(vec 0,&1)
     ==> ?n. homotopic_loops (sphere(vec 0,&1)) p
               (moi_s4u_ppow (circlepath(vec 0,&1)) n) \/
             homotopic_loops (sphere(vec 0,&1)) p
               (reversepath(moi_s4u_ppow (circlepath(vec 0,&1)) n))`,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN
  SUBGOAL_THEN `~(vec 0 IN path_image (p:real^1->real^2)) /\
                ~(vec 0 IN path_image (circlepath(vec 0:real^2,&1)))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `path_image (p:real^1->real^2) SUBSET sphere(vec 0,&1)` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN
      ASM_REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:real^1->real^2`; `vec 0:real^2`] INTEGER_WINDING_NUMBER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_FH1_COMPLEX_INTEGER_CASES) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`circlepath(vec 0:real^2,&1)`; `n:num`] MOI_S4U_PPOW_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`circlepath(vec 0:real^2,&1)`; `vec 0:real^2`; `n:num`]
    MOI_S4U_PPOW_WINDING) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(vec 0 IN path_image (moi_s4u_ppow (circlepath(vec 0:real^2,&1)) n))`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `path_image (moi_s4u_ppow (circlepath(vec 0:real^2,&1)) n) SUBSET
                 sphere(vec 0,&1)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN
    ASM_REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOI_FH1_CIRCLE_HOMOTOPIC_LOOPS_EQ o snd) THEN
  ASM_REWRITE_TAC[PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                  PATH_IMAGE_REVERSEPATH] THEN
  ASM_SIMP_TAC[WINDING_NUMBER_REVERSEPATH]);;

let MOI_S4U_TT_CURVE_PARAM = prove
 (`!c:real^(2,2)finite_sum->bool.
     c SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
     c homeomorphic sphere(vec 0:real^2,&1)
     ==> ?g. simple_path g /\ pathfinish g = pathstart g /\ path_image g = c /\
             !h. path h /\ pathfinish h = pathstart h /\ path_image h SUBSET c
                 ==> ?m. integer m /\ moi_s4u_disp h = m % moi_s4u_disp g`,
  GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(c:real^(2,2)finite_sum->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `h0:real^2->real^(2,2)finite_sum`
    (X_CHOOSE_THEN `k0:real^(2,2)finite_sum->real^2` ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism]) THEN
  STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN
  ABBREV_TAC `cp = circlepath(vec 0:real^2,&1)` THEN
  SUBGOAL_THEN `simple_path (cp:real^1->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "cp" THEN REWRITE_TAC[SIMPLE_PATH_CIRCLEPATH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(h0:real^2->real^(2,2)finite_sum) o (cp:real^1->real^2)` THEN
  REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `h:real^1->real^(2,2)finite_sum` THEN STRIP_TAC THEN
  SUBGOAL_THEN `path ((k0:real^(2,2)finite_sum->real^2) o (h:real^1->real^(2,2)finite_sum)) /\
                pathfinish (k0 o h) = pathstart (k0 o h) /\
                path_image (k0 o h) SUBSET sphere(vec 0,&1)` MP_TAC THENL
   [REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `c:real^(2,2)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `path_image (h:real^1->real^(2,2)finite_sum) SUBSET c` THEN
      UNDISCH_TAC `IMAGE (k0:real^(2,2)finite_sum->real^2) c = sphere(vec 0,&1)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S4U_S1_LOOP_POWER) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
  (* push the homotopy forward by h0 *)
  SUBGOAL_THEN
   `!q. homotopic_loops (sphere(vec 0,&1)) ((k0:real^(2,2)finite_sum->real^2) o h) q
        ==> homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
              h ((h0:real^2->real^(2,2)finite_sum) o q)`
  (LABEL_TAC "hpush") THENL
   [X_GEN_TAC `q:real^1->real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN EXISTS_TAC `c:real^(2,2)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(h0:real^2->real^(2,2)finite_sum) o (k0:real^(2,2)finite_sum->real^2) o (h:real^1->real^(2,2)finite_sum)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[o_THM] THEN
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `path_image (h:real^1->real^(2,2)finite_sum) SUBSET c` THEN
      REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
      EXISTS_TAC `sphere(vec 0:real^2,&1)` THEN ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path ((h0:real^2->real^(2,2)finite_sum) o (cp:real^1->real^2)) /\
    pathfinish (h0 o cp) = pathstart (h0 o cp) /\
    path_image (h0 o cp) SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(h0:real^2->real^(2,2)finite_sum) o (cp:real^1->real^2)`; `n:num`] MOI_S4U_PPOW_LOOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `path_image (moi_s4u_ppow ((h0:real^2->real^(2,2)finite_sum) o (cp:real^1->real^2)) n) SUBSET
                sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!q. (h0:real^2->real^(2,2)finite_sum) o reversepath q =
                    reversepath (h0 o q)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; reversepath]; ALL_TAC] THEN
  REWRITE_TAC[] THEN STRIP_TAC THENL
   [EXISTS_TAC `&n` THEN REWRITE_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) h
        (moi_s4u_ppow ((h0:real^2->real^(2,2)finite_sum) o (cp:real^1->real^2)) n)`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM MOI_S4U_PPOW_COMPOSE] THEN USE_THEN "hpush" MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:real^1->real^(2,2)finite_sum`;
                   `moi_s4u_ppow ((h0:real^2->real^(2,2)finite_sum) o (cp:real^1->real^2)) n`]
      MOI_S4U_DISP_HOMOTOPIC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC MOI_S4U_DISP_PPOW THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `-- &n` THEN REWRITE_TAC[INTEGER_NEG; INTEGER_CLOSED] THEN
    SUBGOAL_THEN
     `homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) h
        (reversepath(moi_s4u_ppow ((h0:real^2->real^(2,2)finite_sum) o
                                   (cp:real^1->real^2)) n))`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM MOI_S4U_PPOW_COMPOSE] THEN
      REWRITE_TAC[GSYM(ASSUME `!q. (h0:real^2->real^(2,2)finite_sum) o reversepath q =
                                   reversepath (h0 o q)`)] THEN
      USE_THEN "hpush" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:real^1->real^(2,2)finite_sum`;
                   `reversepath(moi_s4u_ppow ((h0:real^2->real^(2,2)finite_sum) o
                                              (cp:real^1->real^2)) n)`]
      MOI_S4U_DISP_HOMOTOPIC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                      PATH_IMAGE_REVERSEPATH] THEN
      ASM_MESON_TAC[SUBSET_TRANS];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOI_S4U_DISP_REVERSEPATH o lhand o snd) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[MOI_S4U_DISP_PPOW; VECTOR_MUL_LNEG]]);;

(* The lift of a simple closed curve is injective modulo integer vectors  *)
(* on [0,1) (the hypothesis of the separation lemma).                      *)

let MOI_S4U_SIMPLE_LIFT = prove
 (`!g:real^1->real^(2,2)finite_sum.
     simple_path g /\ pathfinish g = pathstart g /\
     path_image g SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
     ==> integer((moi_s4u_disp g)$1) /\ integer((moi_s4u_disp g)$2) /\
         ?h. path h /\ pathfinish h = pathstart h + moi_s4u_disp g /\
             (!t. t IN interval[vec 0,vec 1] ==> moi_s4u_tor (h t) = g t) /\
             (!s t u. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
                      integer(u$1) /\ integer(u$2) /\ h s = h t + u
                      ==> s = t \/ (s = vec 0 /\ t = vec 1) \/ (s = vec 1 /\ t = vec 0))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `g:real^1->real^(2,2)finite_sum` MOI_S4U_LOOP_LIFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLE_PATH_IMP_PATH THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `h:real^1->real^2` STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  EXISTS_TAC `h:real^1->real^2` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MAP_EVERY X_GEN_TAC [`s:real^1`; `t:real^1`; `u:real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^1->real^(2,2)finite_sum) s = g t` ASSUME_TAC THENL
   [MP_TAC(SPEC `s:real^1` (ASSUME `!t. t IN interval[vec 0,vec 1]
        ==> moi_s4u_tor ((h:real^1->real^2) t) = (g:real^1->real^(2,2)finite_sum) t`)) THEN
    MP_TAC(SPEC `t:real^1` (ASSUME `!t. t IN interval[vec 0,vec 1]
        ==> moi_s4u_tor ((h:real^1->real^2) t) = (g:real^1->real^(2,2)finite_sum) t`)) THEN
    REWRITE_TAC[ASSUME `(s:real^1) IN interval[vec 0,vec 1]`;
                ASSUME `(t:real^1) IN interval[vec 0,vec 1]`] THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[ASSUME `(h:real^1->real^2) s = h t + u`] THEN
    MATCH_MP_TAC MOI_S4U_TOR_INTEGER_SHIFT THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `simple_path (g:real^1->real^(2,2)finite_sum)` THEN
  REWRITE_TAC[simple_path] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;
(* A chain of translates of a connected set, each meeting the next.        *)

let MOI_S4U_CHAIN_CONNECTED = prove
 (`!(p:real^N->bool) w a.
     connected p /\ a IN p /\ a + w IN p
     ==> !n. connected (UNIONS (IMAGE (\k. IMAGE (\x. x + &k % w) p) (0..n)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[NUMSEG_SING; IMAGE_CLAUSES; UNIONS_1; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  REWRITE_TAC[NUMSEG_CLAUSES; LE_0; IMAGE_CLAUSES; UNIONS_INSERT] THEN
  MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNIONS; EXISTS_IN_IMAGE; IN_IMAGE] THEN
    EXISTS_TAC `a + &(SUC n) % w:real^N` THEN CONJ_TAC THENL
     [EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG; LE_0; LE_REFL] THEN
      EXISTS_TAC `a + w:real^N` THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
      VECTOR_ARITH_TAC]]);;

(* Loops missing an essential simple closed curve g have displacements     *)
(* parallel to that of g.                                                   *)

let MOI_S4U_TT_PARALLEL = prove
 (`!(g:real^1->real^(2,2)finite_sum) h.
     simple_path g /\ pathfinish g = pathstart g /\
     path_image g SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
     ~(moi_s4u_disp g = vec 0) /\
     path h /\ pathfinish h = pathstart h /\
     path_image h SUBSET
       (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) DIFF path_image g
     ==> moi_s4u_nu (moi_s4u_disp g) (moi_s4u_disp h) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `g:real^1->real^(2,2)finite_sum` MOI_S4U_SIMPLE_LIFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `gl:real^1->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPEC `h:real^1->real^(2,2)finite_sum` MOI_S4U_LOOP_LIFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image (h:real^1->real^(2,2)finite_sum) SUBSET
       (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) DIFF path_image g` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `hl:real^1->real^2` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `d = moi_s4u_disp (g:real^1->real^(2,2)finite_sum)` THEN
  ABBREV_TAC `w = moi_s4u_disp (h:real^1->real^(2,2)finite_sum)` THEN
  MP_TAC(SPECL [`gl:real^1->real^2`; `d:real^2`] MOI_S4U_LINE_SEP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `t:real^1`; `n:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `gl:real^1->real^2`)) (concl th) &&
      can (find_term ((=) `integer:real->bool`)) (concl th))) THEN
    EXISTS_TAC `n % d:real^2` THEN ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    CONJ_TAC THEN MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 INTEGER_CLOSED)))) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `K:real`)] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?N. K + abs(moi_s4u_nu d ((hl:real^1->real^2)(vec 0))) <
                    &N * abs(moi_s4u_nu d w)`
  (X_CHOOSE_TAC `N:num`) THENL
   [MP_TAC(SPEC `abs(moi_s4u_nu d w)` REAL_ARCH) THEN
    ANTS_TAC THENL [UNDISCH_TAC `~(moi_s4u_nu d w = &0)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ACCEPT_TAC o SPEC `K + abs(moi_s4u_nu d ((hl:real^1->real^2)(vec 0)))`);
    ALL_TAC] THEN
  ABBREV_TAC `P = IMAGE (\x:real^2. x - &N % w) (path_image hl)` THEN
  ABBREV_TAC `a = (hl:real^1->real^2)(vec 0) - &N % w` THEN
  SUBGOAL_THEN `(a:real^2) IN P /\ a + w IN P /\ connected (P:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN EXPAND_TAC "a" THEN REWRITE_TAC[IN_IMAGE] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `(hl:real^1->real^2)(vec 0)` THEN
      REWRITE_TAC[path_image; IN_IMAGE] THEN EXISTS_TAC `vec 0:real^1` THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
      EXISTS_TAC `(hl:real^1->real^2)(vec 1)` THEN CONJ_TAC THENL
       [MP_TAC(ASSUME `pathfinish (hl:real^1->real^2) = pathstart hl + w`) THEN
        REWRITE_TAC[pathstart; pathfinish] THEN DISCH_THEN SUBST1_TAC THEN
        VECTOR_ARITH_TAC;
        REWRITE_TAC[path_image; IN_IMAGE] THEN EXISTS_TAC `vec 1:real^1` THEN
        REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[CONNECTED_PATH_IMAGE; CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID;
                   CONTINUOUS_ON_CONST]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:real^2->bool`; `w:real^2`; `a:real^2`] MOI_S4U_CHAIN_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `2 * N`) THEN
  ABBREV_TAC `S = UNIONS (IMAGE (\k. IMAGE (\x:real^2. x + &k % w) P) (0..2 * N))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!y. y IN S ==> ?s k. s IN interval[vec 0,vec 1] /\
                               (y:real^2) = (hl:real^1->real^2) s + (&k - &N) % w`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN EXPAND_TAC "P" THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_IMAGE; path_image] THEN
    X_GEN_TAC `y:real^2` THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `z:real^2` (CONJUNCTS_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `x:real^2` (CONJUNCTS_THEN2 SUBST1_TAC
          (X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC))))))) THEN
    MAP_EVERY EXISTS_TAC [`s:real^1`; `k:num`] THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `S:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^2`; `t:real^1`; `n:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^1` (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC)) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^1->real^(2,2)finite_sum) s = (g:real^1->real^(2,2)finite_sum) t`
    MP_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `moi_s4u_tor (y:real^2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `moi_s4u_tor ((hl:real^1->real^2) s)` THEN
        CONJ_TAC THENL
         [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          REWRITE_TAC[ASSUME `y:real^2 = (hl:real^1->real^2) s + (&k - &N) % w`] THEN
          CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_S4U_TOR_INTEGER_SHIFT THEN
          REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN CONJ_TAC THEN
          MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 INTEGER_CLOSED)))) THEN
          ASM_SIMP_TAC[INTEGER_CLOSED]];
        MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `moi_s4u_tor ((gl:real^1->real^2) t)` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[ASSUME `y:real^2 = (gl:real^1->real^2) t + n % d`] THEN
          MATCH_MP_TAC MOI_S4U_TOR_INTEGER_SHIFT THEN
          REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN CONJ_TAC THEN
          MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 INTEGER_CLOSED)))) THEN
          ASM_REWRITE_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
      ALL_TAC] THEN
    UNDISCH_TAC `path_image (h:real^1->real^(2,2)finite_sum) SUBSET
       (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) DIFF path_image g` THEN
    REWRITE_TAC[SUBSET; path_image; FORALL_IN_IMAGE] THEN REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^1`) THEN
    REWRITE_TAC[ASSUME `(s:real^1) IN interval[vec 0,vec 1]`] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    REWRITE_TAC[] THEN EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the two far points *)
  SUBGOAL_THEN `(a:real^2) IN S /\ a + (&2 * &N) % w IN S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_IMAGE] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `0` THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN EXISTS_TAC `a:real^2` THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      EXISTS_TAC `2 * N` THEN REWRITE_TAC[IN_NUMSEG; LE_0; LE_REFL] THEN
      EXISTS_TAC `a:real^2` THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s4u_nu d a = moi_s4u_nu d ((hl:real^1->real^2)(vec 0)) - &N * moi_s4u_nu d w /\
    moi_s4u_nu d (a + (&2 * &N) % w) =
    moi_s4u_nu d ((hl:real^1->real^2)(vec 0)) + &N * moi_s4u_nu d w`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[MOI_S4U_NU_LINEAR] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISJ_CASES_TAC(MATCH_MP (REAL_ARITH `~(x = &0) ==> &0 < x \/ x < &0`)
                          (ASSUME `~(moi_s4u_nu d w = &0)`)) THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `a + (&2 * &N) % w:real^2`;
      EXISTS_TAC `a:real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `K + abs(moi_s4u_nu d ((hl:real^1->real^2)(vec 0))) <
                 &N * abs(moi_s4u_nu d w)` THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN REAL_ARITH_TAC;
    CONJ_TAC THENL
     [EXISTS_TAC `a:real^2`;
      EXISTS_TAC `a + (&2 * &N) % w:real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `K + abs(moi_s4u_nu d ((hl:real^1->real^2)(vec 0))) <
                 &N * abs(moi_s4u_nu d w)` THEN
    ASM_SIMP_TAC[REAL_ARITH `x < &0 ==> abs x = --x`] THEN REAL_ARITH_TAC]);;
(* The displacement of an essential simple closed curve is primitive: an  *)
(* integer vector parallel to it is an integer multiple of it.            *)

let MOI_S4U_TT_PRIMITIVE = prove
 (`!(g:real^1->real^(2,2)finite_sum) w.
     simple_path g /\ pathfinish g = pathstart g /\
     path_image g SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
     ~(moi_s4u_disp g = vec 0) /\
     integer(w$1) /\ integer(w$2) /\ moi_s4u_nu (moi_s4u_disp g) w = &0
     ==> ?m. integer m /\ w = m % moi_s4u_disp g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `g:real^1->real^(2,2)finite_sum` MOI_S4U_SIMPLE_LIFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `gl:real^1->real^2` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `d = moi_s4u_disp (g:real^1->real^(2,2)finite_sum)` THEN
  MP_TAC(SPECL [`gl:real^1->real^2`; `d:real^2`; `w:real^2`] MOI_S4U_PARALLEL_MEETS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `t:real^1`; `n:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `gl:real^1->real^2`)) (concl th) &&
      can (find_term ((=) `integer:real->bool`)) (concl th))) THEN
    EXISTS_TAC `n % d:real^2` THEN ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    CONJ_TAC THEN MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 INTEGER_CLOSED)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^1` (X_CHOOSE_THEN `t:real^1`
    (X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^1`; `t:real^1`; `w + n % d:real^2`] o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `gl:real^1->real^2`)) (concl th) &&
    can (find_term ((=) `integer:real->bool`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    CONJ_TAC THEN MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 INTEGER_CLOSED)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 INTEGER_CLOSED)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gl:real^1->real^2)(vec 1) = gl(vec 0) + d` ASSUME_TAC THENL
   [MP_TAC(ASSUME `pathfinish (gl:real^1->real^2) = pathstart gl + d`) THEN
    REWRITE_TAC[pathstart; pathfinish];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `--n:real` THEN ASM_REWRITE_TAC[INTEGER_NEG] THEN
    UNDISCH_TAC `(gl:real^1->real^2) s = gl t + w + n % d` THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    EXISTS_TAC `--n - &1:real` THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN
    UNDISCH_TAC `(gl:real^1->real^2) s = gl t + w + n % d` THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    EXISTS_TAC `&1 - n:real` THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN
    UNDISCH_TAC `(gl:real^1->real^2) s = gl t + w + n % d` THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC]);;

(* Loops missing an essential circle in the round torus are homotopic to  *)
(* loops in the circle.                                                    *)

let MOI_S4U_TT_CURVE_LOOPS = prove
 (`!(c:real^(2,2)finite_sum->bool) h.
     c SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
     c homeomorphic sphere(vec 0:real^2,&1) /\
     (?k. path k /\ pathfinish k = pathstart k /\ path_image k SUBSET c /\
          ~homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
                           k (linepath(pathstart k,pathstart k))) /\
     path h /\ pathfinish h = pathstart h /\
     path_image h SUBSET (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) DIFF c
     ==> ?h'. path h' /\ pathfinish h' = pathstart h' /\ path_image h' SUBSET c /\
              homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) h h'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^1->real^(2,2)finite_sum` STRIP_ASSUME_TAC)
      STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPEC `c:real^(2,2)finite_sum->bool` MOI_S4U_TT_CURVE_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^(2,2)finite_sum` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path_image (h:real^1->real^(2,2)finite_sum) SUBSET
                sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
                path_image (k:real^1->real^(2,2)finite_sum) SUBSET
                sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
                path_image (g:real^1->real^(2,2)finite_sum) SUBSET
                sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`path_image (h:real^1->real^(2,2)finite_sum) SUBSET
       (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) DIFF c`;
      `path_image (k:real^1->real^(2,2)finite_sum) SUBSET c`;
      `(c:real^(2,2)finite_sum->bool) SUBSET
       sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the displacement of g is nonzero *)
  SUBGOAL_THEN `~(moi_s4u_disp (g:real^1->real^(2,2)finite_sum) = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
                   (k:real^1->real^(2,2)finite_sum) (linepath(pathstart k,pathstart k))` THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `pathstart (k:real^1->real^(2,2)finite_sum) IN
                  sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `k:real^1->real^(2,2)finite_sum` PATHSTART_IN_PATH_IMAGE) THEN
      UNDISCH_TAC `path_image (k:real^1->real^(2,2)finite_sum) SUBSET
                   sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:real^1->real^(2,2)finite_sum`;
                   `linepath(pathstart (k:real^1->real^(2,2)finite_sum),pathstart k)`]
      MOI_S4U_DISP_HOMOTOPIC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                      PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[MOI_S4U_DISP_CONST] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^1->real^(2,2)finite_sum` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `integer:real->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  (* the displacement of h is parallel to, hence a multiple of, that of g *)
  MP_TAC(SPECL [`g:real^1->real^(2,2)finite_sum`; `h:real^1->real^(2,2)finite_sum`]
    MOI_S4U_TT_PARALLEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `h:real^1->real^(2,2)finite_sum` MOI_S4U_LOOP_LIFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  MP_TAC(SPECL [`g:real^1->real^(2,2)finite_sum`;
                `moi_s4u_disp (h:real^1->real^(2,2)finite_sum)`] MOI_S4U_TT_PRIMITIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`g:real^1->real^(2,2)finite_sum`; `m:real`] MOI_S4U_DISP_MULTIPLE) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [MATCH_MP_TAC SIMPLE_PATH_IMP_PATH THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h':real^1->real^(2,2)finite_sum` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h':real^1->real^(2,2)finite_sum` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:real^1->real^(2,2)finite_sum`; `h':real^1->real^(2,2)finite_sum`]
    MOI_S4U_DISP_HOMOTOPIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image (h':real^1->real^(2,2)finite_sum) SUBSET c` THEN
    UNDISCH_TAC `(c:real^(2,2)finite_sum->bool) SUBSET
                 sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
    SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Torus surfaces and H_1.  Transfer of MOI_S4U_TT_CURVE_LOOPS to any       *)
(* set homeomorphic to S1 x S1 (MOI_S4U_CURVE_LOOPS); the image of H_1(x)   *)
(* in H_1(y) lies in a subgroup containing the classes of all loops in x    *)
(* (MOI_S4U_H1_IMAGE_LOOPS, from additivity over path components); a       *)
(* carrying union of disjoint circles in a torus surface has a carrying     *)
(* component (MOI_S4U_T1); a carrying circle and a carrying open set on the *)
(* other side of an open cover of the torus surface give a carrying         *)
(* intersection (MOI_S4U_SEP, Mayer-Vietoris).                               *)
(* ------------------------------------------------------------------------- *)

let MOI_S4U_CURVE_LOOPS = prove
 (`!(th:real^N->bool) c h.
     torus_surface th /\ c SUBSET th /\ c homeomorphic sphere(vec 0:real^2,&1) /\
     (?k. path k /\ pathfinish k = pathstart k /\ path_image k SUBSET c /\
          ~homotopic_loops th k (linepath(pathstart k,pathstart k))) /\
     path h /\ pathfinish h = pathstart h /\ path_image h SUBSET th DIFF c
     ==> ?h'. path h' /\ pathfinish h' = pathstart h' /\ path_image h' SUBSET c /\
              homotopic_loops th h h'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `k:real^1->real^N` STRIP_ASSUME_TAC)
      STRIP_ASSUME_TAC)))) THEN
  REWRITE_TAC[torus_surface; homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `ph:real^N->real^(2,2)finite_sum`
    (X_CHOOSE_THEN `ps:real^(2,2)finite_sum->real^N` ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism]) THEN
  (* pulling a loop of the model torus back to th *)
  SUBGOAL_THEN
   `!p q. homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
            ((ph:real^N->real^(2,2)finite_sum) o p) q /\
          path p /\ pathfinish p = pathstart p /\ path_image p SUBSET th
          ==> homotopic_loops th p ((ps:real^(2,2)finite_sum->real^N) o q)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `(ps:real^(2,2)finite_sum->real^N) o (ph:real^N->real^(2,2)finite_sum) o
                (p:real^1->real^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[o_THM] THEN
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `path_image (p:real^1->real^N) SUBSET th` THEN
      REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
      EXISTS_TAC `sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
      ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. path p /\ pathfinish p = pathstart p /\ path_image p SUBSET th
        ==> path ((ph:real^N->real^(2,2)finite_sum) o p) /\
            pathfinish (ph o p) = pathstart (ph o p) /\
            path_image (ph o p) = IMAGE ph (path_image p)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `th:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (ph:real^N->real^(2,2)finite_sum) c`;
                 `(ph:real^N->real^(2,2)finite_sum) o (h:real^1->real^N)`] MOI_S4U_TT_CURVE_LOOPS) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `path_image (k:real^1->real^N) SUBSET th /\
                  path_image (h:real^1->real^N) SUBSET th` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`path_image (k:real^1->real^N) SUBSET c`;
                             `path_image (h:real^1->real^N) SUBSET th DIFF c`;
                             `(c:real^N->bool) SUBSET th`] THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (ph:real^N->real^(2,2)finite_sum) th =
                   sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
      UNDISCH_TAC `(c:real^N->bool) SUBSET th` THEN SET_TAC[];
      MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN EXISTS_TAC `c:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FH1_IMAGE_HOMEOMORPHIC THEN
      MAP_EVERY EXISTS_TAC
       [`th:real^N->bool`; `sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
        `ps:real^(2,2)finite_sum->real^N`] THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `(ph:real^N->real^(2,2)finite_sum) o (k:real^1->real^N)` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:real^1->real^N` o check (fun th ->
        can (find_term ((=) `path_image:(real^1->real^N)->real^N->bool`)) (concl th) &&
        is_forall (concl th) && not (can (find_term ((=) `ps:real^(2,2)finite_sum->real^N`))
                                         (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `path_image (k:real^1->real^N) SUBSET c` THEN SET_TAC[];
        DISCH_TAC THEN
        UNDISCH_TAC `~homotopic_loops th (k:real^1->real^N)
                        (linepath(pathstart k,pathstart k))` THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`k:real^1->real^N`;
          `linepath(pathstart ((ph:real^N->real^(2,2)finite_sum) o (k:real^1->real^N)),
                    pathstart (ph o k))`] o check (fun th ->
           can (find_term ((=) `ps:real^(2,2)finite_sum->real^N`)) (concl th) &&
           is_forall (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(ps:real^(2,2)finite_sum->real^N) o
                      linepath(pathstart ((ph:real^N->real^(2,2)finite_sum) o
                                          (k:real^1->real^N)),pathstart (ph o k)) =
                      linepath(pathstart k,pathstart k)` SUBST1_TAC THENL
         [REWRITE_TAC[LINEPATH_REFL; FUN_EQ_THM; o_THM; PATHSTART_COMPOSE] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          MP_TAC(ISPEC `k:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN
          UNDISCH_TAC `path_image (k:real^1->real^N) SUBSET th` THEN SET_TAC[];
          SIMP_TAC[]]];
      FIRST_X_ASSUM(MP_TAC o SPEC `h:real^1->real^N` o check (fun th ->
        can (find_term ((=) `path_image:(real^1->real^N)->real^N->bool`)) (concl th) &&
        is_forall (concl th) && not (can (find_term ((=) `ps:real^(2,2)finite_sum->real^N`))
                                         (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `h:real^1->real^N` o check (fun th ->
        can (find_term ((=) `path_image:(real^1->real^N)->real^N->bool`)) (concl th) &&
        is_forall (concl th) && not (can (find_term ((=) `ps:real^(2,2)finite_sum->real^N`))
                                         (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `h:real^1->real^N` o check (fun th ->
        can (find_term ((=) `path_image:(real^1->real^N)->real^N->bool`)) (concl th) &&
        is_forall (concl th) && not (can (find_term ((=) `ps:real^(2,2)finite_sum->real^N`))
                                         (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`path_image (h:real^1->real^N) SUBSET th DIFF c`;
        `(c:real^N->bool) SUBSET th`;
        `!x. x IN th ==> (ps:real^(2,2)finite_sum->real^N) (ph x) = x`;
        `IMAGE (ph:real^N->real^(2,2)finite_sum) th =
         sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^(2,2)finite_sum` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(ps:real^(2,2)finite_sum->real^N) o (q:real^1->real^(2,2)finite_sum)` THEN
  REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image (q:real^1->real^(2,2)finite_sum) SUBSET
                 IMAGE (ph:real^N->real^(2,2)finite_sum) c` THEN
    UNDISCH_TAC `(c:real^N->bool) SUBSET th` THEN
    UNDISCH_TAC `IMAGE (ph:real^N->real^(2,2)finite_sum) th =
                 sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN SET_TAC[];
    UNDISCH_TAC `path_image (q:real^1->real^(2,2)finite_sum) SUBSET
                 IMAGE (ph:real^N->real^(2,2)finite_sum) c` THEN
    UNDISCH_TAC `(c:real^N->bool) SUBSET th` THEN
    UNDISCH_TAC `!x. x IN th ==> (ps:real^(2,2)finite_sum->real^N) (ph x) = x` THEN
    SET_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `ps:real^(2,2)finite_sum->real^N`)) (concl th) &&
      is_forall (concl th) &&
      can (find_term ((=) `homotopic_loops:(real^N->bool)->(real^1->real^N)->
                                           (real^1->real^N)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path_image (h:real^1->real^N) SUBSET th DIFF c` THEN SET_TAC[]]);;
(* The image of H_1(x) in H_1(y) lies in any subgroup containing the       *)
(* classes of all loops in x (H_1 is the sum over the path components, and *)
(* H_1 of a path-connected set consists of loop classes).                  *)

let MOI_S4U_H1_IMAGE_LOOPS = prove
 (`!(x:real^N->bool) y h.
     x SUBSET y /\ h subgroup_of homology_group(&1,subtopology euclidean y) /\
     (!g. path g /\ pathfinish g = pathstart g /\ path_image g SUBSET x
          ==> homologous_rel (1,subtopology euclidean y,{})
                (frag_of (path_simplex (g o lift))) IN h)
     ==> group_image (homology_group(&1,subtopology euclidean x),
                      homology_group(&1,subtopology euclidean y))
                     (hom_induced (&1) (subtopology euclidean x,{})
                                       (subtopology euclidean y,{}) (\x. x))
         SUBSET h`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `j = hom_induced (&1) (subtopology euclidean (x:real^N->bool),{})
                                   (subtopology euclidean y,{}) (\x:real^N. x)` THEN
  ABBREV_TAC `u = {path_component (x:real^N->bool) a | a | a IN x}` THEN
  (* every path component maps into h *)
  SUBGOAL_THEN
   `!v c. v IN u /\
          c IN group_carrier (homology_group(&1,subtopology (subtopology euclidean x) v))
          ==> (j:(((num->real)->real^N)frag->bool)->((num->real)->real^N)frag->bool)
                (hom_induced (&1) (subtopology (subtopology euclidean x) v,{})
                                  (subtopology euclidean (x:real^N->bool),{}) (\z. z) c)
              IN h`
  ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
    MAP_EVERY X_GEN_TAC [`v:real^N->bool`; `c:((num->real)->real^N)frag->bool`;
                         `a:real^N`] THEN
    DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[MOI_S4J_SUBTOP; PATH_COMPONENT_SUBSET] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`path_component (x:real^N->bool) a`; `a:real^N`;
                   `c:((num->real)->real^N)frag->bool`] MOI_FH1_H1_LOOP_REPRESENTATIVE) THEN
    ASM_REWRITE_TAC[PATH_CONNECTED_PATH_COMPONENT] THEN
    ANTS_TAC THENL [REWRITE_TAC[IN] THEN MATCH_MP_TAC PATH_COMPONENT_REFL THEN
                    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `path_image (g:real^1->real^N) SUBSET x` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `path_component (x:real^N->bool) a` THEN
      ASM_REWRITE_TAC[PATH_COMPONENT_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `path_in (subtopology euclidean (path_component (x:real^N->bool) a))
                    ((g:real^1->real^N) o lift) /\
                  path_in (subtopology euclidean x) (g o lift) /\
                  (g o lift) (&0) = (g o lift) (&1)` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM PATH_EUCLIDEAN; o_THM; LIFT_NUM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!f:real->real^N. (\z:real^N. z) o f = f` ASSUME_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOI_FH1_HOM_INDUCED_LOOP o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION; PATH_COMPONENT_SUBSET];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "j" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOI_FH1_HOM_INDUCED_LOOP o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `h:(((num->real)->real^N)frag->bool)->bool`))
                                  (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* additivity *)
  MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (x:real^N->bool)`; `u:(real^N->bool)->bool`]
    HOMOLOGY_ADDITIVITY_AXIOM_GEN) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; UNIONS_PATH_COMPONENT] THEN
    REWRITE_TAC[PATH_CONNECTED_IN_SUBTOPOLOGY; PATH_CONNECTED_IN_EUCLIDEAN; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[pairwise; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC) MP_TAC)) THEN
      ASM_REWRITE_TAC[PATH_COMPONENT_DISJOINT] THEN
      DISCH_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `~(path_component (x:real^N->bool) a = path_component x b)` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC PATH_COMPONENT_EQ THEN FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `t:real^N->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) MP_TAC))) THEN
      ASM_REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `path_component (x:real^N->bool) b = path_component x a` (SUBST1_TAC o SYM)
      THENL [MATCH_MP_TAC PATH_COMPONENT_EQ THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC PATH_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_EPIMORPHISM) THEN
  REWRITE_TAC[group_epimorphism] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[SUBSET; group_image; FORALL_IN_IMAGE] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `xx:(real^N->bool)->((num->real)->real^N)frag->bool` THEN DISCH_TAC THEN
  ABBREV_TAC `G = homology_group(&1,subtopology euclidean (x:real^N->bool))` THEN
  SUBGOAL_THEN
   `iterate (group_add G) u
      (\v. hom_induced (&1) (subtopology (subtopology euclidean (x:real^N->bool)) v,{})
                            (subtopology euclidean x,{}) (\z. z)
             ((xx:(real^N->bool)->((num->real)->real^N)frag->bool) v)) IN
    {z | z IN group_carrier G /\
         (j:(((num->real)->real^N)frag->bool)->((num->real)->real^N)frag->bool) z IN h}`
  MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]] THEN
  W(MP_TAC o PART_MATCH (rand o rand) ABELIAN_GROUP_SUM_ITERATE o lhand o snd) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[ABELIAN_HOMOLOGY_GROUP] THEN
    REWRITE_TAC[homology_group; HOM_INDUCED];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC IN_SUBGROUP_SUM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBGROUP_OF_HOMOMORPHIC_PREIMAGE THEN
    EXISTS_TAC `homology_group(&1,subtopology euclidean (y:real^N->bool))` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "j" THEN EXPAND_TAC "G" THEN
    REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^N->bool` THEN BETA_TAC THEN STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `u:(real^N->bool)->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(xx:(real^N->bool)->((num->real)->real^N)frag->bool) IN
               group_carrier (sum_group u
                 (\s. homology_group(&1,subtopology (subtopology euclidean x) s)))` THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
    (ISPECL [`product_group (u:(real^N->bool)->bool)
               (\s. homology_group(&1,subtopology (subtopology euclidean (x:real^N->bool)) s))`;
             `{z | z IN cartesian_product (u:(real^N->bool)->bool)
                     (\i. group_carrier ((\s. homology_group(&1,subtopology
                            (subtopology euclidean (x:real^N->bool)) s)) i)) /\
                   FINITE {i | i IN u /\ ~(z i = group_id ((\s. homology_group(&1,
                     subtopology (subtopology euclidean x) s)) i))}}`]
     GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET)) o REWRITE_RULE[sum_group]) THEN
  REWRITE_TAC[PRODUCT_GROUP; IN_CARTESIAN_PRODUCT] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N->bool` o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;
(* Loop classes lie in the image; images compose; a Mayer-Vietoris lift.  *)

let MOI_S4U_LOOP_CLASS_IMAGE = prove
 (`!(x:real^N->bool) y g.
     x SUBSET y /\ path g /\ pathfinish g = pathstart g /\ path_image g SUBSET x
     ==> homologous_rel (1,subtopology euclidean y,{})
           (frag_of (path_simplex (g o lift))) IN
         group_image (homology_group(&1,subtopology euclidean x),
                      homology_group(&1,subtopology euclidean y))
                     (hom_induced (&1) (subtopology euclidean x,{})
                                       (subtopology euclidean y,{}) (\x. x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_image; IN_IMAGE] THEN
  EXISTS_TAC `homologous_rel (1,subtopology euclidean (x:real^N->bool),{})
                (frag_of (path_simplex ((g:real^1->real^N) o lift)))` THEN
  SUBGOAL_THEN `path_in (subtopology euclidean (x:real^N->bool)) ((g:real^1->real^N) o lift) /\
                (g o lift) (&0) = (g o lift) (&1)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM PATH_EUCLIDEAN; o_THM; LIFT_NUM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FH1_LOOP_CLASS_IN_CARRIER] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOI_FH1_HOM_INDUCED_LOOP o rand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_ASSOC; I_O_ID; GSYM I_DEF]);;

let MOI_S4U_IMAGE_COMPOSE = prove
 (`!(x:real^N->bool) y z.
     x SUBSET y /\ y SUBSET z
     ==> group_image (homology_group(&1,subtopology euclidean x),
                      homology_group(&1,subtopology euclidean z))
                     (hom_induced (&1) (subtopology euclidean x,{})
                                       (subtopology euclidean z,{}) (\x. x)) =
         IMAGE (hom_induced (&1) (subtopology euclidean y,{})
                                 (subtopology euclidean z,{}) (\x. x))
               (group_image (homology_group(&1,subtopology euclidean x),
                             homology_group(&1,subtopology euclidean y))
                            (hom_induced (&1) (subtopology euclidean x,{})
                                              (subtopology euclidean y,{}) (\x. x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_image; GSYM IMAGE_o] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(\x:real^N. x) = (\x. x) o (\x. x)` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC HOM_INDUCED_COMPOSE_EMPTY THEN
  ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION]);;

let MOI_S4U_MV_LIFT = prove
 (`!top s t (a:((num->real)->A)frag->bool).
     open_in top s /\ open_in top t /\ topspace top = s UNION t /\
     a IN group_carrier (homology_group(&1,subtopology top s)) /\
     hom_induced (&1) (subtopology top s,{}) (top,{}) (\x. x) a IN
     group_image (homology_group(&1,subtopology top t),homology_group(&1,top))
                 (hom_induced (&1) (subtopology top t,{}) (top,{}) (\x. x))
     ==> ?c. c IN group_carrier (homology_group(&1,subtopology top (s INTER t))) /\
             hom_induced (&1) (subtopology top (s INTER t),{}) (subtopology top s,{})
                         (\x. x) c = a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  REWRITE_TAC[group_image; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:((num->real)->A)frag->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`&1:int`; `top:A topology`; `s:A->bool`; `t:A->bool`]
    (REWRITE_RULE[ATOP_MAYER_VIETORIS_STATEMENT] ATOP_MAYER_VIETORIS)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:(((num->real)->A)frag->bool)->((num->real)->A)frag->bool`
    (MP_TAC o CONJUNCT1)) THEN
  DISCH_THEN(MP_TAC o SPEC
   `(a:((num->real)->A)frag->bool,b:((num->real)->A)frag->bool)` o
   MATCH_MP (REWRITE_RULE[IMP_CONJ] ATOP_EXACT_IMAGE)) THEN
  REWRITE_TAC[PROD_GROUP; IN_CROSS] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq (concl th) && can (find_term ((=) `b:((num->real)->A)frag->bool`)) (concl th))) THEN
    MATCH_MP_TAC GROUP_DIV_REFL THEN
    REWRITE_TAC[homology_group; HOM_INDUCED];
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]]);;
(* A loop in a set all of whose loops are null-homotopic in y has trivial *)
(* class in H_1(y); the image subgroup of a circle in a torus surface.     *)

let MOI_S4U_IMAGE_SUBGROUP = prove
 (`!(x:real^N->bool) y.
     group_image (homology_group(&1,subtopology euclidean x),
                  homology_group(&1,subtopology euclidean y))
                 (hom_induced (&1) (subtopology euclidean x,{})
                                   (subtopology euclidean y,{}) (\x. x))
     subgroup_of homology_group(&1,subtopology euclidean y)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBGROUP_GROUP_IMAGE THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY]);;

let MOI_S4U_IMAGE_TRIVIAL = prove
 (`!(x:real^N->bool) y.
     x SUBSET y /\
     (!g. path g /\ pathfinish g = pathstart g /\ path_image g SUBSET x
          ==> homotopic_loops y g (linepath(pathstart g,pathstart g)))
     ==> group_image (homology_group(&1,subtopology euclidean x),
                      homology_group(&1,subtopology euclidean y))
                     (hom_induced (&1) (subtopology euclidean x,{})
                                       (subtopology euclidean y,{}) (\x. x))
         SUBSET {group_id (homology_group(&1,subtopology euclidean y))}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4U_H1_IMAGE_LOOPS THEN
  ASM_REWRITE_TAC[TRIVIAL_SUBGROUP_OF; IN_SING] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_FH1_NULLHOMOTOPIC_LOOP_CLASS THEN ASM_SIMP_TAC[]);;

(* T1: a carrying union of circles in a torus surface has a carrying       *)
(* component.                                                               *)

let MOI_S4U_T1 = prove
 (`!(th:real^N->bool) s z.
     torus_surface th /\ th SUBSET s /\ z SUBSET th /\ ~(z = {}) /\
     (!c. c IN components z ==> c homeomorphic sphere(vec 0:real^2,&1)) /\
     carries_h1 z s
     ==> ?c. c IN components z /\ carries_h1 c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `?c k. c IN components z /\
          path k /\ pathfinish k = pathstart k /\ path_image k SUBSET c /\
          ~homotopic_loops (th:real^N->bool) k (linepath(pathstart k,pathstart k))` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c:real^N->bool) SUBSET z` ASSUME_TAC THENL
     [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `group_image (homology_group(&1,subtopology euclidean z),
                   homology_group(&1,subtopology euclidean th))
                  (hom_induced (&1) (subtopology euclidean z,{})
                                    (subtopology euclidean th,{}) (\x:real^N. x)) SUBSET
      group_image (homology_group(&1,subtopology euclidean c),
                   homology_group(&1,subtopology euclidean th))
                  (hom_induced (&1) (subtopology euclidean c,{})
                                    (subtopology euclidean th,{}) (\x:real^N. x))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4U_H1_IMAGE_LOOPS THEN
      ASM_REWRITE_TAC[MOI_S4U_IMAGE_SUBGROUP] THEN
      X_GEN_TAC `g:real^1->real^N` THEN STRIP_TAC THEN
      ASM_CASES_TAC `path_image (g:real^1->real^N) INTER c = {}` THENL
       [MP_TAC(ISPECL [`th:real^N->bool`; `c:real^N->bool`; `g:real^1->real^N`]
          MOI_S4U_CURVE_LOOPS) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
           [ASM_MESON_TAC[SUBSET_TRANS];
            EXISTS_TAC `k:real^1->real^N` THEN ASM_REWRITE_TAC[];
            MAP_EVERY UNDISCH_TAC
             [`path_image (g:real^1->real^N) INTER c = {}`;
              `path_image (g:real^1->real^N) SUBSET z`; `(z:real^N->bool) SUBSET th`] THEN
            SET_TAC[]];
          DISCH_THEN(X_CHOOSE_THEN `g':real^1->real^N` STRIP_ASSUME_TAC)] THEN
        FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_FH1_LOOP_CLASS_HOMOTOPIC) THEN
        MATCH_MP_TAC MOI_S4U_LOOP_CLASS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[SUBSET_TRANS];
        MATCH_MP_TAC MOI_S4U_LOOP_CLASS_IMAGE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
        MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `z:real^N->bool` THEN
        ASM_SIMP_TAC[CONNECTED_PATH_IMAGE] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `carries_h1 (z:real^N->bool) s` THEN REWRITE_TAC[carries_h1] THEN
    MP_TAC(ISPECL [`z:real^N->bool`; `th:real^N->bool`; `s:real^N->bool`]
      MOI_S4U_IMAGE_COMPOSE) THEN
    MP_TAC(ISPECL [`c:real^N->bool`; `th:real^N->bool`; `s:real^N->bool`]
      MOI_S4U_IMAGE_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[homology_group; HOM_INDUCED];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* every circle is inessential: the image of H_1 z is trivial *)
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN
  SUBGOAL_THEN `?c:real^N->bool. c IN components z` (X_CHOOSE_TAC `c:real^N->bool`) THENL
   [UNDISCH_TAC `~(z:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MESON_TAC[CONNECTED_COMPONENT_IN_COMPONENTS];
    ALL_TAC] THEN
  EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `group_image (homology_group(&1,subtopology euclidean z),
                 homology_group(&1,subtopology euclidean th))
                (hom_induced (&1) (subtopology euclidean z,{})
                                  (subtopology euclidean th,{}) (\x:real^N. x)) SUBSET
    {group_id (homology_group(&1,subtopology euclidean th))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4U_IMAGE_TRIVIAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `g:real^1->real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`connected_component (z:real^N->bool) (pathstart g)`; `g:real^1->real^N`]) THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN
    SUBGOAL_THEN `pathstart (g:real^1->real^N) IN z` ASSUME_TAC THENL
     [MP_TAC(ISPEC `g:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN
      UNDISCH_TAC `path_image (g:real^1->real^N) SUBSET z` THEN SET_TAC[];
      ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(TAUT `p ==> (~p \/ q) ==> q`) THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM_SIMP_TAC[CONNECTED_PATH_IMAGE; PATHSTART_IN_PATH_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `group_carrier (homology_group(&1,subtopology euclidean (s:real^N->bool))) SUBSET
    {group_id (homology_group(&1,subtopology euclidean s))}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `carries_h1 (z:real^N->bool) s` THEN REWRITE_TAC[carries_h1] THEN
    MP_TAC(ISPECL [`z:real^N->bool`; `th:real^N->bool`; `s:real^N->bool`]
      MOI_S4U_IMAGE_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (hom_induced (&1) (subtopology euclidean th,{})
                                        (subtopology euclidean s,{}) (\x:real^N. x))
                      {group_id (homology_group(&1,subtopology euclidean th))}` THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_CLAUSES; SING_SUBSET; IN_SING] THEN
    MATCH_MP_TAC ATOP_GROUP_HOM_ID THEN REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[carries_h1] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; group_image; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[homology_group; HOM_INDUCED];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{group_id (homology_group(&1,subtopology euclidean (s:real^N->bool)))}` THEN
    ASM_REWRITE_TAC[SING_SUBSET; group_image; IN_IMAGE] THEN
    EXISTS_TAC `group_id(homology_group(&1,subtopology euclidean (c:real^N->bool)))` THEN
    REWRITE_TAC[GROUP_ID] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC ATOP_GROUP_HOM_ID THEN REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY]]);;
(* SEP: if a circle c in a torus surface th carries H_1(s), H_1(s) is      *)
(* nontrivial, and th = a UNION b is an open cover with c in b and a       *)
(* missing c, then a INTER b carries H_1(s) as soon as a does.             *)

let MOI_S4U_SEP = prove
 (`!(th:real^N->bool) s c a b.
     torus_surface th /\ th SUBSET s /\ c SUBSET th /\
     c homeomorphic sphere(vec 0:real^2,&1) /\ carries_h1 c s /\
     ~trivial_group(homology_group(&1,subtopology euclidean s)) /\
     open_in (subtopology euclidean th) a /\ open_in (subtopology euclidean th) b /\
     a UNION b = th /\ c SUBSET b /\ a INTER c = {} /\ carries_h1 a s
     ==> carries_h1 (a INTER b) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^N->bool) SUBSET th /\ (b:real^N->bool) SUBSET th` STRIP_ASSUME_TAC
  THENL
   [UNDISCH_TAC `(a:real^N->bool) UNION b = th` THEN SET_TAC[]; ALL_TAC] THEN
  (* c is essential in th *)
  SUBGOAL_THEN
   `?k. path k /\ pathfinish k = pathstart k /\ path_image k SUBSET c /\
        ~homotopic_loops (th:real^N->bool) k (linepath(pathstart k,pathstart k))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_THEN(ASSUME_TAC o
      REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(p /\ q /\ r /\ ~s) <=> p /\ q /\ r ==> s`]) THEN
    MP_TAC(ISPECL [`c:real^N->bool`; `th:real^N->bool`] MOI_S4U_IMAGE_TRIVIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~trivial_group(homology_group(&1,subtopology euclidean (s:real^N->bool)))` THEN
    REWRITE_TAC[trivial_group] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SING_SUBSET; GROUP_ID] THEN
    UNDISCH_TAC `carries_h1 (c:real^N->bool) s` THEN REWRITE_TAC[carries_h1] THEN
    MP_TAC(ISPECL [`c:real^N->bool`; `th:real^N->bool`; `s:real^N->bool`]
      MOI_S4U_IMAGE_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (hom_induced (&1) (subtopology euclidean th,{})
                                        (subtopology euclidean s,{}) (\x:real^N. x))
                      {group_id (homology_group(&1,subtopology euclidean th))}` THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_CLAUSES; SING_SUBSET; IN_SING] THEN
    MATCH_MP_TAC ATOP_GROUP_HOM_ID THEN REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    ALL_TAC] THEN
  (* the image of H_1(a) in H_1(th) lies in that of H_1(b) *)
  SUBGOAL_THEN
   `group_image (homology_group(&1,subtopology euclidean a),
                 homology_group(&1,subtopology euclidean th))
                (hom_induced (&1) (subtopology euclidean a,{})
                                  (subtopology euclidean th,{}) (\x:real^N. x)) SUBSET
    group_image (homology_group(&1,subtopology euclidean b),
                 homology_group(&1,subtopology euclidean th))
                (hom_induced (&1) (subtopology euclidean b,{})
                                  (subtopology euclidean th,{}) (\x:real^N. x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4U_H1_IMAGE_LOOPS THEN ASM_REWRITE_TAC[MOI_S4U_IMAGE_SUBGROUP] THEN
    X_GEN_TAC `g:real^1->real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`th:real^N->bool`; `c:real^N->bool`; `g:real^1->real^N`]
      MOI_S4U_CURVE_LOOPS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`path_image (g:real^1->real^N) SUBSET a`; `(a:real^N->bool) INTER c = {}`;
        `(a:real^N->bool) SUBSET th`] THEN
      SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `g':real^1->real^N` STRIP_ASSUME_TAC)] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_FH1_LOOP_CLASS_HOMOTOPIC) THEN
    MATCH_MP_TAC MOI_S4U_LOOP_CLASS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Mayer-Vietoris: H_1(a INTER b) maps onto H_1(a) *)
  SUBGOAL_THEN `carries_h1 ((a:real^N->bool) INTER b) a` ASSUME_TAC THENL
   [REWRITE_TAC[carries_h1] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; group_image; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[homology_group; HOM_INDUCED];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; group_image; IN_IMAGE] THEN
    X_GEN_TAC `z:((num->real)->real^N)frag->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (th:real^N->bool)`; `a:real^N->bool`;
                   `b:real^N->bool`; `z:((num->real)->real^N)frag->bool`]
      MOI_S4U_MV_LIFT) THEN
    SUBGOAL_THEN
     `subtopology (subtopology euclidean (th:real^N->bool)) a = subtopology euclidean a /\
      subtopology (subtopology euclidean th) b = subtopology euclidean b /\
      subtopology (subtopology euclidean th) (a INTER b) = subtopology euclidean (a INTER b)`
    (fun thm -> REWRITE_TAC[thm]) THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_S4J_SUBTOP THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `a:real^N->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `b:real^N->bool`)) (concl th) &&
        can (find_term ((=) `a:real^N->bool`)) (concl th) &&
        not (can (find_term ((=) `s:real^N->bool`)) (concl th)) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "group_image")) (concl th))) THEN
      REWRITE_TAC[group_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN(X_CHOOSE_THEN `c':((num->real)->real^N)frag->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `c':((num->real)->real^N)frag->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* compose with H_1(a) -> H_1(s) *)
  UNDISCH_TAC `carries_h1 ((a:real^N->bool) INTER b) a` THEN
  UNDISCH_TAC `carries_h1 (a:real^N->bool) s` THEN REWRITE_TAC[carries_h1] THEN
  MP_TAC(ISPECL [`(a:real^N->bool) INTER b`; `a:real^N->bool`; `s:real^N->bool`]
    MOI_S4U_IMAGE_COMPOSE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `th:real^N->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[group_image]);;

(* ------------------------------------------------------------------------- *)
(* Bridges to the PL setting: the PL torus model is a torus surface,        *)
(* PL 1-spheres are circles, and (PL_SOLID_TORUS_BASIC, pc_moi_fnd_plst)    *)
(* the frontier of a PL solid torus in real^3 is a polyhedral torus surface *)
(* inside it, and its H_1 is nontrivial.                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S4U_TORUS_MODEL = prove
 (`torus_surface pl_torus_model /\ pl_polyhedron pl_torus_model`,
  CONJ_TAC THENL
   [REWRITE_TAC[torus_surface; pl_torus_model] THEN
    MATCH_MP_TAC HOMEOMORPHIC_PCROSS THEN
    SUBGOAL_THEN `vec 1:real^2 = vector[&1;&1]` SUBST1_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT]; ALL_TAC] THEN
    MP_TAC(SPEC `&1` MOI_FH1_SQUARE_FRONTIER_CIRCLE) THEN REWRITE_TAC[REAL_LT_01] THEN
    SIMP_TAC[];
    REWRITE_TAC[pl_torus_model; GSYM moi_fps_sq] THEN
    MATCH_MP_TAC MOI_FPS_PL_POLYHEDRON_PCROSS THEN
    REWRITE_TAC[MOI_FPS_SQ_PL_POLYHEDRON]]);;

let MOI_S4U_PL_SPHERE1_CIRCLE = prove
 (`!j:real^N->bool. pl_sphere 1 j ==> j homeomorphic sphere(vec 0:real^2,&1)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN EXISTS_TAC `relative_frontier k:real^N->bool` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^2,&1) = relative_frontier(cball(vec 0,&1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[RELATIVE_FRONTIER_CBALL] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
  REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL; DIMINDEX_2; REAL_LT_01] THEN
  UNDISCH_TAC `&(1 + 1) simplex (k:real^N->bool)` THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLEX_IMP_CONVEX THEN EXISTS_TAC `&2:int` THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC SIMPLEX_IMP_COMPACT THEN
    EXISTS_TAC `&2:int` THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC AFF_DIM_SIMPLEX THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S4U_PL_SOLID_TORUS_FACTS = prove
 (`!s:real^3->bool.
     pl_solid_torus s
     ==> compact s /\ torus_surface (frontier s) /\ frontier s SUBSET s /\
         pl_polyhedron (frontier s) /\
         ~trivial_group(homology_group(&1,subtopology euclidean s))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `compact (s:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_solid_torus (s:real^3->bool)` THEN
    REWRITE_TAC[pl_solid_torus; pl_homeomorphism; homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^(2,1)finite_sum->real^3` (X_CHOOSE_THEN
      `g:real^3->real^(2,1)finite_sum` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq (concl th) && rhs (concl th) = `s:real^3->bool`)) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_INTERVAL; OPEN_INTERVAL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(CONJUNCT2 PL_SOLID_TORUS_BASIC) THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(2,2)finite_sum->real^3` (X_CHOOSE_THEN
    `g:real^3->real^(2,2)finite_sum` ASSUME_TAC)) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[torus_surface] THEN
    MATCH_MP_TAC(INST_TYPE [`:(2,2)finite_sum`,`:N`] HOMEOMORPHIC_TRANS) THEN
    EXISTS_TAC `pl_torus_model` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`f:real^(2,2)finite_sum->real^3`;
                            `g:real^3->real^(2,2)finite_sum`] THEN
      UNDISCH_TAC `pl_homeomorphism (pl_torus_model,frontier s)
                     (f:real^(2,2)finite_sum->real^3,g)` THEN
      SIMP_TAC[pl_homeomorphism];
      REWRITE_TAC[GSYM torus_surface; MOI_S4U_TORUS_MODEL]];
    MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `pl_homeomorphism (pl_torus_model,frontier s)
                   (f:real^(2,2)finite_sum->real^3,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq (concl th) && rhs (concl th) = `frontier (s:real^3->bool)`)) THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[MOI_S4U_TORUS_MODEL];
    MP_TAC(ISPEC `s:real^3->bool` (CONJUNCT1 PL_SOLID_TORUS_BASIC)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:real^3->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP SPINE_HOMOLOGY_ISOMORPHISM) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP ISOMORPHIC_GROUP_TRIVIALITY) THEN
    REWRITE_TAC[NON_TRIVIAL_INTEGER_GROUP]]);;

